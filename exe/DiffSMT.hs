module Main where

import Data.Map(Map)
import qualified Data.Map.Strict as Map
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import Data.List(mapAccumL, foldl')
import Data.Char(isSpace)
import SimpleSMT(SExpr(..), readSExpr)

main :: IO ()
main = interact $ \txt ->
  case readSExpr txt of
    Just (sexp,rest) | all isSpace rest ->
      case fromSExp emptyCtx sexp of
        (ctx, t0@Term { termF = App "=" [x,y] }) ->
          let (_, d) = diff ctx x y in
          toJS (toBinds mempty d) d
        _ -> error "S-expression is not an equality"
    _ -> error "malformed S-expression"


data TermCtx = TermCtx {
  terms :: !(Map TermF Term),
  nextTerm :: !Int
}

emptyCtx :: TermCtx
emptyCtx = TermCtx { terms = mempty, nextTerm = 0 }

data Term = Term {
  termId :: !Int,
  termF  :: TermF
} deriving Show

instance Eq Term where
  x == y = termId x == termId y

instance Ord Term where
  compare x y = compare (termId x) (termId y)

data TermF =
    Con String
  | App String [Term]
  | Tup [Term]
  | Diff Term Term
    deriving (Eq,Ord,Show)

fromSExp :: TermCtx -> SExpr -> (TermCtx, Term)
fromSExp ctx0 sexp =
  case sexp of
    Atom a -> fromShp ctx0 (Con a)
    List (Atom a : more) ->
      let (ctx, ts) = mapAccumL fromSExp ctx0 more
      in fromShp ctx (App a ts) 
    List es ->
      let (ctx, ts) = mapAccumL fromSExp ctx0 es
      in fromShp ctx (Tup ts)

fromShp :: TermCtx -> TermF -> (TermCtx, Term)
fromShp ctx shp =
  case Map.lookup shp (terms ctx) of
    Just t -> (ctx, t)
    Nothing ->
      let i     = nextTerm ctx
          t     = Term { termId = i, termF = shp }
          ts    = Map.insert shp t (terms ctx)
          ctx1  = TermCtx { nextTerm = i + 1, terms = ts }
      in ctx1 `seq` (ctx1, t)

diffMany :: TermCtx -> [Term] -> [Term] -> Maybe (TermCtx, [Term])
diffMany ctx xs ys
  | length xs == length ys =
    Just (mapAccumL (\c (x,y) -> diff c x y) ctx (zip xs ys))
  | otherwise = Nothing

diff :: TermCtx -> Term -> Term -> (TermCtx, Term)
diff ctx x y
  | x == y = (ctx, x)
diff ctx Term { termF = App f xs } Term { termF = App g ys }
  | f == g, Just (ctx1, ts) <- diffMany ctx xs ys = fromShp ctx1 (App f ts)
diff ctx Term { termF = Tup xs } Term { termF = Tup ys }
  | Just (ctx1, ts) <- diffMany ctx xs ys = fromShp ctx1 (Tup ts)
-- We ignore Diff for the moment, as the plan is to use ths on fromSExp,
-- which shouldn't have any of these.  We could handle `Diff` as if it
-- is an "or" and try to diff each option separately.
diff ctx x y = fromShp ctx (Diff x y)


data Bind = Bind {
  def :: Term,
  count :: !Int,
  hasDiff :: Bool
}

type Binds = IntMap Bind

toBindsMany :: Binds -> [Term] -> (Binds, Bool)
toBindsMany bs as =
  case mapAccumL toBinds' bs as of
    (bs1, ds) -> (bs1, or ds)

toBinds :: Binds -> Term -> Binds
toBinds bs = fst . toBinds' bs

toBinds' :: Binds -> Term -> (Binds, Bool)
toBinds' bs t =
  case IntMap.lookup (termId t) bs of
    Just b -> (IntMap.insert (termId t) b { count = count b + 1 } bs, hasDiff b)
    Nothing ->
      let bs1 = IntMap.insert (termId t) Bind { def = t, count = 1, hasDiff = snd res } bs
          res = 
            case termF t of
              Con _      -> (bs1, False)
              App _ as   -> toBindsMany bs1 as
              Tup as     -> toBindsMany bs1 as
              Diff x y   -> (toBinds (toBinds bs1 x) y, True)
      in res
      

type JS = String

toJS :: Binds -> Term -> JS
toJS bs t = unlines $ [
  "{ \"root\": " ++ tid t ++ ",",
  "  \"terms\": {"
  ] ++
  [ l | b <- IntMap.elems bs, l <- bind b ] ++ 
  [
  "  }"
  ]
  where
  tid x = "t" ++ show (termId x)
  bind b =
    let t = def b
    in [
         "  " ++ tid t ++ ": {",
         "    \"diff\": " ++ (if hasDiff b then "true" else "false") ++ ",",
         "    \"count\": " ++ show (count b),
         "    \"shape\": " ++ toShape t
       ]
  toShape t =
    case termF t of
      Con a     -> shape "con" a []
      App f as  -> shape "app" f as
      Tup as    -> shape "tup" "" as
      Diff a b  -> shape "diff" "" [a,b]

  shape t f xs = "{ \"tag\": " ++ show t ++ concat [ ", \"fun\": " ++ show f | not (null f) ] ++
                 ", \"args\": " ++ show (map tid xs) ++ "}"  
