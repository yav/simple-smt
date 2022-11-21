{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE ViewPatterns      #-}
-- | A module for interacting with an SMT solver, using SmtLib-2 format.
module SimpleSMT.SExpr
    -- ** S-Expressions
  ( SExpr(..)
  , showsSExpr
  , renderSExpr
  , serializeSingle
  , serializeBatch
  , ppSExpr
  , readSExpr
  , parseSExpr
  , Result(..)
  , Value(..)
  , sexprToVal
    -- * Convenience Functions for SmtLib-2 Expressions
  , fam
  , fun
  , const
  , app
    -- * Convenience Functions for SmtLib-2 identifiers
  , quoteSymbol
  , symbol
  , keyword
  , as
    -- ** Types
  , tInt
  , tBool
  , tReal
  , tArray
  , tBits
    -- ** Literals
  , int
  , real
  , bool
  , bvBin
  , bvHex
  , value
    -- ** Connectives
  , not
  , and
  , andMany
  , or
  , orMany
  , xor
  , implies
    -- ** If-then-else
  , ite
    -- ** Relational Predicates
  , eq
  , distinct
  , gt
  , lt
  , geq
  , leq
  , bvULt
  , bvULeq
  , bvSLt
  , bvSLeq
    -- ** Arithmetic
  , add
  , addMany
  , sub
  , neg
  , mul
  , abs
  , div
  , mod
  , divisible
  , realDiv
  , toInt
  , toReal
    -- ** Bit Vectors
  , concat
  , extract
  , bvNot
  , bvNeg
  , bvAnd
  , bvXOr
  , bvOr
  , bvAdd
  , bvSub
  , bvMul
  , bvUDiv
  , bvURem
  , bvSDiv
  , bvSRem
  , bvShl
  , bvLShr
  , bvAShr
  , signExtend
  , zeroExtend
    -- ** Arrays
  , select
  , store
  -- ** Other
  , named
  ) where

import Prelude hiding (not, and, or, abs, div, mod, concat, const)
import qualified Prelude as P
import Data.Char(isSpace, isDigit)
import Data.Bits(testBit)
import Data.ByteString.Builder (Builder, stringUtf8)
import Data.ByteString.Builder.Extra (defaultChunkSize, smallChunkSize, toLazyByteStringWith, untrimmedStrategy)
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.List (intersperse)
import Text.Read(readMaybe)
import Data.Ratio((%), numerator, denominator)
import Numeric(showHex, readHex, showFFloat)


-- | Results of checking for satisfiability.
data Result = Sat         -- ^ The assertions are satisfiable
            | Unsat       -- ^ The assertions are unsatisfiable
            | Unknown     -- ^ The result is inconclusive
              deriving (Eq,Show)

-- | Common values returned by SMT solvers.
data Value =  Bool  !Bool           -- ^ Boolean value
            | Int   !Integer        -- ^ Integral value
            | Real  !Rational       -- ^ Rational value
            | Bits  !Int !Integer   -- ^ Bit vector: width, value
            | Other !SExpr          -- ^ Some other value
              deriving (Eq,Show)

-- | S-expressions. These are the basic format for SmtLib-2.
data SExpr  = Atom String
            | List [SExpr]
              deriving (Eq, Ord, Show)

-- | Show an s-expression.
--
-- >>> let Just (e, _) = readSExpr "(assert (= ((_ map (- (Int Int) Int)) a1Cl a1Cm) a1Cv))"
-- >>> putStrLn $ showsSExpr e ""
-- (assert (= ((_ map (- (Int Int) Int)) a1Cl a1Cm) a1Cv))
showsSExpr :: SExpr -> ShowS
showsSExpr ex =
  case ex of
    Atom x  -> showString x
    List [] -> showString "()"
    List (e0 : es) -> showChar '(' . showsSExpr e0 .
                       foldr (\e m -> showChar ' ' . showsSExpr e . m)
                       (showChar ')') es

-- | Evaluate a bytestring builder to a lazy bytestring.
serializeWithChunkSizes :: Int -> Int -> Builder -> LBS.ByteString
serializeWithChunkSizes firstChunkSize newChunksSize =
  -- we're using the untrimmed strategy here as all backends consume the bytestring
  -- immediately
  -- TODO ideally the backend should be able to specify which strategy to use,
  -- depending on whether they consume the bytestring immediately
  toLazyByteStringWith (untrimmedStrategy firstChunkSize newChunksSize) ""

-- | Evaluate a bytestring builder corresponding to a single SMTLib2 command
-- (the size of the buffer is expected to be small). The output is a lazy bytestring.
serializeSingle :: Builder -> LBS.ByteString
serializeSingle =
  -- 256 is the first power of 2 that is bigger than the length of the longest
  -- command with interesting output in isUnity, and 2048 is just four times this
  -- because smallChunkSize * 4 = defaultChunkSize.
  serializeWithChunkSizes 256 2048

-- | Evaluate a bytestring builder corresponding to a batch of SMTLib2 commands
-- (the size of the buffer is expected to be important). The output is a lazy bytestring.
serializeBatch :: Builder -> LBS.ByteString
serializeBatch = serializeWithChunkSizes smallChunkSize defaultChunkSize

-- | Create a bytestring builder from an s-expression.
renderSExpr :: SExpr -> Builder
renderSExpr (Atom x) = stringUtf8 x
renderSExpr (List es) =
  "(" <> mconcat (intersperse " " [renderSExpr e | e <- es]) <> ")"

-- | Show an s-expression in a somewhat readable fashion.
--
-- >>> let Just (e, _) = readSExpr "(assert (= ((_ map (- (Int Int) Int)) a1Cl a1Cm) a1Cv))"
-- >>> putStrLn $ ppSExpr e ""
-- (assert
--    (=
--       (
--         (_
--            map
--            (-
--               (Int Int)
--               Int))
--         a1Cl
--         a1Cm)
--       a1Cv))
ppSExpr :: SExpr -> ShowS
ppSExpr = go 0
  where
  tab n = showString (replicate n ' ')
  many  = foldr (.) id

  new n e = showChar '\n' . tab n . go n e

  small :: Int -> [SExpr] -> Maybe [ShowS]
  small n es =
    case es of
      [] -> Just []
      e : more
        | n <= 0 -> Nothing
        | otherwise -> case e of
                         Atom x -> (showString x :) <$> small (n-1) more
                         _      -> Nothing

  go :: Int -> SExpr -> ShowS
  go n ex =
    case ex of
      Atom x        -> showString x
      List es
        | Just fs <- small 5 es ->
          showChar '(' . many (intersperse (showChar ' ') fs) . showChar ')'

      List (Atom x : es) -> showString "(" . showString x .
                                many (map (new (n+3)) es) . showString ")"

      List es -> showString "(" . many (map (new (n+2)) es) . showString ")"


-- | Parse an s-expression.
--
-- >>> readSExpr "(_ map (- (Int Int) Int)) a1Cl a1Cm)"
-- Just (List [Atom "_",Atom "map",List [Atom "-",List [Atom "Int",Atom "Int"],Atom "Int"]]," a1Cl a1Cm)")
readSExpr :: String -> Maybe (SExpr, String)
readSExpr (c : more) | isSpace c = readSExpr more
readSExpr (';' : more) = readSExpr $ drop 1 $ dropWhile (/= '\n') more
readSExpr ('|' : more) = do (sym, '|' : rest) <- pure (span ((/=) '|') more)
                            Just (Atom ('|' : sym ++ ['|']), rest)
readSExpr ('(' : more) = do (xs,more1) <- list more
                            return (List xs, more1)
  where
  list (c : txt) | isSpace c = list txt
  list (')' : txt) = return ([], txt)
  list txt         = do (v,txt1) <- readSExpr txt
                        (vs,txt2) <- list txt1
                        return (v:vs, txt2)
readSExpr txt     = case break end txt of
                       (as',bs) | P.not (null as') -> Just (Atom as', bs)
                       _ -> Nothing
  where end x = x == ')' || isSpace x

-- | Convert an s-expression to a value.
sexprToVal :: SExpr -> Value
sexprToVal expr =
  case expr of
    Atom "true"                    -> Bool True
    Atom "false"                   -> Bool False
    Atom ('#' : 'b' : ds)
      | Just n <- binLit ds         -> Bits (length ds) n
    Atom ('#' : 'x' : ds)
      | [(n,[])] <- readHex ds      -> Bits (4 * length ds) n
    Atom txt
      | Just n <- readMaybe txt     -> Int n
    List [ Atom "-", x ]
      | Int a <- sexprToVal x    -> Int (negate a)
    List [ Atom "/", x, y ]
      | Int a <- sexprToVal x
      , Int b <- sexprToVal y    -> Real (a % b)
    _ -> Other expr

  where
  binLit cs = do ds <- mapM binDigit cs
                 return $ sum $ zipWith (*) (reverse ds) powers2
  powers2   = 1 : map (2 *) powers2
  binDigit '0' = Just 0
  binDigit '1' = Just 1
  binDigit _   = Nothing


infixr 5 :<
pattern (:<) :: Char -> LBS.ByteString -> LBS.ByteString
pattern c :< rest <- (LBS.uncons -> Just (c, rest))

-- | Parse an s-expression.
-- Like readSExpr but for ByteStrings.
parseSExpr :: LBS.ByteString -> Maybe (SExpr, LBS.ByteString)
parseSExpr (c :< more) | isSpace c = parseSExpr more
parseSExpr (';' :< more) = parseSExpr $ LBS.drop 1 $ LBS.dropWhile (/= '\n') more
parseSExpr ('|' :< more) = do
  let (sym, '|' :< rest) = LBS.break (== '|') more
  Just (Atom $ LBS.unpack $ LBS.cons '|' $ LBS.snoc sym '|', rest)
parseSExpr ('(' :< more) = do
  (es, rest) <- list more
  return (List es, rest)
  where
    list :: LBS.ByteString -> Maybe ([SExpr], LBS.ByteString)
    list (c :< more') | isSpace c = list more'
    list (')' :< more') = return ([], more')
    list more' = do
      (e, rest) <- parseSExpr more'
      (es, rest') <- list rest
      return (e : es, rest')
parseSExpr txt =
  case LBS.break end txt of
    (atom, rest)
      | P.not (LBS.null atom) -> Just (Atom $ LBS.unpack atom, rest)
    _ -> Nothing
  where
    end x = x == ')' || isSpace x

-- | A constant, corresponding to a family indexed by some integers.
fam :: String -> [Integer] -> SExpr
fam f is = List (Atom "_" : Atom f : map (Atom . show) is)

-- | An SMT function.
fun :: String -> [SExpr] -> SExpr
fun f [] = Atom f
fun f as' = List (Atom f : as')

-- | An SMT constant.  A special case of 'fun'.
const :: String -> SExpr
const f = fun f []

app :: SExpr -> [SExpr] -> SExpr
app f xs = List (f : xs)

-- Identifiers -----------------------------------------------------------------------

-- | Symbols are either simple or quoted (c.f. SMTLIB v2.6 S3.1).
-- This predicate indicates whether a character is allowed in a simple
-- symbol.  Note that only ASCII letters are allowed.
allowedSimpleChar :: Char -> Bool
allowedSimpleChar c =
  isDigit c || c `elem` (['a' .. 'z'] ++ ['A' .. 'Z'] ++ "~!@$%^&*_-+=<>.?/")

isSimpleSymbol :: String -> Bool
isSimpleSymbol s@(c : _) = P.not (isDigit c) && all allowedSimpleChar s
isSimpleSymbol _         = False

quoteSymbol :: String -> String
quoteSymbol s
  | isSimpleSymbol s = s
  | otherwise        = '|' : s ++ "|"

symbol :: String -> SExpr
symbol = Atom . quoteSymbol

keyword :: String -> SExpr
keyword s = Atom (':' : s)

-- | Generate a type annotation for a symbol
as :: SExpr -> SExpr -> SExpr
as s t = fun "as" [s, t]

-- Types -----------------------------------------------------------------------


-- | The type of integers.
tInt :: SExpr
tInt = const "Int"

-- | The type of booleans.
tBool :: SExpr
tBool = const "Bool"

-- | The type of reals.
tReal :: SExpr
tReal = const "Real"

-- | The type of arrays.
tArray :: SExpr {- ^ Type of indexes  -} ->
          SExpr {- ^ Type of elements -} ->
          SExpr
tArray x y = fun "Array" [x,y]

-- | The type of bit vectors.
tBits :: Integer {- ^ Number of bits -} ->
         SExpr
tBits w = fam "BitVec" [w]



-- Literals --------------------------------------------------------------------

-- | Boolean literals.
bool :: Bool -> SExpr
bool b = const (if b then "true" else "false")

-- | Integer literals.
int :: Integer -> SExpr
int x | x < 0     = neg (int (negate x))
      | otherwise = Atom (show x)

-- | Real (well, rational) literals.
real :: Rational -> SExpr
real x
  | toRational y == x = Atom (showFFloat Nothing y "")
  | otherwise = realDiv (int (numerator x)) (int (denominator x))
  where y = fromRational x :: Double

-- | A bit vector represented in binary.
--
--     * If the value does not fit in the bits, then the bits will be increased.
--     * The width should be strictly positive.
bvBin :: Int {- ^ Width, in bits -} -> Integer {- ^ Value -} -> SExpr
bvBin w v = const ("#b" ++ bits)
  where
  bits = reverse [ if testBit v n then '1' else '0' | n <- [ 0 .. w - 1 ] ]

-- | A bit vector represented in hex.
--
--    * If the value does not fit in the bits, the bits will be increased to
--      the next multiple of 4 that will fit the value.
--    * If the width is not a multiple of 4, it will be rounded
--      up so that it is.
--    * The width should be strictly positive.
bvHex :: Int {- ^ Width, in bits -} -> Integer {- ^ Value -} -> SExpr
bvHex w v
  | v >= 0    = const ("#x" ++ padding ++ hex)
  | otherwise = bvHex w (2^w + v)
  where
  hex     = showHex v ""
  padding = replicate (P.div (w + 3) 4 - length hex) '0'


-- | Render a value as an expression.  Bit-vectors are rendered in hex,
-- if their width is a multiple of 4, and in binary otherwise.
value :: Value -> SExpr
value val =
  case val of
    Bool b    -> bool b
    Int n     -> int n
    Real r    -> real r
    Bits w v | P.mod w 4 == 0 -> bvHex w v
             | otherwise      -> bvBin w v
    Other o   -> o

-- Connectives -----------------------------------------------------------------

-- | Logical negation.
not :: SExpr -> SExpr
not p = fun "not" [p]

-- | Conjunction.
and :: SExpr -> SExpr -> SExpr
and p q = fun "and" [p,q]

andMany :: [SExpr] -> SExpr
andMany xs = if null xs then bool True else fun "and" xs

-- | Disjunction.
or :: SExpr -> SExpr -> SExpr
or p q = fun "or" [p,q]

orMany :: [SExpr] -> SExpr
orMany xs = if null xs then bool False else fun "or" xs

-- | Exclusive-or.
xor :: SExpr -> SExpr -> SExpr
xor p q = fun "xor" [p,q]

-- | Implication.
implies :: SExpr -> SExpr -> SExpr
implies p q = fun "=>" [p,q]


-- If-then-else ----------------------------------------------------------------

-- | If-then-else.  This is polymorphic and can be used to construct any term.
ite :: SExpr -> SExpr -> SExpr -> SExpr
ite x y z = fun "ite" [x,y,z]




-- Relations -------------------------------------------------------------------

-- | Equality.
eq :: SExpr -> SExpr -> SExpr
eq x y = fun "=" [x,y]

distinct :: [SExpr] -> SExpr
distinct xs = if null xs then bool True else fun "distinct" xs

-- | Greater-then
gt :: SExpr -> SExpr -> SExpr
gt x y = fun ">" [x,y]

-- | Less-then.
lt :: SExpr -> SExpr -> SExpr
lt x y = fun "<" [x,y]

-- | Greater-than-or-equal-to.
geq :: SExpr -> SExpr -> SExpr
geq x y = fun ">=" [x,y]

-- | Less-than-or-equal-to.
leq :: SExpr -> SExpr -> SExpr
leq x y = fun "<=" [x,y]

-- | Unsigned less-than on bit-vectors.
bvULt :: SExpr -> SExpr -> SExpr
bvULt x y = fun "bvult" [x,y]

-- | Unsigned less-than-or-equal on bit-vectors.
bvULeq :: SExpr -> SExpr -> SExpr
bvULeq x y = fun "bvule" [x,y]

-- | Signed less-than on bit-vectors.
bvSLt :: SExpr -> SExpr -> SExpr
bvSLt x y = fun "bvslt" [x,y]

-- | Signed less-than-or-equal on bit-vectors.
bvSLeq :: SExpr -> SExpr -> SExpr
bvSLeq x y = fun "bvsle" [x,y]




-- | Addition.
-- See also 'bvAdd'
add :: SExpr -> SExpr -> SExpr
add x y = fun "+" [x,y]

addMany :: [SExpr] -> SExpr
addMany xs = if null xs then int 0 else fun "+" xs

-- | Subtraction.
sub :: SExpr -> SExpr -> SExpr
sub x y = fun "-" [x,y]

-- | Arithmetic negation for integers and reals.
-- See also 'bvNeg'.
neg :: SExpr -> SExpr
neg x = fun "-" [x]

-- | Multiplication.
mul :: SExpr -> SExpr -> SExpr
mul x y = fun "*" [x,y]

-- | Absolute value.
abs :: SExpr -> SExpr
abs x = fun "abs" [x]

-- | Integer division.
div :: SExpr -> SExpr -> SExpr
div x y = fun "div" [x,y]

-- | Modulus.
mod :: SExpr -> SExpr -> SExpr
mod x y = fun "mod" [x,y]

-- | Is the number divisible by the given constant.
divisible :: SExpr -> Integer -> SExpr
divisible x n = List [ fam "divisible" [n], x ]

-- | Division of real numbers.
realDiv :: SExpr -> SExpr -> SExpr
realDiv x y = fun "/" [x,y]

-- | Bit vector concatenation.
concat :: SExpr -> SExpr -> SExpr
concat x y = fun "concat" [x,y]

-- | Extend to the signed equivalent bitvector by @i@ bits
signExtend :: Integer -> SExpr -> SExpr
signExtend i x = List [ fam "sign_extend" [i], x ]

-- | Extend with zeros to the unsigned equivalent bitvector
-- by @i@ bits
zeroExtend :: Integer -> SExpr -> SExpr
zeroExtend i x = List [ fam "zero_extend" [i], x ]

-- | Satisfies @toInt x <= x@ (i.e., this is like Haskell's 'floor')
toInt :: SExpr -> SExpr
toInt e = fun "to_int" [e]

-- | Promote an integer to a real
toReal :: SExpr -> SExpr
toReal e = fun "to_real" [e]

-- | Extract a sub-sequence of a bit vector.
extract :: SExpr -> Integer -> Integer -> SExpr
extract x y z = List [ fam "extract" [y,z], x ]

-- | Bitwise negation.
bvNot :: SExpr -> SExpr
bvNot x = fun "bvnot" [x]

-- | Bitwise conjuction.
bvAnd :: SExpr -> SExpr -> SExpr
bvAnd x y = fun "bvand" [x,y]

-- | Bitwise disjunction.
bvOr :: SExpr -> SExpr -> SExpr
bvOr x y = fun "bvor" [x,y]

-- | Bitwise exclusive or.
bvXOr :: SExpr -> SExpr -> SExpr
bvXOr x y = fun "bvxor" [x,y]

-- | Bit vector arithmetic negation.
bvNeg :: SExpr -> SExpr
bvNeg x = fun "bvneg" [x]

-- | Addition of bit vectors.
bvAdd :: SExpr -> SExpr -> SExpr
bvAdd x y = fun "bvadd" [x,y]

-- | Subtraction of bit vectors.
bvSub :: SExpr -> SExpr -> SExpr
bvSub x y = fun "bvsub" [x,y]



-- | Multiplication of bit vectors.
bvMul :: SExpr -> SExpr -> SExpr
bvMul x y = fun "bvmul" [x,y]

-- | Bit vector unsigned division.
bvUDiv :: SExpr -> SExpr -> SExpr
bvUDiv x y = fun "bvudiv" [x,y]

-- | Bit vector unsigned reminder.
bvURem :: SExpr -> SExpr -> SExpr
bvURem x y = fun "bvurem" [x,y]

-- | Bit vector signed division.
bvSDiv :: SExpr -> SExpr -> SExpr
bvSDiv x y = fun "bvsdiv" [x,y]

-- | Bit vector signed reminder.
bvSRem :: SExpr -> SExpr -> SExpr
bvSRem x y = fun "bvsrem" [x,y]




-- | Shift left.
bvShl :: SExpr {- ^ value -} -> SExpr {- ^ shift amount -} -> SExpr
bvShl x y = fun "bvshl" [x,y]

-- | Logical shift right.
bvLShr :: SExpr {- ^ value -} -> SExpr {- ^ shift amount -} -> SExpr
bvLShr x y = fun "bvlshr" [x,y]

-- | Arithemti shift right (copies most significant bit).
bvAShr :: SExpr {- ^ value -} -> SExpr {- ^ shift amount -} -> SExpr
bvAShr x y = fun "bvashr" [x,y]


-- | Get an elemeent of an array.
select :: SExpr {- ^ array -} -> SExpr {- ^ index -} -> SExpr
select x y = fun "select" [x,y]

-- | Update an array
store :: SExpr {- ^ array -}     ->
         SExpr {- ^ index -}     ->
         SExpr {- ^ new value -} ->
         SExpr
store x y z = fun "store" [x,y,z]


--------------------------------------------------------------------------------
-- Attributes

named :: String -> SExpr -> SExpr
named x e = fun "!" [e, Atom ":named", Atom x ]
