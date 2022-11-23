{-# LANGUAGE QuasiQuotes #-}
module Sources (Source(..), sources) where

import           Text.RawString.QQ

data Source = Source { name :: String, content :: String, parsed :: [String] }

-- | A list of examples SMT-Lib2 files. Most of them were taken from the official
-- SMT-Lib website:
-- https://smtlib.cs.uiowa.edu/examples.shtml
sources =
  [ Source "assertions" assertions assertionsParsed
  , Source "assignments" assignments assignmentsParsed
  , Source "boolean" boolean booleanParsed
  , Source "info" info infoParsed
  , Source "integer arithmetic" integerArithmetic integerArithmeticParsed
  , Source
      "modeling sequential code (SSA)"
      modelingSequentialCodeSSA
      modelingSequentialCodeSSAParsed
  , Source
      "modeling sequential code (bitvectors)"
      modelingSequentialCodeBitvectors
      modelingSequentialCodeBitvectorsParsed
  , Source "scopes" scopes scopesParsed
  , Source "sorts" sorts sortsParsed
  , Source "unsat cores" unsatCores unsatCoresParsed
  , Source "values or models" valuesOrModels valuesOrModelsParsed
  , Source "Z3 error message" z3error z3errorParsed
  ]

assertions = [r|
; Getting assertions
(set-option :produce-assertions true)
(set-logic QF_UF)
(declare-const p Bool) (declare-const q Bool)
(push 1)
(assert (or p q))
(push 1)
(assert (not q))
(get-assertions)
; ((or p q)
;  (not q)
; )
(pop 1)
(get-assertions)
; ((or p q))
(pop 1)
(get-assertions)
; ()
(exit)|]

assertionsParsed =
  [ "(set-option :produce-assertions true)"
  , "(set-logic QF_UF)"
  , "(declare-const p Bool)"
  , "(declare-const q Bool)"
  , "(push 1)"
  , "(assert (or p q))"
  , "(push 1)"
  , "(assert (not q))"
  , "(get-assertions)"
  , "(pop 1)"
  , "(get-assertions)"
  , "(pop 1)"
  , "(get-assertions)"
  , "(exit)"
  ]

assignments = [r|
; Getting assignments
(set-option :produce-assignments true)
(set-logic QF_UF)
(declare-const p Bool) (declare-const q Bool) (declare-const r Bool)
(assert (not (=(! (and (! p :named P) q) :named PQ) (! r :named R))))
(check-sat)
; sat
(get-assignment)
; ((P true) (R false) (PQ true))
(exit)|]
assignmentsParsed =
  [ "(set-option :produce-assignments true)"
  , "(set-logic QF_UF)"
  , "(declare-const p Bool)"
  , "(declare-const q Bool)"
  , "(declare-const r Bool)"
  , "(assert (not (=(! (and (! p :named P) q) :named PQ) (! r :named R))))"
  , "(check-sat)"
  , "(get-assignment)"
  , "(exit)"
  ]

boolean = [r|
; Basic Boolean example
(set-option :print-success false)
(set-logic QF_UF)
(declare-const p Bool)
(assert (and p (not p))) 
(check-sat) ; returns 'unsat'
(exit)|]
booleanParsed =
  [ "(set-option :print-success false)"
  , "(set-logic QF_UF)"
  , "(declare-const p Bool)"
  , "(assert (and p (not p)))"
  , "(check-sat)"
  , "(exit)"
  ]

info = [r|
; Getting info
(get-info :name)
; (: name "CVC4")
(get-info :version )
; (:version "4.0" )
(get-info :authors )
; (:authors "The CVC4 Team" )
(exit)|]
infoParsed =
  ["(get-info :name)", "(get-info :version)", "(get-info :authors)", "(exit)"]

integerArithmetic = [r|
; Integer arithmetic
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (- x y) (+ x (- y) 1)))
(check-sat)
; unsat
(exit)|]
integerArithmeticParsed =
  [ "(set-logic QF_LIA)"
  , "(declare-const x Int)"
  , "(declare-const y Int)"
  , "(assert (= (- x y) (+ x (- y) 1)))"
  , "(check-sat)"
  , "(exit)" ]

modelingSequentialCodeSSA = [r|
; Modeling sequential code in SSA form
;; Buggy swap
; int x, y;
; int t = x;
; x = y;
; y = x;

(set-logic QF_UFLIA)
(set-option :produce-models true)
(declare-fun x (Int) Int)  (declare-fun y (Int) Int)
(declare-fun t (Int) Int)
(assert (= (t 0) (x 0)))
(assert (= (y 1) (t 0)))
(assert (= (x 1) (y 1)))

(assert
    (not
        (and (= (x 1) (y 0)) (= (y 1) (x 0)))))
(check-sat)
(get-value ((x 0) (y 0) (x 1) (y 1)))
; possible returned valuation:
; (((x 0) (- 1)) ((y 0) 2) ((x 1) (- 1)) ((y 1) (- 1)))
(get-model)
; possible returned model:
; (
;  (define-fun x ((_ufmt_1 Int)) Int (- 1))
;  (define-fun y ((_ufmt_1 Int)) Int (ite (= _ufmt_1 1) (- 1) 2))
;  (define-fun t ((_ufmt_1 Int)) Int (- 1))
; )
(exit)|]
modelingSequentialCodeSSAParsed =
  [ "(set-logic QF_UFLIA)"
  , "(set-option :produce-models true)"
  , "(declare-fun x (Int) Int)"
  , "(declare-fun y (Int) Int)"
  , "(declare-fun t (Int) Int)"
  , "(assert (= (t 0) (x 0)))"
  , "(assert (= (y 1) (t 0)))"
  , "(assert (= (x 1) (y 1)))"
  , "(assert (not (and (= (x 1) (y 0)) (= (y 1) (x 0)))))"
  , "(check-sat)"
  , "(get-value ((x 0) (y 0) (x 1) (y 1)))"
  , "(get-model)"
  , "(exit)"
  ]

modelingSequentialCodeBitvectors = [r|
; Modeling sequential code in SSA form
;; Buggy swap
; int x, y;
; int t = x;
; x = y;
; y = x;

(set-logic QF_UFLIA)
(set-option :produce-models true)
(declare-fun x (Int) Int)  (declare-fun y (Int) Int)
(declare-fun t (Int) Int)
(assert (= (t 0) (x 0)))
(assert (= (y 1) (t 0)))
(assert (= (x 1) (y 1)))

(assert
    (not
        (and (= (x 1) (y 0)) (= (y 1) (x 0)))))
(check-sat)
(get-value ((x 0) (y 0) (x 1) (y 1)))
; possible returned valuation:
; (((x 0) (- 1)) ((y 0) 2) ((x 1) (- 1)) ((y 1) (- 1)))
(get-model)
; possible returned model:
; (
;  (define-fun x ((_ufmt_1 Int)) Int (- 1))
;  (define-fun y ((_ufmt_1 Int)) Int (ite (= _ufmt_1 1) (- 1) 2))
;  (define-fun t ((_ufmt_1 Int)) Int (- 1))
; )
(exit)|]
modelingSequentialCodeBitvectorsParsed =
  [ "(set-logic QF_UFLIA)"
  , "(set-option :produce-models true)"
  , "(declare-fun x (Int) Int)"
  , "(declare-fun y (Int) Int)"
  , "(declare-fun t (Int) Int)"
  , "(assert (= (t 0) (x 0)))"
  , "(assert (= (y 1) (t 0)))"
  , "(assert (= (x 1) (y 1)))"
  , "(assert (not (and (= (x 1) (y 0)) (= (y 1) (x 0)))))"
  , "(check-sat)"
  , "(get-value ((x 0) (y 0) (x 1) (y 1)))"
  , "(get-model)"
  , "(exit)"
  ]

scopes = [r|
; Using scopes to explore multiple problems
(set-option :print-success false)
(set-logic QF_LIA)
(declare-const x Int) (declare-const y Int)
(assert (= (+ x (* 2 y)) 20))
(push 1)
  (assert (= (- x y) 2))
  (check-sat)
  ; sat
(pop 1)
(push 1)
  (assert (= (- x y) 3))
  (check-sat)
  ; unsat
(pop 1)
(exit)|]
scopesParsed =
  [ "(set-option :print-success false)"
  , "(set-logic QF_LIA)"
  , "(declare-const x Int)"
  , "(declare-const y Int)"
  , "(assert (= (+ x (* 2 y)) 20))"
  , "(push 1)"
  , "(assert (= (- x y) 2))"
  , "(check-sat)"
  , "(pop 1)"
  , "(push 1)"
  , "(assert (= (- x y) 3))"
  , "(check-sat)"
  , "(pop 1)"
  , "(exit)"
  ]

sorts = [r|
; Defining and using new sorts
(set-option :print-success false)
(set-logic QF_UF)
(declare-sort A 0)
(declare-const a A) (declare-const b A) (declare-const c A)
(declare-const d A) (declare-const e A)
(assert (or (= c a)(= c b)))
(assert (or (= d a)(= d b)))
(assert (or (= e a)(= e b)))
(push 1)
  (assert (distinct c d))
  (check-sat)
  ; sat
(pop 1)
(push 1)
  (assert (distinct c d e))
  (check-sat)
  ; unsat
(pop 1)
(exit)|]
sortsParsed =
  [ "(set-option :print-success false)"
  , "(set-logic QF_UF)"
  , "(declare-sort A 0)"
  , "(declare-const a A)"
  , "(declare-const b A)"
  , "(declare-const c A)"
  , "(declare-const d A)"
  , "(declare-const e A)"
  , "(assert (or (= c a) (= c b)))"
  , "(assert (or (= d a) (= d b)))"
  , "(assert (or (= e a) (= e b)))"
  , "(push 1)"
  , "(assert (distinct c d))"
  , "(check-sat)"
  , "(pop 1)"
  , "(push 1)"
  , "(assert (distinct c d e))"
  , "(check-sat)"
  , "(pop 1)"
  , "(exit)"
  ]

unsatCores = [r|
; Getting unsatisfiable cores
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(declare-const p Bool) (declare-const q Bool) (declare-const r Bool)
(declare-const s Bool) (declare-const t Bool)
(assert (! (=> p q) :named PQ))
(assert (! (=> q r) :named QR))
(assert (! (=> r s) :named RS))
(assert (! (=> s t) :named ST))
(assert (! (not (=> q s)) :named NQS))
(check-sat)
; unsat
(get-unsat-core)
; (QR RS NQS)
(exit)|]
unsatCoresParsed =
  [ "(set-option :produce-unsat-cores true)"
  , "(set-logic QF_UF)"
  , "(declare-const p Bool)"
  , "(declare-const q Bool)"
  , "(declare-const r Bool)"
  , "(declare-const s Bool)"
  , "(declare-const t Bool)"
  , "(assert (! (=> p q) :named PQ))"
  , "(assert (! (=> q r) :named QR))"
  , "(assert (! (=> r s) :named RS))"
  , "(assert (! (=> s t) :named ST))"
  , "(assert (! (not (=> q s)) :named NQS))"
  , "(check-sat)"
  , "(get-unsat-core)"
  , "(exit)"
  ]

valuesOrModels = [r|
 ; Getting values or models
(set-option :print-success false)
(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x (* 2 y)) 20))
(assert (= (- x y) 2))
(check-sat)
; sat
(get-value (x y))
; ((x 8) (y 6))
(get-model)
; ((define-fun x () Int 8)
;  (define-fun y () Int 6)
; )
(exit)|]
valuesOrModelsParsed =
  [ "(set-option :print-success false)"
  , "(set-option :produce-models true)"
  , "(set-logic QF_LIA)"
  , "(declare-const x Int)"
  , "(declare-const y Int)"
  , "(assert (= (+ x (* 2 y)) 20))"
  , "(assert (= (- x y) 2))"
  , "(check-sat)"
  , "(get-value (x y))"
  , "(get-model)"
  , "(exit)"
  ]

z3error = "(error \"line 1 column 33: invalid command, '(' expected\")"
z3errorParsed = [ z3error ]
