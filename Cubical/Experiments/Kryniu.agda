{-# OPTIONS --safe #-}

module Cubical.Experiments.Kryniu where

-- open import Cubical.Foundations.Everything

-- open import Cubical.Data.Nat
-- open import Cubical.Data.Unit
-- open import Cubical.Data.Empty
-- open import Cubical.Data.Nat.Order
-- open import Cubical.Data.Bool
-- open import Cubical.Data.Sum
-- open import Cubical.Data.Sigma
-- open import Cubical.Data.Vec




-- data myBool : Type where
--  myTrue : myBool
--  myFalse : myBool




-- _=B_ : Bool → Bool → Type
-- false =B false = Unit
-- false =B true = ⊥
-- true =B false = ⊥
-- true =B true = Unit


-- notNot : (x : Bool) → x =B (not (not x))
-- notNot = {!!}


-- module ElmAST where

-- Basic data types

postulate
 Integer Float Char String : Type

data Literal : Type where
  LitInt    : Integer → Literal
  LitFloat  : Float   → Literal
  LitChar   : Char    → Literal
  LitString : String  → Literal
  LitBool   : Bool    → Literal

data BinOp : Type where
  Add  : BinOp
  Sub  : BinOp
  Mul  : BinOp
  Div  : BinOp
  Eq   : BinOp
  Neq  : BinOp
  Lt   : BinOp
  Gt   : BinOp
  Lte  : BinOp
  Gte  : BinOp
  And  : BinOp
  Or   : BinOp

data UnOp : Type where
  Neg : UnOp
  Not : UnOp

-- Expressions
data Expr : Type where
  EVar      : String      → Expr
  ELit      : Literal     → Expr
  EUnOp     : UnOp        → Expr → Expr
  EBinOp    : BinOp       → Expr → Expr → Expr
  EIf       : Expr        → Expr → Expr → Expr
  ELet      : Declaration → Expr → Expr
  EFunction : List String → Expr → Expr
  EApply    : Expr        → List Expr → Expr
  ECase     : Expr        → List (Pattern, Expr) → Expr

-- Patterns
data Pattern : Type where
  PVar  : String → Pattern
  PLit  : Literal → Pattern
  PAny  : Pattern
  PCons : Pattern → Pattern → Pattern

-- Declarations
data Declaration : Type where
  DValue : String → Expr → Declaration
  DType  : String → List String → Declaration

