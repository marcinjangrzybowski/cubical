{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Agda.Builtin.Char
open import Agda.Builtin.String

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List as L
open import Cubical.Data.Maybe as Mb

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.Reflection


-- toℕTerm : ℕ → R.Term
-- toℕTerm zero = R.con (quote zero) []
-- toℕTerm (suc x) = R.con (quote suc) v[ toℕTerm x ]


-- _≟ℕ_ : ℕ → ℕ → Bool
-- x ≟ℕ x₁ = Dec→Bool (discreteℕ x x₁)

-- _≟qn_ = R.primQNameEquality

-- quotedMaybe→maybeTerm : R.Term → R.TC (Maybe (R.Term))
-- quotedMaybe→maybeTerm (R.con (quote nothing) _) = R.returnTC nothing
-- quotedMaybe→maybeTerm (R.con (quote just) (_ ∷ _ ∷ varg x ∷ [])) = R.returnTC (just x)
-- quotedMaybe→maybeTerm t =   R.typeError
--  (R.termErr t ∷ [(R.strErr "Not a Maybe!")])


-- quotedList→ListOfTerms : R.Term → R.TC (List (R.Term))
-- quotedList→ListOfTerms (R.con (quote []) _) = R.returnTC []
-- quotedList→ListOfTerms (R.con (quote _∷_) (_ ∷ _ ∷ varg x ∷ varg xs ∷ [])) =
--  quotedList→ListOfTerms xs >>= (λ xs → R.returnTC (x ∷ xs))
-- quotedList→ListOfTerms t = R.typeError
--  (R.termErr t ∷ [(R.strErr "Not a List!")])

-- blockIfContainsMeta : R.Term → R.TC Unit

-- blockIfContainsMeta' : List (R.Arg R.Term) → R.TC Unit
-- blockIfContainsMeta' [] = R.returnTC _
-- blockIfContainsMeta' (R.arg i x ∷ x₁) =
--  blockIfContainsMeta x >> blockIfContainsMeta' x₁


-- blockIfContainsMeta (R.var _ args) = blockIfContainsMeta' args
-- blockIfContainsMeta (R.con _ args) = blockIfContainsMeta' args
-- blockIfContainsMeta (R.def _ args) = blockIfContainsMeta' args
-- blockIfContainsMeta (R.lam _ (R.abs s x)) = blockIfContainsMeta x
-- blockIfContainsMeta (R.pat-lam _ _) = R.typeError [(R.strErr "TODO : blockIfContainsMeta")]
-- blockIfContainsMeta (R.pi _ _) = R.typeError [(R.strErr "TODO : blockIfContainsMeta")]
-- blockIfContainsMeta (R.agda-sort _) = R.typeError [(R.strErr "TODO : blockIfContainsMeta")]
-- blockIfContainsMeta (R.lit l) = R.returnTC _
-- blockIfContainsMeta (R.meta m _) = R.blockTC (R.blockerMeta m)
-- blockIfContainsMeta R.unknown = R.returnTC _

any? : List Bool → Bool
any? [] = false
any? (false ∷ x₁) = any? x₁
any? (true ∷ x₁) = true

-- containsMeta? : R.Term → Bool
-- containsMetaAny? : List (R.Arg R.Term) → Bool

-- containsMeta? (R.var x args) = containsMetaAny? args
-- containsMeta? (R.con c args) = containsMetaAny? args
-- containsMeta? (R.def f args) = containsMetaAny? args
-- containsMeta? (R.lam v₁ (R.abs _ t)) = containsMeta? t
-- containsMeta? (R.pat-lam cs args) = containsMetaAny? args
-- containsMeta? (R.pi (R.arg _ a) (R.abs _ b)) = containsMeta? a or containsMeta? b
-- containsMeta? (R.agda-sort s) = false
-- containsMeta? (R.lit l) = false
-- containsMeta? (R.meta x x₁) = true
-- containsMeta? R.unknown = true

-- containsMetaAny? [] = false
-- containsMetaAny? ((R.arg _ x) ∷ x₁) = containsMeta? x or containsMetaAny? x₁

-- catchOrSkip : ∀ {ℓ} {A : Type ℓ} → Bool → R.TC A → R.TC A → R.TC A
-- catchOrSkip true _ x = x
-- catchOrSkip false x y = R.catchTC x y

-- uniqeAtoms : List R.Term → R.TC (List R.Term)
-- uniqeAtoms [] = R.returnTC []
-- uniqeAtoms (x ∷ x₁) = do
--   notIn ← ensureNotIn x₁
--   xs' ← uniqeAtoms x₁
--   R.returnTC (if notIn then x ∷ xs' else xs')
--  where
--  ensureNotIn : List R.Term → R.TC Bool
--  ensureNotIn [] = R.returnTC true
--  ensureNotIn (x' ∷ xs) =
--    R.catchTC ( (R.unify x x' >> R.returnTC false))
--              (ensureNotIn xs)


-- lookT : List R.Term → R.Term → R.TC ℕ
-- lookT [] _ = R.typeError []
-- lookT (x ∷ x₂) x₁ =
--      R.catchTC ((R.unify x x₁ >> R.returnTC zero))
--          (lookT x₂ x₁ >>= R.returnTC ∘ suc)

-- quoteList : List R.Term → R.Term
-- quoteList [] = R.con (quote []) []
-- quoteList (x ∷ x₁) = R.con (quote _∷_)
--   (varg x ∷ varg (quoteList x₁) ∷ [])


-- matchVarg : List (R.Arg R.Term) → R.TC R.Term
-- matchVarg (harg _ ∷ xs) = matchVarg xs
-- matchVarg (varg t ∷ []) = R.returnTC t
-- matchVarg _ = R.typeError [ R.strErr "matchV fail" ]

-- matchFirstVarg : List (R.Arg R.Term) → R.TC R.Term
-- matchFirstVarg (harg _ ∷ xs) = matchFirstVarg xs
-- matchFirstVarg (varg t ∷ _) = R.returnTC t
-- matchFirstVarg _ = R.typeError [ R.strErr "matchV fail" ]



-- match2Vargs : List (R.Arg R.Term) → R.TC (R.Term × R.Term)
-- match2Vargs (harg _ ∷ xs) = match2Vargs xs
-- match2Vargs (varg t1 ∷ varg t2 ∷ []) = R.returnTC (t1 , t2)
-- match2Vargs _ = R.typeError []

-- match2Vargs' : List (R.Arg R.Term) → Maybe (R.Term × R.Term)
-- match2Vargs' (harg _ ∷ xs) = match2Vargs' xs
-- match2Vargs' (varg t1 ∷ varg t2 ∷ []) = just (t1 , t2)
-- match2Vargs' _ = nothing

-- matchFunctorAppArgs : List (R.Arg R.Term) → Maybe (R.Term × R.Term)
-- matchFunctorAppArgs (harg _ ∷ xs) = matchFunctorAppArgs xs
-- matchFunctorAppArgs (varg t1 ∷ harg _ ∷ harg _ ∷ varg t2 ∷ []) = just (t1 , t2)
-- matchFunctorAppArgs _ = nothing


-- match3Vargs : List (R.Arg R.Term) → R.TC (R.Term × R.Term × R.Term)
-- match3Vargs (harg _ ∷ xs) = match3Vargs xs
-- match3Vargs (varg t1 ∷ varg t2 ∷ varg t3 ∷  []) = R.returnTC (t1 , t2 , t3)
-- match3Vargs _ = R.typeError []



-- inferEnds : R.Term → R.TC (R.Type × (R.Term × R.Term))
-- inferEnds hole = do
--   ty ← R.inferType hole >>= wait-for-type
--   (eTy , (e0 , e1)) ← R.withNormalisation true $ pathTypeView ty
--   blockIfContainsMeta e0
--   blockIfContainsMeta e1

--   R.returnTC (eTy , (e0 , e1))
--  where
--  pathTypeView : R.Term → R.TC (R.Type × (R.Term × R.Term))
--  pathTypeView (R.def (quote _≡_) l@(_ ∷ (harg ty) ∷ _)) =
--    do e ← match2Vargs l
--       R.returnTC (ty , e)
--  pathTypeView t = R.typeError (R.strErr "Not a Path Type! : " ∷ [ R.termErr t ])




R∙ : R.Term → R.Term → R.Term
R∙ x y = R.def (quote _∙_) (x v∷ y v∷ [] )

R∙' : R.Term → R.Term → R.Term
R∙' x y = R.def (quote _∙'_) (x v∷ y v∷ [] )


-- R∙∙ : R.Term → R.Term → R.Term → R.Term
-- R∙∙ x y z = R.def (quote _∙∙_∙∙_) (x v∷ y v∷ z v∷ [] )

-- Rsym : R.Term → R.Term
-- Rsym x = R.def (quote sym) (x v∷ [] )


explicitRefl : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
explicitRefl x i = x

explicitReflSq : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y)  → p ≡ p
explicitReflSq p i = p


Rrefl : R.Term
Rrefl = R.def (quote refl) []

RexplicitRefl : R.Term → R.Term
RexplicitRefl x = R.def (quote explicitRefl) v[ x ]

RexplicitReflSq : R.Term → R.Term
RexplicitReflSq x = R.def (quote explicitReflSq) v[ x ]


-- foldR∙ : List R.Term → R.Term
-- foldR∙ [] = Rrefl
-- foldR∙ (x ∷ []) = x
-- foldR∙ (x ∷ x₁ ∷ xs) = R∙∙ x x₁ (foldR∙ xs)

-- tryAllTC : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} →
--               R.TC B → List A → (A → R.TC B) → R.TC B
-- tryAllTC fallback [] f = fallback
-- tryAllTC fallback (x ∷ xs) f =
--   f x <|> tryAllTC fallback xs f


-- foldPathTerms : List (Maybe R.Term) → Maybe R.Term
-- foldPathTerms [] = nothing
-- foldPathTerms (nothing ∷ xs) = foldPathTerms xs
-- foldPathTerms (just x ∷ xs) =
--   just $ Mb.rec x (λ xs' → R.def (quote _∙_)
--     (x v∷ xs' v∷ [])) (foldPathTerms xs)


-- foldPathTerms' : R.Term → List (Maybe R.Term) → Maybe R.Term
-- foldPathTerms' A [] = nothing
-- foldPathTerms' A (nothing ∷ xs) = foldPathTerms' A xs
-- foldPathTerms' A (just x ∷ xs) =
--   just $ Mb.rec x (λ xs' → R.def (quote _∙_)
--     (harg {q = R.quantity-ω} R.unknown
--      ∷ harg {q = R.quantity-ω} A ∷ x v∷ xs' v∷ [])) (foldPathTerms' A xs)

-- symPathTerms : List (Maybe R.Term) → List (Maybe R.Term)
-- symPathTerms = map (map-Maybe (R.def (quote sym) ∘ v[_])) ∘ rev


-- matchPiDom : R.Term → R.TC R.Term
-- matchPiDom (R.pi (varg d) _) = pure d
-- matchPiDom t = R.typeError ("matchPiDom fail" ∷ₑ [ t  ]ₑ )

-- unFst : R.Term → R.TC R.Term
-- unFst (R.def (quote fst) t) = matchVarg t
-- unFst t  = R.typeError ("unFst fail" ∷ₑ [ t ]ₑ )





-- renderTerm : R.Term → R.TC String
-- renderTerm = R.formatErrorParts ∘ [_]ₑ


-- renderArg : R.Arg R.Term → R.TC String
-- renderArg (R.arg i x) = renderTerm x



-- dropHArgPrefix : List (R.Arg R.Term) → List R.Term 
-- dropHArgPrefix [] = []
-- dropHArgPrefix xs@(_ v∷ _) = L.map (λ {(R.arg _ x) → x}) xs 
-- dropHArgPrefix (_ ∷ xs) = dropHArgPrefix xs

-- tailIOfContrsFromFirstVarg : R.Term → List R.Term
-- tailIOfContrsFromFirstVarg (R.con _ tl) = dropHArgPrefix tl
-- tailIOfContrsFromFirstVarg _ = []

mapArg : ∀ {ℓ ℓ'} → {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) → R.Arg A → R.Arg B
mapArg f (R.arg i x) = R.arg i (f x)

-- mapArgM : ∀ {ℓ ℓ'} → {A : Type ℓ} {B : Type ℓ'}
--   → (f : A → R.TC B) → R.Arg A → R.TC (R.Arg B)
-- mapArgM f (R.arg i x) = ⦇ R.arg ⦇ i ⦈ (f x) ⦈

unArg : ∀ {ℓ} → {A : Type ℓ} → R.Arg A → A
unArg (R.arg i x) = x

argInfo : ∀ {ℓ} → {A : Type ℓ} → R.Arg A → R.ArgInfo
argInfo (R.arg i x) = i
