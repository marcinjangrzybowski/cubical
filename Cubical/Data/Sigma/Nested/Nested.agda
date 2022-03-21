{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.Nested where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Sigma


open import Cubical.Foundations.Everything

open import Cubical.Data.Sigma.Nested.Base


-- crude (temporary) name "Par" for this datatype
-- comes from Parenthesis
--
-- it is clearly binary tree, but without any data atached to nodes, or leafs
--
-- maybe this should be datatype on its own ?
-- what would be the good name for it?
--
-- I have version of this where Par is indexed by its "length",
-- but this verision was shorter
--
-- this datatype is used to describe different ways to apply multiple Σ
-- to create NestedΣ type
--

data Par : Type₀ where
  □ : Par
  [-_-_-] : Par → Par → Par
  assocPar : ∀ x y z → [- [- x - y -] - z -] ≡ [- x - [- y - z -] -]
  -- isSetPar : isSet Par
  -- ⬠ : ∀ x y z w → Path ( [- [- [- x - y -] - z -] - w -] ≡ [- x - [- y - [- z - w -] -] -])
  --              (assocPar _ _ _  ∙ assocPar _ _ _)
  --              (cong ([-_- w -]) (assocPar _ _ _) ∙∙ (assocPar _ _ _) ∙∙ cong ([- x -_-]) (assocPar _ _ _))              
  -- isGroupoidPar : isGroupoid Par
  
leftMost : ℕ → Par
leftMost zero = □
leftMost (suc n) = [- leftMost n - □ -]

rigthMost : ℕ → Par
rigthMost zero = □
rigthMost (suc n) = [- □ - rigthMost n -]




len : Par → ℕ
len □ = 1
len [- x - x₁ -] = len x + len x₁
len (assocPar x x₁ x₂ i) = +-assoc (len x) (len x₁) (len x₂) (~ i)
-- len (⬠ x x₁ x₂ x₃ i j) = 
 
--   isSetℕ (len x + len x₁ + len x₂ + len x₃) (len x + (len x₁ + (len x₂ + len x₃)))
--       (λ j → hcomp
--                (λ i₁ → primPOr j (~ j) (λ _ → +-assoc (len x) (len x₁) (len x₂ + len x₃) (~ i₁))
--                                          λ _ → +-assoc (len x + len x₁) (len x₂) (len x₃) (i1))
--                (+-assoc (len x + len x₁) (len x₂) (len x₃) (~ j)) )
  
--    (λ j → hcomp
--             (λ i₁ → primPOr j (~ j)
--                          (λ _ → (len x) + +-assoc (len x₁) (len x₂) (len x₃) (~ i₁))
--                          λ _ → (+-assoc (len x) (len x₁) (len x₂) i₁) + (len x₃)
--                          )
--             (+-assoc (len x) (len x₁ + len x₂) (len x₃) (~ j)))
--    i j

-- len (isGroupoidPar x x₁ x₂ y x₃ y₁ i i₁ i₂) =
--   isOfHLevelSuc 2 isSetℕ (len x) (len x₁) (λ i₂ → len (x₂ i₂)) (λ i₂ → len (y i₂)) (λ i₁ i₂ → len (x₃ i₁ i₂)) (λ i₁ i₂ → len (y₁ i₁ i₂)) i i₁ i₂ 


NestedΣ : ∀ {ℓ} → ∀ sh → (Σ (Sig ℓ (len sh)) (isSet ∘ NestedΣᵣ))) → hSet ℓ

NestedΣ-NestedΣᵣ-Iso : ∀ {ℓ} → (sh : Par) → (s : Σ (Sig ℓ (len sh)) (isSet ∘ NestedΣᵣ)))
                      → Iso (fst (NestedΣ sh s)) (NestedΣᵣ (fst s))



NestedΣ □ hs = hs
NestedΣ [- shL - shR -] ss@(s , isSetΣᵣ-s) =

   let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s
   in Σ (fst (NestedΣ shL sL ?)) (fst ∘ NestedΣ shR ∘ sR ∘ {!!}) , {!!}

NestedΣ (assocPar sh sh₁ sh₂ i) s ss = {!!}

NestedΣ-NestedΣᵣ-Iso = {!!}

-- NestedΣ (⬠ sh sh₁ sh₂ sh₃ x₁ i) x = {!!}
-- NestedΣ (isGroupoidPar sh sh₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}

-- isSet-Par' : ∀ p q → len p ≡ len q → p ≡ q
-- isSet-Par' p q x = {!p q!}

-- isSet-Par' : ∀ n → ∀ p → len p ≡ suc n → p ≡ rigthMost n
-- isSet-Par' zero □ x = refl
-- isSet-Par' zero [- p - p₁ -] x = {!!}
-- isSet-Par' zero (assocPar p p₁ p₂ i) x = {!!}
-- isSet-Par' zero (⬠ p p₁ p₂ p₃ x₁ i) x = {!len (⬠ p p₁ p₂ p₃ i0 i0)!}
-- isSet-Par' zero (isGroupoidPar p p₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}
-- isSet-Par' (suc n) □ x = {!!}
-- isSet-Par' (suc zero) [- p - p₁ -] x = {!!}
-- isSet-Par' (suc (suc n)) [- p - p₁ -] x =
--   let z = isSet-Par' (suc n) {!!} {!!}
--   in {!!}
-- isSet-Par' (suc n) (assocPar p p₁ p₂ i) x = {!!}
-- isSet-Par' (suc n) (⬠ p p₁ p₂ p₃ x₁ i) x = {!!}
-- isSet-Par' (suc n) (isGroupoidPar p p₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}


-- isSet-Par : ∀ n → ∀ p q → {!len p ≡ len q → p ≡ q!}
-- isSet-Par = {!!}

-- NestedΣ : ∀ {ℓ} → ∀ sh → Sig ℓ (len sh) → hSet ℓ

-- -- for any signature, there is isomorphism betwen NestedΣᵣ (nested Sigma in rigtmost shape)
-- -- and NestedΣ sh (nested Sigma in shape described by the argument of type Par)

-- NestedΣ-NestedΣᵣ-Iso : ∀ {ℓ} → (sh : Par) → (s : Sig ℓ (len sh))
--                       → Iso (fst (NestedΣ sh s)) (NestedΣᵣ s)

-- NestedΣ □ x = x , {!!}
-- NestedΣ [- shL - shR -] s = 
--    let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s
--    in Σ (fst (NestedΣ shL sL)) (fst ∘ NestedΣ shR ∘ sR ∘ Iso.fun (NestedΣ-NestedΣᵣ-Iso shL _)) , {!!}


-- NestedΣ (Par≡ i) s = {!!} --TypeOfHLevel≡ 2 {X = {! [- x - [- y - z -] -]!}} {Y = {!!}} {!!} i
-- NestedΣ (isSetPar sh sh₁ x₁ y i i₁) x = {!!}

-- NestedΣ-NestedΣᵣ-Iso = {!!}



-- -- -- NestedΣ : ∀ {ℓ} → ∀ sh → Sig ℓ (len sh) → Type ℓ

-- -- -- -- for any signature, there is isomorphism betwen NestedΣᵣ (nested Sigma in rigtmost shape)
-- -- -- -- and NestedΣ sh (nested Sigma in shape described by the argument of type Par)

-- -- -- NestedΣ-NestedΣᵣ-Iso : ∀ {ℓ} → (sh : Par) → (s : Sig ℓ (len sh))
-- -- --                       → Iso (NestedΣ sh s) (NestedΣᵣ s)

-- -- -- NestedΣ □ x = x
-- -- -- NestedΣ [- shL - shR -] s =
-- -- --    let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s
-- -- --    in Σ (NestedΣ shL sL) (NestedΣ shR ∘ sR ∘ Iso.fun (NestedΣ-NestedΣᵣ-Iso shL _))

-- -- -- NestedΣ-NestedΣᵣ-Iso □ s = idIso
-- -- -- NestedΣ-NestedΣᵣ-Iso [- shL - shR -] s =
-- -- --   let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s
-- -- --   in
-- -- --      _ Iso⟨ Σ-cong-iso-snd (λ _ → NestedΣ-NestedΣᵣ-Iso shR _) ⟩
-- -- --      _ Iso⟨ Σ-cong-iso-fst (NestedΣ-NestedΣᵣ-Iso shL sL) ⟩
-- -- --      _ Iso⟨ nestedΣᵣ-cs.isom-split {n = len shL} {m = len shR} _ ⟩ _ ∎Iso


-- -- -- -- NestedΣ≡ : ∀ {ℓ} → ∀ n → Sig ℓ n → ∥ Σ Par ((n ≡_) ∘ len) ∥  → Type {!!}

-- -- -- -- -- NestedΣ≡' : ∀ {ℓ} → ∀ n → (s : Sig ℓ n) → (p : ∥ Σ Par ((n ≡_) ∘ len) ∥ ) → NestedΣ≡ n s p ≡ NestedΣᵣ s 
-- -- -- -- -- NestedΣ≡'

-- -- -- -- -- --{ℓ} n s ∣ p , p≡ ∣ = isoToPath (NestedΣ-NestedΣᵣ-Iso p (subst (Sig _) p≡ s)) ∙ λ j → NestedΣᵣ ((transp (λ i → Sig ℓ (p≡ (i ∧ ~ j))) j s))
-- -- -- -- -- -- NestedΣ≡' n s (squash p q i) i₁ = {!NestedΣ≡' n s p!}


-- -- -- -- NestedΣ≡ n s = invEq (SetElim.trunc→Set≃₂ {!!}) {!!}

-- -- -- -- -- NestedΣₗ : ∀ {ℓ} → ∀ n → (s : Sig ℓ n) → Type ℓ 
-- -- -- -- -- NestedΣₗ zero s = {!!}
-- -- -- -- -- NestedΣₗ (suc n) s = {!!}

-- -- -- -- -- -- fromNestedΣₗ : ∀ {ℓ} → ∀ n → (s : Sig ℓ n) → Σ (Type ℓ) (λ x → (x → NestedΣᵣ s))
-- -- -- -- -- -- fromNestedΣₗ zero s = (Lift Unit) , idfun _
-- -- -- -- -- -- fromNestedΣₗ (suc zero) s = s , idfun _
-- -- -- -- -- -- fromNestedΣₗ (suc (suc n)) s = {!!} , {!!}
