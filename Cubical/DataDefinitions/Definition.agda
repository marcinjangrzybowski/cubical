{-# OPTIONS --cubical --no-exact-split --safe #-}

module Cubical.DataDefinitions.Definition where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Logic

open import Cubical.Data.Sum

open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary


open import Cubical.Data.Universe



Iso≡ : ∀ {ℓ} → (A : Type ℓ) → (iso1 iso2 : (Iso A A))
         → (fun= : Iso.fun iso1 ≡ Iso.fun iso2)
         → (inv= : Iso.inv iso1 ≡ Iso.inv iso2)
         → (sec= : ( transport (λ i₁ → (b : A) → fun= i₁ (inv= i₁ b) ≡ b) (Iso.rightInv iso1)) ≡ (Iso.rightInv iso2))
         → (ret= : ( transport (λ i₁ → (b : A) → inv= i₁ (fun= i₁ b) ≡ b) (Iso.leftInv iso1)) ≡ (Iso.leftInv iso2))
         → iso1 ≡ iso2 
Iso.fun (Iso≡ A iso1 iso2 fun= inv= _ _ i) = fun= i
Iso.inv (Iso≡ A iso1 iso2 fun= inv= _ _ i) = inv= i
Iso.rightInv (Iso≡ A iso1 iso2 fun= inv= sec= ret= i) = toPathP {A = λ i₁ → (section (fun= i₁) (inv= i₁))} {x = Iso.rightInv iso1} {y = Iso.rightInv iso2}
                   ( sec=) i   
Iso.leftInv (Iso≡ A iso1 iso2 fun= inv= sec= ret= i) = toPathP {A = λ i₁ → (retract (fun= i₁) (inv= i₁))} {x = Iso.leftInv iso1} {y = Iso.leftInv iso2}
                   ( ret=) i


Iso≡-Set : ∀ {ℓ} → (A : Type ℓ) → isSet A → (iso1 iso2 : (Iso A A))
         → (fun= : Iso.fun iso1 ≡ Iso.fun iso2)
         → (inv= : Iso.inv iso1 ≡ Iso.inv iso2)
         → iso1 ≡ iso2 
Iso.fun (Iso≡-Set A x iso1 iso2 fun= inv= i) = fun= i
Iso.inv (Iso≡-Set A x iso1 iso2 fun= inv= i) = inv= i
Iso.rightInv (Iso≡-Set A x iso1 iso2 fun= inv= i) b = x _ _ (coe0→i (λ x₁ →  fun= x₁ (inv= x₁ b) ≡ b) i (Iso.rightInv iso1 b))
                                                           ((coe1→i (λ x₁ →  fun= x₁ (inv= x₁ b) ≡ b) i (Iso.rightInv iso2 b))) i
Iso.leftInv (Iso≡-Set A x iso1 iso2 fun= inv= i) b = x _ _ (coe0→i (λ x₁ → inv= x₁ (fun= x₁ b) ≡ b) i (Iso.leftInv iso1 b))
                                                           ((coe1→i (λ x₁ → inv= x₁ (fun= x₁ b) ≡ b) i (Iso.leftInv iso2 b))) i


isSet-Iso-≡ : ∀ {ℓ} → (A : Type ℓ) → isSet A → Iso (Iso A A) (A ≡ A) 
isSet-Iso-≡ A isSet-A = iso (isoToPath) pathToIso h-sec h-ret
  where
    h-sec : (b : A ≡ A) → isoToPath (pathToIso b) ≡ b
    h-sec b = isInjectiveTransport (funExt λ x → transportRefl _)

    h-ret : (a : Iso A A) → pathToIso (isoToPath a) ≡ a
    h-ret a =  Iso≡-Set A isSet-A (pathToIso (isoToPath a)) a
                     (funExt λ x → transportRefl _)
                     (funExt λ x → cong (Iso.inv a) (transportRefl _))


record IsDefinition (B : Type₀ → Type₁) : Type₁ where
  constructor isDefinition

  field
    ww1 : ∀ A₁ A₂ → B A₁ → B A₂ → A₁ → A₂
    ww-law : ∀ A → ∀ ba → ∀ x → ww1 A A ba ba x ≡ x
    ww2 : ∀ A₁ A₂ → ∀ x → ∀ xx → section (ww1 A₂ A₁ x xx) (ww1 A₁ A₂ xx x)


  defToIso : ∀ {A₁ A₂} → B A₂ → B A₁ → Iso A₂ A₁
  defToIso {A₁} {A₂} x xx = (iso (ww1 A₂ A₁ x xx) (ww1 A₁ A₂ xx x) (ww2 A₁ A₂ x xx) ((ww2 A₂ A₁ xx x)))  

  defToPath : ∀ {A₁ A₂} → B A₂ → B A₁ → A₂ ≡ A₁
  defToPath {A₁} {A₂} x xx = isoToPath (defToIso x xx)  

  defToPath-Refl : ∀ {A} → ∀ ba → defToPath ba ba ≡ refl
  defToPath-Refl {A} ba = isInjectiveTransport (funExt λ x → cong (transp (λ i → A) i0) (ww-law _ _ x))

  defToPath-consistent : ∀ {A₁ A₂} → (ba : B A₁) →  (b : A₁ ≡ A₂) → defToPath ba (subst B b ba) ≡ b
  defToPath-consistent ba b =
    J {x = _} (λ y x → defToPath {y} {_} ba ((subst B x ba)) ≡ x) ((cong (defToPath ba ) (transportRefl _) ∙ defToPath-Refl ba)) b

  -- It would be nice to have this, but i am unable to prove it for any B
  
  -- field
  --   ww3 : ∀ A₁ A₂ → ∀ x → (a : B A₂) → subst B (f1 A₂ A₁ x a) x ≡ a

  -- def-≡ : ∀ A₁ A₂ → B A₁ → (( (B A₂)) ≡ ( (A₁ ≡ A₂)))
  -- def-≡ A₁ A₂ x = isoToPath (iso (λ x₁ → (f1 A₂ A₁ x (x₁))) (λ x₁ → (subst B ( x₁) x)) (def-11 A₁ A₂ x) ( ww3 A₁ A₂ x))


