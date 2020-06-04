{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.Interval.Base where

open import Cubical.Core.Everything

open import Cubical.Data.Bool

open import Cubical.Foundations.Prelude

data Interval : Type₀ where
  zero : Interval
  one  : Interval
  seg  : zero ≡ one

isContrInterval : isContr Interval
isContrInterval = (zero , (λ x → rem x))
  where
  rem : (x : Interval) → zero ≡ x
  rem zero      = refl
  rem one       = seg
  rem (seg i) j = seg (i ∧ j)

funExtInterval : ∀ {ℓ} (A B : Type ℓ) (f g : A → B) → ((x : A) → f x ≡ g x) → f ≡ g
funExtInterval A B f g p = λ i x → hmtpy x (seg i)
  where
  hmtpy : A → Interval → B
  hmtpy x zero    = f x
  hmtpy x one     = g x
  hmtpy x (seg i) = p x i

rec : ∀ {ℓ} → {A : Type ℓ} {a0 a1 : A}
               (p : a0 ≡ a1) → (x : Interval) → A
rec p zero = p i0
rec p one = p i1
rec p (seg i) = p i

intervalEta-rec : ∀ {ℓ} → {A : Type ℓ} 
                    → (f : Interval → A)
                    → rec (cong f seg) ≡ f
intervalEta-rec f i zero = f zero
intervalEta-rec f i one = f one
intervalEta-rec f i (seg i₁) = f (seg i₁)

elim : ∀ {ℓ} → (A : Interval → Type ℓ) → {x : A (seg i0)} → {y : A (seg i1)}
               (p : PathP (λ i → A (seg i)) x y) → (x : Interval) → A x
elim A p zero    = p i0
elim A p one     = p i1
elim A p (seg i) = p i

-- Note that this is not definitional (it is not proved by refl)
intervalEta : ∀ {ℓ} → ∀ {A : Interval → Type ℓ}
                (f : (x : Interval) → A x) → elim A (λ i → f (seg i)) ≡ f
intervalEta f i zero    = f zero
intervalEta f i one     = f one
intervalEta f i (seg j) = f (seg j)

end : Bool → Interval
end true = one
end false = zero
