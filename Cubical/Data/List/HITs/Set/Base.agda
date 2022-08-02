{-# OPTIONS --safe #-}

module Cubical.Data.List.HITs.Set.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Nat

private
  variable
    ℓ : Level

infixr 5 _++_

data List (A : Type ℓ) : Type ℓ where
  [] : List A
  [_] : A → List A
  _++_ : List A → List A → List A
  ++-unit-r : (xs : List A) → xs ++ [] ≡ xs
  ++-unit-l : (xs : List A) → [] ++ xs ≡ xs
  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
  trunc : isSet (List A)


module _ {A : Type ℓ} where

  infixr 5 _∷_
  infixr 5 _∷ʳ_

  _∷_ : A → List A → List A
  x ∷ xs = [ x ] ++ xs

  _∷ʳ_ : List A → A → List A
  xs ∷ʳ x = xs ++ [ x ]


  module Elim {ℓb} {B : List A → Type ℓb}
              (isSetB : ∀ x → isSet (B x))
              (b[] : B [])
              (b[_] : ∀ a → B [ a ])
              (_b++_ : ∀ {xs ys} → B xs → B ys → B (xs ++ ys))
              (b++ur : ∀ {xs} → (b : B xs) →
                        PathP (λ i → B (++-unit-r xs i)) (b b++ b[]) b)
              (b++ul : ∀ {xs} → (b : B xs) →
                        PathP (λ i → B (++-unit-l xs i)) (b[] b++ b) b)
              (b++-assoc : ∀ {xs ys zs} → (bx : B xs) (by : B ys) (bz : B zs)
                             → PathP (λ i → B (++-assoc xs ys zs i))
                                ((bx b++ by) b++ bz)
                                 (bx b++ (by b++ bz)))

              where

    f : ∀ x → B x
    f [] = b[]
    f [ a ] = b[ a ]
    f (xs ++ ys) = f xs b++ f ys
    f (++-unit-r x i) = b++ur (f x) i
    f (++-unit-l x i) = b++ul (f x) i
    f (++-assoc xs ys zs i) = b++-assoc (f xs) (f ys) (f zs) i
    f (trunc x y p q i₀ i₁) =
       (isOfHLevel→isOfHLevelDep (suc (suc zero)) isSetB)
            (f x) (f y)
            (cong f p) (cong f q)
            (trunc x y p q) i₀ i₁

  module ElimProp {ℓb} {B : List A → Type ℓb}
              (isPropB : ∀ x → isProp (B x))
              (b[] : B [])
              (b[_] : ∀ a → B [ a ])
              (_b++_ : ∀ {xs ys} → B xs → B ys → B (xs ++ ys))


              where

    f : ∀ x → B x
    f = Elim.f (isProp→isSet ∘ isPropB) b[] b[_] _b++_
      (λ _ → isProp→PathP (λ _ → isPropB _) _ _ )
      (λ _ → isProp→PathP (λ _ → isPropB _) _ _ )
      (λ _ _ _ → isProp→PathP (λ _ → isPropB _) _ _ )

  module Rec {ℓb} {B : Type ℓb}
              (isSetB : isSet B)
              (b[] : B)
              (b[_] : A → B)
              (_b++_ : B → B → B)
              (b++ur : (b : B) → (b b++ b[]) ≡ b)
              (b++ul : (b : B) → (b[] b++ b) ≡ b)
              (b++-assoc : (bx by bz : B) → ((bx b++ by) b++ bz) ≡ (bx b++ (by b++ bz)))

              where
    f : List A → B
    f [] = b[]
    f [ a ] = b[ a ]
    f (xs ++ ys) = f xs b++ f ys
    f (++-unit-r x i) = b++ur (f x) i
    f (++-unit-l x i) = b++ul (f x) i
    f (++-assoc xs ys zs i) =
       b++-assoc (f xs) (f ys) (f zs) i
    f (trunc x y p q i₀ i₁) =
       isSetB (f x) (f y) (cong f p) (cong f q) i₀ i₁

  length : List A → ℕ
  length = Rec.f isSetℕ 
    zero
    (λ _ → suc zero)
    _+_
    +-zero
    (λ _ → refl)
    (λ bx by bz → sym (+-assoc bx by bz))
    
  rev : List A → List A
  rev [] = []
  rev [ x ] = [ x ]
  rev (x ++ y) = rev y ++ rev x
  rev (++-unit-r x i) = ++-unit-l (rev x) i
  rev (++-unit-l x i) = ++-unit-r (rev x) i
  rev (++-assoc x y z i) = ++-assoc (rev z) (rev y) (rev x) (~ i)
  rev (trunc x y p q i₀ i₁) = trunc (rev x) (rev y) (cong rev p) (cong rev q) i₀ i₁ 
