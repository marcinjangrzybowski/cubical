{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.Base where

--open import Cubical.Core.Glue

-- open import Cubical.Foundations.Everything as E 
-- import Cubical.Foundations.Id as Id

-- open import Cubical.HITs.Interval

-- open import Cubical.Data.Sigma
-- open import Cubical.Data.Prod
-- open import Cubical.Data.Sum
-- open import Cubical.Data.Unit
-- open import Cubical.Data.Empty

-- open import Cubical.Data.List
-- open import Cubical.Data.Nat.Order



open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Cubical.Data.List
open import Cubical.HITs.Interval
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism



data Interval' : Type₀ where
   end : Bool → Interval'
   inside : end false ≡ end true 

fromI : I → Interval'
fromI x = inside x

Bool→I : Bool → I
Bool→I false = i0
Bool→I true = i1

NCube : ℕ -> Type₀
NCube zero = Unit
NCube (suc n) = Interval' × (NCube n)


data NBorder' {n} (X : Type₀) (injX : X → NCube (n)) : Type₀ where
   lid : Bool → NCube (n) → NBorder' X injX
   cyl : ∀ x → lid false (injX x) ≡ lid true (injX x)

NBorder : ℕ → Type₀

boundaryMap : ∀ {n} → NBorder n → NCube n

NBorder zero = ⊥
NBorder (suc n) = NBorder' {n} (NBorder n) (boundaryMap)

boundaryMap {zero} ()
boundaryMap {suc _} (lid x₁ x) = (end x₁) , x
boundaryMap {suc _} (cyl x i) = inside i ,  boundaryMap x



flipNBorderHead : ∀ {n} → Iso (NBorder (suc (suc n))) (NBorder (suc (suc n)))
flipNBorderHead = iso f f law law
  where
    f : _
    f (lid x (end x₁ , x₂)) = (lid x₁ (end x , x₂))
    f (lid x (inside i , x₂)) = (cyl (lid x x₂) i)
    f (cyl (lid x x₁) i) = (lid x (inside i , x₁))
    f (cyl (cyl x i₁) i) = (cyl (cyl x i) i₁)
    
    law : _
    law (lid x (end x₁ , x₂)) = refl
    law (lid x (inside i , x₂)) = refl
    law (cyl (lid x x₁) i) = refl
    law (cyl (cyl x i₁) i) = refl

lid' : ∀ {n} → Bool  → NCube n → NBorder (suc n) 
lid' = lid

borderEndMap : ∀ {n} → Bool → NBorder n → NBorder (suc n)
borderEndMap {n} x = lid x ∘ boundaryMap

cyl' : ∀ {n} → (bd : NBorder (suc n)) →
                          borderEndMap false bd ≡ borderEndMap true bd 
cyl' = cyl

cylEx : ∀ {n} → borderEndMap {n} false ≡ borderEndMap true 
cylEx i x = cyl x i

faceMap : ∀ {n}
          → ℕ → Bool
          → NCube n → NBorder (suc n)  
faceMap {suc n} (suc k) s (end x₂ , x₃) = lid x₂ (boundaryMap (faceMap k s x₃))
faceMap {suc n} (suc k) s (inside i , x₃) = cyl (faceMap k s x₃) i
faceMap  _  = lid

