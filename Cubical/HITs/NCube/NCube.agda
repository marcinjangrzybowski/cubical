{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.NCube where

--open import Cubical.Core.Glue

open import Cubical.Foundations.Everything as E 
import Cubical.Foundations.Id as Id

open import Cubical.HITs.Interval

open import Cubical.Data.Sigma
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Nat.Order

open import Cubical.Data.Bool




data hcube (A : Type₀) : Type₀ where
   co : Bool -> A -> hcube A
   ins : ∀ a → (co false a) ≡ (co true a)


Hcube : ℕ -> Type₀
Hcube zero = Unit
Hcube (suc n) = hcube (Hcube n)

  
data hborder (A : Type₀) (B : Type₀) (C : A → B) : Type₀ where
   sideBo : Bool → B → hborder A B C
   tube : ∀ a → sideBo false (C a) ≡ sideBo true (C a)

injHelp : ∀ {A} → ∀ n → ∀ {B} → hborder A (Hcube n) B → Hcube (suc n)
injHelp n (sideBo x x₁) = co x x₁
injHelp n {B} (tube a i) = ins  {Hcube n} (B a) i

Hborder : (n : ℕ) → Type₀

borderInj : ∀ {n} → Hborder n → Hcube n

Hborder zero = ⊥
Hborder (suc n) = hborder ((Hborder n)) _ borderInj

borderInj {zero} = ⊥-elim
borderInj {suc n} = injHelp n

borderCapInj : ∀ {n} → Bool → Hcube n → Hborder (suc n) 
borderCapInj = sideBo

borderEndInj : ∀ {n} → Bool → Hborder n → Hborder (suc n) 
borderEndInj {n} b = (borderCapInj {n} b) E.∘ borderInj

hcubeEndInd : ∀ {n} → Bool → Hcube n → Hcube (suc n)
hcubeEndInd  = co

borderEndInj≡ : ∀ {n} → borderEndInj {n} false ≡ borderEndInj {n} true 
borderEndInj≡ {n} i x = tube x i


-- -- -- --------------

Boundary : (A : Type₀) → (n : ℕ) → Type₀
Boundary A n = Hborder n → A

Cubi : (A : Type₀) → (n : ℕ) → Type₀
Cubi A n = Hcube n → A


Cubi→Boundary : ∀ {A : Type₀} → ∀ {n} → Cubi A n → Boundary A n 
Cubi→Boundary cu =  cu  E.∘ borderInj 

CubiEnd : ∀ {A} → ∀ {n} → Bool → Cubi A (suc n) → Cubi A n
CubiEnd x x₁ x₂ = x₁ (hcubeEndInd x x₂)

CubiEnd≡ : ∀ {A} → ∀ {n} → ∀ (cu : Cubi A (suc n))
   →  CubiEnd {n = n} false cu ≡ CubiEnd {n = n} true cu
CubiEnd≡ cu i x = cu (ins x i)

BoundaryEnd : ∀ {A} → ∀ {n} → Bool → Boundary A (suc n) → Boundary A n 
BoundaryEnd {n = n} x = E._∘ ((borderEndInj {n} x))

BoundaryEnd≡ : ∀ {A} → ∀ {n} → ∀ (bd : Boundary A (suc n))
   →  BoundaryEnd {n = n} false bd ≡ BoundaryEnd {n = n} true bd
BoundaryEnd≡ {n = n} bd i = (λ x → bd (borderEndInj≡ {n} i x)) 


Hycu :  ∀ {A : Type₀} → ∀ {n} → Boundary A n → Type₀
Hycu {A} {n} bd = Σ (Cubi A n) λ c → Cubi→Boundary c ≡ bd 

BoundaryCap : ∀ {A} → ∀ n → (b : Bool) → (bd : Boundary A (suc n))
             → Hycu {n = n} (BoundaryEnd {n = n} b bd) 
BoundaryCap n b bd = (λ x → bd (sideBo b x)) , E.refl


CubiDeco : ∀ {A : Type₀} → ∀ {n} → (c : Cubi A n)
                → Hycu {n = n} (Cubi→Boundary {n = n} c)
CubiDeco c = c , E.refl

-- many hours spent on trying to convince agda that this definition should mention HycuP itself,
-- so HycuP could be defined without "gluing" in Hycu
HycuP : ∀ {A : Type₀} → ∀ {n} → Boundary A n → Type₀
HycuP {A} {n = zero} _ =  A
HycuP {n = suc n} bd = PathP
             (λ i → Hycu {n = n} (BoundaryEnd≡ {n = n} bd i))
             (BoundaryCap n false bd)
             (BoundaryCap n true bd)

hycuP : ∀ {A} → ∀ n → ∀ bd → Hycu {A} {n = n} bd → HycuP {A} bd 
hycuP zero bd (c , _) = c _
hycuP (suc n) bd (c , bd-glue) i =
     (((λ i₁ → λ x → bd-glue (~ i₁) (sideBo false x)))
       ∙∙ (CubiEnd≡ c)
       ∙∙ (λ i₁ → λ x → bd-glue i₁ (sideBo true x))) i
      ,
      λ i₁ x → hcomp
         (λ k → λ {
            (i = i0) → (bd-glue (i₁ ∨ k) (sideBo false (borderInj x)))
          ; (i = i1) → (bd-glue (i₁ ∨ k) (sideBo true (borderInj x)))
          ; (i₁ = i1) → bd (tube x i)
         })
         ((bd-glue i₁ (tube x i)))

-- hycuP← : ∀ {A} → ∀ n → ∀ bd → HycuP {A} {n = n} bd → Hycu {A} bd 
-- fst (hycuP← zero bd x) x₁ = x
-- snd (hycuP← zero bd x) i ()
-- fst (hycuP← (suc n) bd x) (co false x₂) = fst (x i0) x₂
-- fst (hycuP← (suc n) bd x) (co true x₂) = fst (x i1) x₂
-- fst (hycuP← (suc n) bd x) (ins a i) = fst (x i) a
-- snd (hycuP← (suc zero) bd x) i (sideBo false tt) = bd (sideBo false _) 
-- snd (hycuP← (suc (suc n)) bd x) i (sideBo false (co x₁ x₂)) = {!snd (x i) ? ?!}
-- snd (hycuP← (suc (suc n)) bd x) i (sideBo false (ins a i₁)) = {!!}
-- snd (hycuP← (suc zero) bd x) i (sideBo true x₂) = bd (sideBo true _)
-- snd (hycuP← (suc (suc n)) bd x) i (sideBo true x₂) = {!!}
-- snd (hycuP← (suc n) bd x) i (tube a i₁) = {!!}




mkBo2 : ∀ {A : Type₀} → ∀ {w x y z : A }
               → (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
               → Boundary A 2
mkBo2 p q r s (sideBo false (co false x₁)) = q i0
mkBo2 p q r s (sideBo false (co true x₁)) = q i1
mkBo2 p q r s (sideBo false (ins a i)) = q i
mkBo2 p q r s (sideBo true (co false x₁)) = r i0
mkBo2 p q r s (sideBo true (co true x₁)) = r i1
mkBo2 p q r s (sideBo true (ins a i)) = r i
mkBo2 p q r s (tube (sideBo false x₁) i) = p i
mkBo2 p q r s (tube (sideBo true x₁) i) = s i



-- this Isomorphism is straightforward to prove,
-- after defining mkBo2 there is nothing to decide here
-- values can always be read form constraints after expanding arguments
Hycu2Test : ∀ {A : Type₀} → ∀ {w x y z : A }
              → (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
              → E.Iso (E.Square p q r s) (Hycu {A = A} {n = 2} (mkBo2 p q r s))
fst (Iso.fun (Hycu2Test {w = w} p q r s) x) (co false (co false x₂)) = w
fst (Iso.fun (Hycu2Test {x = x₁} p q r s) x) (co false (co true x₂)) = x₁
fst (Iso.fun (Hycu2Test p q r s) x) (co false (ins a i)) = q i
fst (Iso.fun (Hycu2Test {y = y} p q r s) x) (co true (co false x₂)) = y
fst (Iso.fun (Hycu2Test {z = z} p q r s) x) (co true (co true x₂)) = z
fst (Iso.fun (Hycu2Test p q r s) x) (co true (ins a i)) = r i
fst (Iso.fun (Hycu2Test p q r s) x) (ins (co false x₂) i) = p i
fst (Iso.fun (Hycu2Test p q r s) x) (ins (co true x₂) i) = s i
fst (Iso.fun (Hycu2Test p q r s) x) (ins (ins a i₁) i) = x i i₁
snd (Iso.fun (Hycu2Test {w = w} p q r s) x) i (sideBo false (co false x₂)) = w
snd (Iso.fun (Hycu2Test {x = x₁} p q r s) x) i (sideBo false (co true x₂)) = x₁
snd (Iso.fun (Hycu2Test p q r s) x) i (sideBo false (ins a i₁)) = q i₁
snd (Iso.fun (Hycu2Test {y = y} p q r s) x) i (sideBo true (co false x₂)) = y
snd (Iso.fun (Hycu2Test {z = z} p q r s) x) i (sideBo true (co true x₂)) = z
snd (Iso.fun (Hycu2Test p q r s) x) i (sideBo true (ins a i₁)) = r i₁
snd (Iso.fun (Hycu2Test p q r s) x) i (tube (sideBo false x₂) i₁) = p i₁
snd (Iso.fun (Hycu2Test p q r s) x) i (tube (sideBo true x₂) i₁) = s i₁
Iso.inv (Hycu2Test p q r s) x i j = 
   hcomp
    (λ k → λ {
            (i = i0) → (snd x) k (sideBo false (ins _ j)) 
          ; (i = i1) → (snd x) k (sideBo true ((ins _ j)))
          ; (j = i0) → (snd x) k (tube (sideBo false _) i)
          ; (j = i1) → (snd x) k ((tube (sideBo true _) i))
      })
    ((fst x) (ins (ins _ j) i))
    
fst (Iso.rightInv (Hycu2Test {w = w} p q r s) (fst₁ , snd₁) i) (co false (co false tt)) =
                                                           snd₁ (~ i) (sideBo false (co false _))
fst (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) (co false (co true tt)) =
                                                           snd₁ (~ i) (sideBo false (co true _))
fst (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) (co false (ins _ i₁)) =
                                                           snd₁ (~ i) (sideBo false (ins _ i₁)) 
fst (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) (co true (co false x₁)) =
                                                           snd₁ (~ i) (sideBo true (co false _))
fst (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) (co true (co true x₁)) =
                                                           snd₁ (~ i) (sideBo true (co true _))
fst (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) (co true (ins _ i₁)) =
                                                           snd₁ (~ i) (sideBo true (ins _ i₁))
fst (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) (ins (co false x₁) i₁) =
                                                           snd₁ (~ i) (tube (sideBo false _) i₁)
fst (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) (ins (co true x₁) i₁) =
                                                           snd₁ (~ i) (tube (sideBo true _) i₁)
fst (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) z) (ins (ins tt j) i) = 
    hcomp
    (λ k → λ {
            (i = i0) → snd₁ ((~ z) ∧ k) (sideBo false (ins tt j))
          ; (i = i1) → snd₁ ((~ z) ∧ k) (sideBo true (ins tt j))
          ; (j = i0) →  snd₁ ((~ z) ∧ k) (tube (sideBo false tt) i)
          ; (j = i1) → snd₁ ((~ z) ∧ k) (tube (sideBo true tt) i)
          ; (z = i1) → (fst₁ (ins (ins tt j) i))
      })
    (fst₁ (ins (ins tt j) i))

snd (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) i₁ (sideBo false (co false x₁)) =
                                    snd₁ (i₁ ∨ (~ i)) (sideBo false (co false x₁))
snd (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) i₁ (sideBo false (co true x₁)) =
                                    snd₁ (i₁ ∨ (~ i)) (sideBo false (co true x₁))
snd (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) i₁ (sideBo false (ins a i₂)) =
                                    snd₁ (i₁ ∨ (~ i)) (sideBo false (ins a i₂))
snd (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) i₁ (sideBo true (co false x₁)) =
                                    snd₁ (i₁ ∨ (~ i)) (sideBo true (co false x₁))
snd (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) i₁ (sideBo true (co true x₁)) =
                                    snd₁ (i₁ ∨ (~ i)) (sideBo true (co true x₁))
snd (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) i₁ (sideBo true (ins tt i₂)) =
                                    snd₁ (i₁ ∨ (~ i)) (sideBo true (ins tt i₂))
                                    
snd (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) i₁ (tube (sideBo false x₁) i₂) =
                                     snd₁ (i₁ ∨ (~ i)) (tube (sideBo false _) i₂) 
snd (Iso.rightInv (Hycu2Test p q r s) (fst₁ , snd₁) i) i₁ (tube (sideBo true x₁) i₂) =
                                    snd₁ (i₁ ∨ (~ i)) (tube (sideBo true _) i₂)
Iso.leftInv (Hycu2Test p q r s) a z i j = 
    hcomp
    (λ k → λ {
            (i = i0) → q j
          ; (i = i1) → r j
          ; (j = i0) → p i
          ; (j = i1) → s i
          ; (z = i1) → (a i j)
      })
    (a i j)
