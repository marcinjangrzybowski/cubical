{-# OPTIONS --safe #-}
module Cubical.Data.FinData.Transpositions where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
import Cubical.Foundations.GroupoidLaws as GL

open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.SetQuotients renaming ([_] to [_]/ ; rec to rec/ ; elimProp to elimProp/ ; elim to elim/)

import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetTruncation renaming (map to map₂)

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_) renaming (znots to ℕznots ; snotz to ℕsnotz)
open import Cubical.Data.List renaming (map to mapList)
import Cubical.Data.Vec as V
open import Cubical.Data.FinData
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥


open import Cubical.Foundations.Function
-- open import Cubical.Functions.Logic
open import Cubical.Functions.FunExtEquiv


open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Generators

-- open import Cubical.HITs.FreeGroup
open import Cubical.HITs.FreeGroup.IPresentation3


open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Powerset

-- open import Cubical.Data.List.FinData

open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary

open import Cubical.HITs.ListedFiniteSet.Base2 as FM2

data PermR : ℕ → Type₀ where
  invo : ∀ {n} → PermR (suc n)
  braid : ∀ {n} → PermR (suc (suc n))
  comm : ∀ {n} → Fin n → PermR (suc (suc n))

weakPermR : ∀ {n} → PermR n → PermR (suc n)
weakPermR invo = invo
weakPermR braid = braid
weakPermR (comm x) = comm (weakenFin x)

permRel : ∀ n → PermR n → (List (Fin n) × Fin n )
permRel _ invo = zero ∷ [] , zero
permRel _ braid = zero ∷ one ∷ zero ∷ one ∷ zero ∷ [] , one
permRel _ (comm x) = zero ∷ (suc (suc x)) ∷ zero ∷  [] , suc (suc x)

data PermR' : ℕ → Type₀ where
  zero : ∀ {n k} → PermR n → PermR' (k + n)

¬PermRzero : PermR zero → ⊥.⊥
¬PermRzero ()


spit' : ∀ n → PermR' n → PermR n
spit' .(zero + n) (zero {n} {zero} x) = x
spit' .(suc k + n) (zero {n} {suc k} x) = weakPermR (spit' _ (zero {n} {k} x))

-- mkPermR' : ∀ n → PermR n → PermR' n
-- mkPermR' n = zero {k = zero}

-- weakenPerm' : ∀ n → PermR' n → PermR' (suc n)
-- weakenPerm' n x = (mkPermR' _ (weakPermR (spit' n x)))

-- sucPerm' : ∀ n → PermR' n → PermR' (suc n)
-- sucPerm' n x = zero {n = n} {k = one} (spit' _ x)


¬PermR'zero : PermR' zero → ⊥.⊥
¬PermR'zero = ¬PermRzero ∘ spit' _

permRel' : ∀ n → PermR' n → (List (Fin n) × Fin n )
permRel' _ (zero {k = k} x) = map-× (mapList +k) +k  (permRel _ x)

open Presentation

relatorPerm : ∀ n → PermR' (predℕ n) → List (Fin (predℕ n) ⊎ Fin (predℕ n)) × Fin (predℕ n)
relatorPerm = λ n → (map-fst (mapList ⊎.inl) ∘ permRel' (predℕ n))



Perm : ℕ → Group ℓ-zero
Perm n = presentedGroupGroup
           _ _ (relatorPerm n)

rlt' : ∀ {n} → PermR' (predℕ n) → ⟨ Perm n ⟩ 
rlt' {n} = rlt _ _ (relatorPerm n)

Eli : ∀ {ℓ''} n  → Eliminators _ _ (map-fst (mapList ⊎.inl) ∘ permRel' n) ℓ''
Eliminators.elimPropPG (Eli n) bTrunc b b· bε bInv = w
  where
    w : _
    w (η x) = b x
    w (x · x₁) = b· (w x) (w x₁)
    w ε = bε
    w (inv x) = bInv (w x)
    w (assoc x x₁ x₂ i) = isProp→PathP (λ i → bTrunc (assoc x x₁ x₂ i))
         (b· (w x) (b· (w x₁) (w x₂))) (b· (b· (w  x) (w x₁)) (w x₂)) i 
    w (idr x i) = isProp→PathP (λ i → bTrunc (idr x i))
         (w x) (b· (w x) bε) i 
    w (idl x i) = isProp→PathP (λ i → bTrunc (idl x i))
         (w x) (b· bε (w x)) i 
    w (invr x i) = isProp→PathP (λ i → bTrunc (invr x i))
         (b· (w x) (bInv (w x))) bε i 
    w (invl x i) = isProp→PathP (λ i → bTrunc (invl x i))
         (b· (bInv (w x)) (w x)) bε i
    w (rel (zero invo) i) = isProp→PathP (λ i → bTrunc (rel (zero invo) i))
         (b· (b (+k zero)) (b (+k zero))) bε i
    w (rel (zero braid) i) = isProp→PathP (λ i → bTrunc (rel (zero braid) i))
         ( b· (b (+k zero))
           (b· (b (+k one))
            (b· (b (+k zero))
             (b· (b (+k one)) (b· (b (+k zero)) (b (+k one)))))))
         bε i
    w (rel (zero (comm x)) i) = isProp→PathP (λ i → bTrunc (rel (zero (comm x)) i))
         (b· (b (+k zero))
         (b· (b (+k (suc (suc x))))
          (b· (b (+k zero)) (b (+k (suc (suc x)))))))
         bε i
    w (trunc x y p q i i₁) =
       isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (bTrunc x))
         (w x) (w y) (cong w p) (cong w q) (trunc x y p q) i i₁
 

Eliminators.recPG (Eli n) B b Brel = w ,
    record { pres· = λ _ _ → refl ; pres1 = refl ; presinv = λ _ → refl }
  where

    module BG = GroupStr (snd B)

    w : _ → _
    w (η x) = b x
    w (x · x₁) = w x BG.· w x₁
    w ε = BG.1g
    w (inv x) = BG.inv (w x)
    w (assoc x x₁ x₂ i) = BG.·Assoc (w x) (w x₁) (w x₂) i
    w (idr x i) = sym (BG.·IdR (w x)) i 
    w (idl x i) = sym (BG.·IdL (w x)) i
    w (invr x i) = BG.·InvR (w x) i
    w (invl x i) = BG.·InvL (w x) i
    
    w (rel (zero invo) i) = Brel (zero invo) i 
    w (rel (zero braid) i) = Brel (zero braid) i
    w (rel (zero (comm x)) i) = Brel (zero (comm x)) i
    
    w (trunc x y p q i j) =
       BG.is-set (w x) (w y) (cong w p) (cong w q) i j 

sucHom : ∀ n → GroupHom (Perm n) (Perm (suc n))
sucHom zero = idGroupHom
sucHom (suc n) =
 Eliminators.recPG (Eli n) _
  (λ x → η (suc x) ) zz
   where
     
     zz : _ 
     zz (zero invo) = rel (zero {k = suc _} invo)
     zz (zero braid) = rel (zero {k = suc _} braid)
     zz (zero (comm x)) = rel (zero {k = suc _} (comm x))



sucPerm* : ∀ {n} → ⟨ Perm n ⟩ → ⟨ Perm (suc n) ⟩
sucPerm* = fst (sucHom _)




to≃ : ∀ n → GroupHom (Perm n) (SymData n)
to≃ zero = Eliminators.recPG (Eli zero) _ (λ ()) (⊥.rec ∘ ¬PermR'zero)
to≃ (suc n) = Eliminators.recPG (Eli n) _ adjTransposition w 
  where
    w : _
    w (zero invo) = adjTransposition²=idEquiv (+k zero)
    w (zero braid) = adjTranspositionBraid
    w (zero (comm x)) = commTranspositions' x


to≃' : ∀ n → fst (Perm n) → fst (SymData n)
to≃' n = (fst (to≃ n))

-- to≃* : ∀ n → fst (Perm n) → fst (SymData n)
-- to≃* n (η x) = adjTransposition* x
-- to≃* n (x · x₁) = to≃* n x ∙ₑ to≃* n x₁
-- to≃* n ε = idEquiv _
-- to≃* n (inv x) = invEquiv (to≃* n x)
-- to≃* n (assoc x x₁ x₂ i) =
--   compEquiv-assoc (to≃* n x) (to≃* n x₁) (to≃* n x₂) i
-- to≃* n (idr x i) = compEquivEquivId (to≃* n x) (~ i)
-- to≃* n (idl x i) = compEquivIdEquiv (to≃* n x) (~ i)
-- to≃* n (invr x i) = invEquiv-is-rinv (to≃* n x) i
-- to≃* n (invl x i) = invEquiv-is-linv (to≃* n x) i
-- to≃* zero (rel ix i) = w ix i
--   where
--     w : (ix : PermR' zero) → to≃* zero
--          (rlt (Fin zero) (PermR' zero)
--           (relatorPerm zero) ix)
--            ≡ idEquiv (Fin 0)
--     w (zero invo) = ?
--     w (zero braid) = ?
--     w (zero (comm x)) = ?


-- to≃* (suc n) (rel ix i) = w ix i
--   where
--     w : (ix : PermR' n) → to≃* (suc n)
--          (rlt (Fin (n)) (PermR' (n))
--           (relatorPerm (suc n)) ix)
--            ≡ to≃* (suc n) ε 
--     w (zero invo) = adjTransposition²=idEquiv (+k zero)
--     w (zero braid) = adjTranspositionBraid
--     w (zero (comm x)) = commTranspositions' x

    
-- to≃* n (trunc x x₁ x₂ y i i₁) = {!!}


parityHom : ∀ n → GroupHom (Perm (suc n)) BoolGroup
parityHom n = 
  Eliminators.recPG (Eli n)
   _ (λ _ → false)
    λ { (zero invo) → refl ; (zero braid) → refl ; (zero (comm x)) → refl}


Perm-inv : ∀ n → (a : Fin n) →
               Path
                  (PresentedGroup _ _ (map-fst (mapList _⊎_.inl) ∘ permRel' n))
                  (η a) (inv (η a))
Perm-inv (suc n) zero =
  GroupTheory.invUniqueR (Perm (suc (suc n))) (rel (zero {suc n} {zero} invo))
Perm-inv (suc (suc n)) (suc a) = cong (fst (sucHom (suc (suc n)))) (Perm-inv (suc n) a)

Perm-invo : ∀ n → (a : Fin n) →
               Path
                  (PresentedGroup _ _ (map-fst (mapList _⊎_.inl) ∘ permRel' n))
                  (η a · η a) ε
Perm-invo n a = cong (η a ·_) (Perm-inv n a) ∙ invr _ 

Perm-braid : ∀ n → Path ⟨ Perm (suc (suc (suc n))) ⟩
                      (η one · (η zero · η one)) (η zero · (η one · η zero))
Perm-braid n =
         invUniqueR (( sym (assoc _ _ _) ∙ sym (assoc _ _ _)) ∙
           (rel (zero {_} {zero} braid)))
         ∙ invDistr _ _
        ∙ cong₂ _·_ (sym (Perm-inv _ zero))
          (invDistr _ _
           ∙ cong₂ _·_ (sym (Perm-inv _ one)) (sym (Perm-inv _ zero))) 
  where
    open GroupTheory (Perm (suc (suc (suc n))))

PunchHeadInOutPerm : ∀ n → Fin n → ⟨ Perm n ⟩
PunchHeadInOutPerm (suc n) zero = ε
PunchHeadInOutPerm (suc (suc n)) (suc x) = η zero · sucPerm* (PunchHeadInOutPerm _ x)

from≃ : ∀ n → ⟨ SymData (suc n) ⟩ → ⟨ Perm (suc n) ⟩ 
from≃ zero _ = ε
from≃ (suc n) e =
  let  (e' , p) = unwindPermHead e
  in sucPerm* (from≃ _ e') · PunchHeadInOutPerm _ (fst e zero)


comm0 : ∀ n → (x : Fin n) →
         Path ⟨ Perm (suc (suc (suc n))) ⟩
          (η zero · η (suc (suc x)))
          (η (suc (suc x)) · η zero)
comm0 n x =
  let z = invUniqueL
           (sym (GS.·Assoc _ _ _)
             ∙ (rel (zero {suc (suc n)} {zero} (comm x)))) 
  in  z ∙ invDistr _ _ ∙ sym (cong₂ _·_ (Perm-inv (suc (suc n)) (suc (suc x)))
        ((Perm-inv ((suc (suc n)))  zero) ))

  where
    module GS = GroupStr (snd (Perm (suc (suc (suc n)))))
    open GroupTheory (Perm (suc (suc (suc n))))

0-comm-suc-suc : ∀ n → (g : ⟨ Perm (suc n) ⟩) →
                     Path ⟨ Perm (suc (suc (suc n))) ⟩
                     (η zero · sucPerm* (sucPerm* g))
                     (sucPerm* (sucPerm* g) · η zero) 
0-comm-suc-suc n = Eliminators.elimPropPG (Eli n)
  (λ _ → trunc _ _)
   (comm0 n)
   (λ {x} {y} p q → (GS.·Assoc _ _ _) ∙
       cong (_· (sucPerm* (sucPerm* y))) p
        ∙ sym  (GS.·Assoc _ _ _) ∙
         cong ((sucPerm* (sucPerm* x)) ·_) q
         ∙ GS.·Assoc _ _ _)
   (GS.·IdR (η zero) ∙ sym (GS.·IdL (η zero))) 
   λ {x} p → (cong (_· sucPerm* (sucPerm* (inv x))) ((Perm-inv ((suc (suc n)))  zero))
      ∙ sym (invDistr _ _)) ∙ sym (cong inv p)
       ∙ invDistr _ _ ∙
       cong (sucPerm* (sucPerm* (inv x)) ·_)
       (sym (Perm-inv ((suc (suc n)))  zero))

  where
    module GS = GroupStr (snd (Perm (suc (suc (suc n)))))
    open GroupTheory (Perm (suc (suc (suc n))))




-- -- module P' where

-- --   co : ∀ {n} → Fin n → Fin n → Type
-- --   co zero zero = ⊥
-- --   co zero one = ⊥
-- --   co zero (suc (suc x₁)) = Unit
-- --   co (suc x) x₁ = ⊥



-- --   data Perm' (n : ℕ) : Type where
-- --     [] : Perm' n
-- --     _∷_ : Fin (suc n) → Perm' n → Perm' n
-- --     invo : ∀ k xs → k ∷ k ∷ xs ≡ xs
-- --     comm : ∀ k l → co k l → ∀ xs → (k ∷ (l ∷ xs)) ≡ (l ∷ k ∷ xs)
-- --     braid : ∀ k xs → (suc k) ∷ weakenFin k ∷ (suc k) ∷ xs ≡
-- --                       weakenFin k ∷ (suc k) ∷ weakenFin k ∷ xs
-- --     trunc : isSet (Perm' n)

-- --   -- infixr 5 _P++_
-- --   infixr 5 _∷_


-- --   module Rec {ℓ} {B : ℕ → Type ℓ} (isSetB : ∀ {n} → isSet (B n))
-- --               (b[] : ∀ {n} → B n)
-- --               (b : ∀ {n} → (Fin (suc n)) → B n → B n)
-- --               (bInvo : ∀ {n} k x → (b {n} k (b k x)) ≡ x)
-- --               (bComm :  ∀ {n} k l p x → b {n} k (b l x) ≡ b l (b k x))
-- --               (bBraid : ∀ {n} k x → b (suc k) (b (weakenFin k) (b (suc k) x))
-- --                     ≡  b (weakenFin k) (b (suc k) (b (weakenFin k) x)))
-- --               where
  
-- --     f :  ∀ {n} → Perm' n → B n
-- --     f [] = b[]
-- --     f (k ∷ xs) = b k (f xs)
-- --     f (invo k xs i) = bInvo k (f xs) i
-- --     f (comm k l p xs i) = bComm k l p (f xs) i
-- --     f {n} (braid k xs i) = bBraid {n} k (f xs) i
-- --     f (trunc _ _ p q i i₁) =
-- --       isSetB _ _ (cong f p) (cong f q) i i₁ 


  

-- -- -- -- data FG2 (A : Type₀) : Type where
-- -- -- --   [] : FG2 A
-- -- -- --   _,,_∷_ : Bool → A → FG2 A → FG2 A
-- -- -- --   inv : ∀ b a xs → b ,, a ∷ (not b ,, a ∷ xs) ≡ xs
-- -- -- --   trunc : isSet (FG2 A)




-- -- -- -- module FreeG2 (A : Type) where


-- -- -- --   module Rec {ℓ} {B : Type ℓ} (isSetB : isSet B)
-- -- -- --               (b[] : B)
-- -- -- --               (b : Bool → A → B → B)
-- -- -- --               (bInv : ∀ b' a x → b b' a (b (not b') a x) ≡ x)
-- -- -- --               where
  
-- -- -- --     f :  FG2 A → B
-- -- -- --     f [] = b[]
-- -- -- --     f (x ,, x₁ ∷ x₂) = b x x₁ (f x₂)
-- -- -- --     f (inv b' a x i) = bInv b' a (f x) i
-- -- -- --     f (trunc _ _ p q i i₁) =
-- -- -- --       isSetB _ _ (cong f p) (cong f q) i i₁ 

-- -- -- --   module ElimProp {ℓ} {B : FG2 A → Type ℓ} (isPropB : ∀ x → isProp (B x))
-- -- -- --               (b[] : B [])
-- -- -- --               (b : ∀ b' a  {xs} → B xs → B (b' ,, a ∷ xs))

-- -- -- --               where
  
-- -- -- --     f : ∀ x → B x
-- -- -- --     f [] = b[]
-- -- -- --     f (x ,, x₁ ∷ x₂) = b x x₁ (f x₂)
-- -- -- --     f (inv b' a x i) = 
-- -- -- --       isProp→PathP
-- -- -- --         (λ i →  isPropB (inv b' a x i))
-- -- -- --          (b b' a (b (not b') a (f x))) (f x) i
-- -- -- --     f (trunc x y p q i i₁) =
-- -- -- --        isProp→SquareP (λ i i₁ → isPropB (trunc x y p q i i₁))
-- -- -- --             refl refl (cong f p) (cong f q) i i₁

-- -- -- --   infixr 5 _FG2++_

-- -- -- --   _FG2++_ : FG2 A → FG2 A → FG2 A
-- -- -- --   _FG2++_ [] x₁ = x₁
-- -- -- --   _FG2++_ (x ,, x₂ ∷ x₃) x₁ = x ,, x₂ ∷ (x₃ FG2++  x₁)
-- -- -- --   _FG2++_ (inv b a x i) x₁ = inv b a (x FG2++ x₁) i
-- -- -- --   _FG2++_ (trunc _ _ p q i j) x₁ =
-- -- -- --     trunc _ _ (λ j → (p j)  FG2++ x₁) (λ j → (q j) FG2++  x₁) i j

-- -- -- --   assocFG2 :  (x y z : FG2 A) → x FG2++ y FG2++ z ≡  (x FG2++ y) FG2++ z
-- -- -- --   assocFG2 = ElimProp.f
-- -- -- --     (λ _ → isPropΠ2 λ _ _ → trunc _ _)
-- -- -- --       (λ y z → refl) λ b a p y z i → b ,, a ∷ (p y z i)
 
-- -- -- --   FG2++[] : ∀ x → x FG2++ [] ≡ x
-- -- -- --   FG2++[] = ElimProp.f (λ _ → trunc _ _) refl
-- -- -- --    λ b a → cong (b ,, a ∷_)

-- -- -- --   iv : FG2 A →  FG2 A
-- -- -- --   iv = Rec.f trunc
-- -- -- --     []
-- -- -- --     (λ b a xs → xs FG2++ ((not b) ,, a ∷ []))
-- -- -- --     λ b a xs →
-- -- -- --       (λ i → assocFG2 xs ((notnot b i) ,, a ∷ []) ((not b) ,, a ∷ []) (~ i))
-- -- -- --       ∙ cong (xs FG2++_) (inv b a []) ∙
-- -- -- --       FG2++[] xs
  

-- -- -- --   lInv : (x : FG2 A) →  x FG2++ (iv x) ≡ []
-- -- -- --   lInv = ElimProp.f
-- -- -- --     (λ _ → trunc _ _)
-- -- -- --     refl
-- -- -- --     λ b a {xs} x →
-- -- -- --       cong (b ,, a ∷_)
-- -- -- --         ((assocFG2 xs (iv xs) (not b ,, a ∷ [])) ∙ (cong (_FG2++ (not b ,, a ∷ []))
-- -- -- --            x))
-- -- -- --         ∙ inv b a []

-- -- -- --   rInv : (x : FG2 A) →  (iv x) FG2++ x ≡ []
-- -- -- --   rInv = ElimProp.f
-- -- -- --     (λ _ → trunc _ _)
-- -- -- --       refl
-- -- -- --       λ b a {xs} x →
-- -- -- --        sym (assocFG2 (iv xs) _ _) ∙
-- -- -- --             cong (iv xs FG2++_)
-- -- -- --                ((λ i → (not b ,, a ∷ ((notnot b (~ i)) ,, a ∷ xs))) ∙ inv (not b) a xs)
-- -- -- --             ∙ x
       
-- -- -- --   gg : GroupStr (FG2 A)
-- -- -- --   GroupStr.1g gg = []
-- -- -- --   GroupStr._·_ gg = _FG2++_
-- -- -- --   GroupStr.inv gg = iv
-- -- -- --   GroupStr.isGroup gg =
-- -- -- --     makeIsGroup
-- -- -- --       trunc assocFG2  FG2++[] (λ _ → refl) lInv rInv

-- -- -- -- -- -- -- -- -- inv' : {A : Type} → ∀ a (xs : FG2 A) → a ∷' (a ∷ xs) ≡ xs 
-- -- -- -- -- -- -- -- -- inv' = {!!}

-- -- -- -- -- -- -- -- -- mL-lem : ∀ {n} → (e0 e1 : Fin (suc (suc n))) → ¬ e0 ≡ e1
-- -- -- -- -- -- -- -- --            → Path ⟨ Perm (suc (suc n)) ⟩
-- -- -- -- -- -- -- -- --                 (sucPerm* (PunchHeadInOutPerm (suc n) (predFin (e1 ρ e0)))
-- -- -- -- -- -- -- -- --                   · PunchHeadInOutPerm (suc (suc n)) e1)
-- -- -- -- -- -- -- -- --                 (η zero
-- -- -- -- -- -- -- -- --                    · (sucPerm* (PunchHeadInOutPerm (suc n) (predFin (e0 ρ e1)))
-- -- -- -- -- -- -- -- --                    · PunchHeadInOutPerm (suc (suc n)) e0))
-- -- -- -- -- -- -- -- -- mL-lem zero zero p = ⊥.rec (p refl)
-- -- -- -- -- -- -- -- -- mL-lem zero (suc e1) p =
-- -- -- -- -- -- -- -- --   (ε · (η zero · sucPerm* (PunchHeadInOutPerm (suc _) e1)))
-- -- -- -- -- -- -- -- --      ≡⟨ sym (idl _) ⟩
-- -- -- -- -- -- -- -- --   (η zero · sucPerm* (PunchHeadInOutPerm (suc _) e1))
-- -- -- -- -- -- -- -- --      ≡⟨ cong (η zero ·_) (idr _) ⟩
-- -- -- -- -- -- -- -- --    (η zero · (sucPerm* (PunchHeadInOutPerm (suc _) e1) · ε )) ∎
-- -- -- -- -- -- -- -- -- mL-lem (suc e0) zero x =
-- -- -- -- -- -- -- -- --   (sucPerm* (PunchHeadInOutPerm (suc _) e0) · ε)
-- -- -- -- -- -- -- -- --     ≡⟨ sym (idr _) ⟩ _
-- -- -- -- -- -- -- -- --     ≡⟨ idl _ ⟩ _
-- -- -- -- -- -- -- -- --     ≡⟨ cong (_· sucPerm* (PunchHeadInOutPerm (suc _) e0)) (sym (Perm-invo _ zero)) ⟩ _
-- -- -- -- -- -- -- -- --     ≡⟨ sym (assoc _ _ _) ∙
-- -- -- -- -- -- -- -- --       cong (_· (η zero · sucPerm* (PunchHeadInOutPerm (suc _) e0))) (idr _) ∙ sym (assoc _ _ _) ⟩
-- -- -- -- -- -- -- -- --     (η zero · (ε · (η zero · sucPerm* (PunchHeadInOutPerm (suc _) e0)))) ∎
-- -- -- -- -- -- -- -- -- mL-lem {zero} (suc e0) (suc e1) p =
-- -- -- -- -- -- -- -- --   ⊥.rec (p (cong {B = λ _ → Fin two}
-- -- -- -- -- -- -- -- --    suc (isContr→isProp isContrFin1 _ _)))
-- -- -- -- -- -- -- -- -- mL-lem {suc n} (suc e0) (suc e1) x = 
-- -- -- -- -- -- -- -- --   let z = mL-lem e0 e1 (x ∘ cong suc)
-- -- -- -- -- -- -- -- --       ff = _
-- -- -- -- -- -- -- -- --   in
-- -- -- -- -- -- -- -- --       (sucPerm* (PunchHeadInOutPerm (suc _) (predFin ((suc e1 ρ suc e0)))) ·
-- -- -- -- -- -- -- -- --         (η zero · sucPerm* (PunchHeadInOutPerm (suc _) e1)) )
-- -- -- -- -- -- -- -- --       ≡⟨ cong (λ x → (sucPerm* (PunchHeadInOutPerm (suc _) x) ·
-- -- -- -- -- -- -- -- --         (η zero · sucPerm* (PunchHeadInOutPerm (suc _) e1)) ))
-- -- -- -- -- -- -- -- --            (inj-toℕ ({!!} e0 e1 (x ∘ cong suc))) ⟩ --unwindPermHeadCompSwap0and1Suc''
           
-- -- -- -- -- -- -- -- --             (    ((η one)
-- -- -- -- -- -- -- -- --                 · sucPerm* (sucPerm* ((PunchHeadInOutPerm ((suc n)) ((predFin (e1 ρ e0)))))))
-- -- -- -- -- -- -- -- --               · (η zero · sucPerm* (PunchHeadInOutPerm (suc (suc n)) e1)))
-- -- -- -- -- -- -- -- --       ≡⟨ sym (assoc _ _ _) ∙ cong ((η one) ·_) (assoc _ _ _) ∙
-- -- -- -- -- -- -- -- --          cong (λ x → ((η one) · (x
-- -- -- -- -- -- -- -- --         · sucPerm* (PunchHeadInOutPerm (suc (suc n)) e1))))
-- -- -- -- -- -- -- -- --           (sym (0-comm-suc-suc _ (PunchHeadInOutPerm (suc n) (predFin (e1 ρ e0))))) ∙
-- -- -- -- -- -- -- -- --             cong (λ x → ((η one) · x))
-- -- -- -- -- -- -- -- --               (sym (assoc _ _ _)) ∙ (λ i → assoc (η one) (η zero) (sucPerm* (z i)) i)
-- -- -- -- -- -- -- -- --                ∙ assoc _ _ _ ⟩
-- -- -- -- -- -- -- -- --            ( ((η one · η zero ) · η one) · ff)
-- -- -- -- -- -- -- -- --       ≡⟨ cong (_· ff) (sym (assoc _ _ _) ∙ Perm-braid n ) ⟩
-- -- -- -- -- -- -- -- --               ((η zero · (η one · η zero)) ·
-- -- -- -- -- -- -- -- --                   (sucPerm*
-- -- -- -- -- -- -- -- --                    (sucPerm* (PunchHeadInOutPerm (suc n) (predFin (e0 ρ e1))))
-- -- -- -- -- -- -- -- --                    · sucPerm* (PunchHeadInOutPerm (suc (suc n)) e0)))
-- -- -- -- -- -- -- -- --       ≡⟨ sym (assoc _ _ _) ∙ cong (λ x → (η zero · x))
-- -- -- -- -- -- -- -- --            (sym (assoc _ _ _) ∙ cong (λ x → (η one · x))
-- -- -- -- -- -- -- -- --              ( assoc _ _ _ ∙  cong (_· sucPerm* (PunchHeadInOutPerm (suc (suc n)) e0))
-- -- -- -- -- -- -- -- --                  (0-comm-suc-suc n ((PunchHeadInOutPerm (suc n) ((predFin (e0 ρ e1))))))
-- -- -- -- -- -- -- -- --               ∙ sym (assoc _ _ _)) ∙ assoc _ _ _) ⟩
-- -- -- -- -- -- -- -- --                 (η zero ·
-- -- -- -- -- -- -- -- --                   (sucPerm* (η zero · sucPerm* (PunchHeadInOutPerm (suc n) ((predFin (e0 ρ e1)))))
-- -- -- -- -- -- -- -- --                    · (η zero · sucPerm* (PunchHeadInOutPerm (suc (suc n)) e0))))
-- -- -- -- -- -- -- -- --       ≡⟨ cong (λ x → (η zero ·
-- -- -- -- -- -- -- -- --         (sucPerm* (PunchHeadInOutPerm (suc _) x)
-- -- -- -- -- -- -- -- --          · (η zero · sucPerm* (PunchHeadInOutPerm (suc _) (e0))))))
-- -- -- -- -- -- -- -- --           (inj-toℕ (sym ({!!} e1 e0 (x ∘ cong suc ∘ sym)))) ⟩ --unwindPermHeadCompSwap0and1Suc''
-- -- -- -- -- -- -- -- --       (η zero ·
-- -- -- -- -- -- -- -- --         (sucPerm* (PunchHeadInOutPerm (suc _) (predFin (suc e0 ρ suc e1)))
-- -- -- -- -- -- -- -- --          · (η zero · sucPerm* (PunchHeadInOutPerm (suc _) (e0))))) ∎


-- -- -- -- -- -- -- -- -- mL' : ∀ n → (a : Fin n) → (g : ⟨ SymData (suc n) ⟩) →
-- -- -- -- -- -- -- -- --              from≃ _ (adjTransposition a ∙ₑ g) ≡ η a · from≃ _ g 
-- -- -- -- -- -- -- -- -- mL' .one (zero {zero}) =
-- -- -- -- -- -- -- -- --   Perm2Elim {A = λ g → (sucPerm* ε · PunchHeadInOutPerm 2 (fst (swap0and1≃ ∙ₑ g) zero)) ≡
-- -- -- -- -- -- -- -- --       (η zero · (sucPerm* ε · PunchHeadInOutPerm 2 (fst g zero)))}
-- -- -- -- -- -- -- -- --        (sym (idl _) ∙ cong (η zero ·_) (idr _))
-- -- -- -- -- -- -- -- --        (sym (idr _) ∙ ((sym (Perm-invo _ zero) ∙ idr _)
-- -- -- -- -- -- -- -- --          ∙ sym (assoc _ _ _)) ∙ cong (η zero ·_) (idl _))
-- -- -- -- -- -- -- -- -- mL' .(suc (suc n)) (zero {suc n}) e = 
-- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- --       (e'' , p') = unwindPermHead e'
-- -- -- -- -- -- -- -- --       (e'* , p*) = unwindPermHead (swap0and1≃ ∙ₑ e)
-- -- -- -- -- -- -- -- --       (e''* , p'*) = unwindPermHead e'*


-- -- -- -- -- -- -- -- --       g0 = PunchHeadInOutPerm (suc (suc (suc n))) (fst e zero)
-- -- -- -- -- -- -- -- --       g1 = sucPerm* (sucPerm* (from≃ n e''))
-- -- -- -- -- -- -- -- --       g1' = sucPerm (sucPerm (e''))
-- -- -- -- -- -- -- -- --       g3 = sucPerm* (PunchHeadInOutPerm (suc (suc n)) (fst e' zero))

-- -- -- -- -- -- -- -- --       lemSS : Path ⟨ Perm (suc (suc n)) ⟩
-- -- -- -- -- -- -- -- --                 (sucPerm* ((from≃ n e'')))
-- -- -- -- -- -- -- -- --                 (sucPerm* ( (from≃ n e''*)))
-- -- -- -- -- -- -- -- --       lemSS = cong {B = λ _ → ⟨ Perm (suc (suc n)) ⟩}
-- -- -- -- -- -- -- -- --                   (sucPerm* ∘ from≃ n) (unwindPermHeadCompSwap0and1FST e)

-- -- -- -- -- -- -- -- --   in  _ ≡⟨
-- -- -- -- -- -- -- -- --          cong {B = λ _ → ⟨ Perm (suc (suc (suc n))) ⟩}
-- -- -- -- -- -- -- -- --            (λ x → (sucPerm* (x · PunchHeadInOutPerm _ (fst e'* zero)))
-- -- -- -- -- -- -- -- --                  · PunchHeadInOutPerm _ ((fst e one))) (sym lemSS) ⟩
-- -- -- -- -- -- -- -- --       _ ≡⟨ sym (GS.·Assoc g1 _ _) ⟩
-- -- -- -- -- -- -- -- --       _ ≡⟨ cong {B = λ _ → ⟨ Perm (suc (suc (suc n))) ⟩}
-- -- -- -- -- -- -- -- --                    (g1 ·_) (
-- -- -- -- -- -- -- -- --                     mL-lem (fst e zero) (fst e one) (znots ∘ invEq (congEquiv e) )) ⟩
-- -- -- -- -- -- -- -- --       _ ≡⟨ GS.·Assoc g1 _ _ ∙ GS.·Assoc _ _ _ ⟩
-- -- -- -- -- -- -- -- --       _ ≡⟨ cong {B = λ _ → ⟨ Perm (suc (suc (suc n))) ⟩} (_· g0)
-- -- -- -- -- -- -- -- --                (cong {B = λ _ → ⟨ Perm (suc (suc (suc n))) ⟩} (_· g3)
-- -- -- -- -- -- -- -- --                  ((sym (0-comm-suc-suc _ ((from≃ n e'')))))
-- -- -- -- -- -- -- -- --                 ∙ sym (GS.·Assoc (η zero) g1 g3)) ∙ sym (GS.·Assoc (η zero) (g1 · g3) g0) ⟩
-- -- -- -- -- -- -- -- --         _ ∎


-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --     module GS = GroupStr (snd (Perm (suc (suc (suc n)))))
-- -- -- -- -- -- -- -- --     open GroupTheory (Perm (suc (suc (suc n))))


-- -- -- -- -- -- -- -- -- mL' .(suc n) (suc {n} a) e =
-- -- -- -- -- -- -- -- --   let  (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- --        (e'* , p*) = unwindPermHead (adjTransposition (suc a) ∙ₑ e)
-- -- -- -- -- -- -- -- --   in cong {B = λ _ → ⟨ Perm (suc (suc n)) ⟩}
-- -- -- -- -- -- -- -- --        {x = sucPerm* (from≃ _ e'*)} {y = η (suc a) · sucPerm* (from≃ _ e')}
-- -- -- -- -- -- -- -- --        (λ z → z · (PunchHeadInOutPerm _ (fst e zero)))
-- -- -- -- -- -- -- -- --           (cong {x = (from≃ n (fst (unwindPermHead (adjTransposition (suc a) ∙ₑ e))))}
-- -- -- -- -- -- -- -- --                  {y = (η a · from≃ n (fst (unwindPermHead e)))}
-- -- -- -- -- -- -- -- --              sucPerm* ( cong (from≃ n) (equivEq refl) ∙ mL' n a _))
-- -- -- -- -- -- -- -- --           ∙ sym (PresentedGroup.assoc _ _ _)

-- -- -- -- -- -- -- -- -- fromToSecId : ∀ n → from≃ n (idEquiv (Fin (suc n))) ≡ ε
-- -- -- -- -- -- -- -- -- fromToSecId zero = refl
-- -- -- -- -- -- -- -- -- fromToSecId (suc n) =
-- -- -- -- -- -- -- -- --   sym (idr _) ∙ cong sucPerm* (cong (from≃ n) unwindPermId ∙ fromToSecId n)

-- -- -- -- -- -- -- -- -- fromToSec : ∀ n → section (from≃ n) (fst (to≃ (suc n))) 
-- -- -- -- -- -- -- -- -- fromToSec n =
-- -- -- -- -- -- -- -- --   GeneratedElim'
-- -- -- -- -- -- -- -- --     (Perm (suc n))
-- -- -- -- -- -- -- -- --     (PresentedGeneratedBy' _ _ _ (Eli n) (λ _ → _ , Perm-inv n _))
-- -- -- -- -- -- -- -- --     (λ _ → trunc _ _)
-- -- -- -- -- -- -- -- --     (fromToSecId n)
-- -- -- -- -- -- -- -- --     λ a x p → mL' _ _ _ ∙ cong (η a ·_) p

-- -- -- -- -- -- -- -- -- fromToRet : ∀ n → retract (from≃ n) (fst (to≃ (suc n))) 
-- -- -- -- -- -- -- -- -- fromToRet n =
-- -- -- -- -- -- -- -- --     GeneratedElimConstr'
-- -- -- -- -- -- -- -- --     (SymData (suc n) )
-- -- -- -- -- -- -- -- --     (generatedSym n)
-- -- -- -- -- -- -- -- --     _
-- -- -- -- -- -- -- -- --     (cong ((fst (to≃ (suc n)))) (fromToSecId n))
-- -- -- -- -- -- -- -- --     λ a x p → (cong (fst (to≃ (suc n))) (mL' _ a _)) ∙ cong (adjTransposition a ∙ₑ_) p

-- -- -- -- -- -- -- -- -- GroupIsoPermSymData : ∀ n → GroupIso (Perm (suc n))  (SymData (suc n))
-- -- -- -- -- -- -- -- -- Iso.fun (fst (GroupIsoPermSymData n)) = fst (to≃ (suc n))
-- -- -- -- -- -- -- -- -- Iso.inv (fst (GroupIsoPermSymData n)) = from≃ n
-- -- -- -- -- -- -- -- -- Iso.rightInv (fst (GroupIsoPermSymData n)) = fromToRet n
-- -- -- -- -- -- -- -- -- Iso.leftInv (fst (GroupIsoPermSymData n)) = fromToSec n
-- -- -- -- -- -- -- -- -- snd (GroupIsoPermSymData n) = snd (to≃ (suc n))

-- -- -- -- -- -- -- -- -- parityHomSymData : ∀ n → GroupHom (SymData (suc n)) BoolGroup
-- -- -- -- -- -- -- -- -- parityHomSymData n = compGroupHom (_ , snd (invGroupIso (GroupIsoPermSymData n))) (parityHom n)


-- -- -- -- -- -- -- -- -- -- compTest0 : {!!}
-- -- -- -- -- -- -- -- -- -- compTest0 =
-- -- -- -- -- -- -- -- -- --   let z = permutationFromList (4 ∷ 3 ∷ 2 ∷ 1 ∷ 3 ∷ 1 ∷ [])
-- -- -- -- -- -- -- -- -- --       p : fst (to≃ 6) (from≃ 5 z) ≡ z
-- -- -- -- -- -- -- -- -- --       p = {!!}
-- -- -- -- -- -- -- -- -- --   in {!!}

-- -- -- -- -- -- -- -- -- -- parityHomSymDataTest : {!!}
-- -- -- -- -- -- -- -- -- -- parityHomSymDataTest = {!fst (parityHomSymData 8) (swap0and1≃)!}


-- -- -- -- -- -- -- -- -- --   -- Eliminators.elimPropPG (Eli n)
-- -- -- -- -- -- -- -- -- --   --  (λ _ → trunc _ _)
-- -- -- -- -- -- -- -- -- --   --  (fromToSec-1 n)
-- -- -- -- -- -- -- -- -- --   --  {!!}
-- -- -- -- -- -- -- -- -- --   --  (fromToSec-3 n)
-- -- -- -- -- -- -- -- -- --   --  {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- isSurjectionTo≃ : ∀ n → isSurjection (fst (to≃ n) )
-- -- -- -- -- -- -- -- -- -- -- -- isSurjectionTo≃ zero _ = PT.∣ ε , (equivEq (funExt (⊥.rec ∘ ¬Fin0))) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- isSurjectionTo≃ (suc n) b =
-- -- -- -- -- -- -- -- -- -- -- --  let (z , p) = generatedSym n b
-- -- -- -- -- -- -- -- -- -- -- --  in PT.∣ (concatG (Perm (suc n)) (mapList η z)) , {!!} ∙ p ∣₁ 


-- -- -- -- -- -- -- -- -- -- -- -- isEmbTo≃ : ∀ n → isEmbedding (fst (to≃ n) )
-- -- -- -- -- -- -- -- -- -- -- -- isEmbTo≃ = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- isOfHLevelList 0 isSetA


-- -- -- -- -- -- -- -- -- -- -- -- -- ListOfLenSymHom≃ : ∀ {ℓ} {A : Type ℓ} → (isSetA : isSet A) → ∀ n →
-- -- -- -- -- -- -- -- -- -- -- -- --    GroupHom (SymData (suc n)) (Symmetric-Group (ListOfLen A (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --     (isOfHLevelListOfLen 0 isSetA (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- fst (ListOfLenSymHom≃ isSetA n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- snd (ListOfLenSymHom≃ isSetA n) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- ListOfLenSymHom : ∀ {ℓ} {A : Type ℓ} → (isSetA : isSet A) → ∀ n →
-- -- -- -- -- -- -- -- -- -- -- -- --    GroupHom (Perm (suc n)) (Symmetric-Group (ListOfLen A (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --     (isOfHLevelListOfLen 0 isSetA (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- ListOfLenSymHom {A = A} isSetA n = Eliminators.recPG (Eli n) _  (w n)
-- -- -- -- -- -- -- -- -- -- -- -- --    (equivEq ∘ funExt ∘ uncurry ∘ w' n)

-- -- -- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- -- -- --     f : ∀ {n} → Fin n → ListOfLen A (suc n) → ListOfLen A (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- --     f _ ([] , p) = ⊥.rec (ℕznots p )
-- -- -- -- -- -- -- -- -- -- -- -- --     f {suc n} k (x₁ ∷ [] , p) = ⊥.rec (ℕznots (injSuc p))
-- -- -- -- -- -- -- -- -- -- -- -- --     f zero (x ∷ y ∷ l , p) = ((y ∷ x ∷ l) , p)
-- -- -- -- -- -- -- -- -- -- -- -- --     f (suc k) (x ∷ y ∷ l , p) =
-- -- -- -- -- -- -- -- -- -- -- -- --       let (l' , p') = f k ((y ∷ l) , injSuc p)
-- -- -- -- -- -- -- -- -- -- -- -- --       in x ∷ l' , cong suc p' 

-- -- -- -- -- -- -- -- -- -- -- -- --     fHlp : ∀ {n} → ∀ (k : Fin n) → (x : A) → (l : List A) → ∀ p p' 
-- -- -- -- -- -- -- -- -- -- -- -- --               → fst (f (suc k) (x ∷ l , p)) ≡ x ∷ fst (f k (l , p'))
-- -- -- -- -- -- -- -- -- -- -- -- --     fHlp k x [] p p' = ⊥.rec (ℕznots p' )
-- -- -- -- -- -- -- -- -- -- -- -- --     fHlp k x (x₁ ∷ l) p p' i = x ∷ fst (f k (x₁ ∷ l , isSetℕ _ _ (injSuc p) p' i))

-- -- -- -- -- -- -- -- -- -- -- -- --     fSec' : ∀ {n} → ∀ (k : Fin n) → (b : ListOfLen A (suc n)) → f k (f k b) .fst ≡ b .fst
-- -- -- -- -- -- -- -- -- -- -- -- --     fSec' k ([] , p) = ⊥.rec (ℕznots p )
-- -- -- -- -- -- -- -- -- -- -- -- --     fSec' {suc n} k (x ∷ [] , p) = ⊥.rec (ℕznots (injSuc p))
-- -- -- -- -- -- -- -- -- -- -- -- --     fSec' zero (x ∷ x₁ ∷ fst₁ , _) = refl
-- -- -- -- -- -- -- -- -- -- -- -- --     fSec' (suc k) (x ∷ x₁ ∷ fst₁ , p) =
-- -- -- -- -- -- -- -- -- -- -- -- --       (fHlp k x (fst (f k (x₁ ∷ fst₁ , injSuc p)))
-- -- -- -- -- -- -- -- -- -- -- -- --         _ _) ∙ cong (x ∷_) (fSec' k (x₁ ∷ fst₁ , injSuc p))


-- -- -- -- -- -- -- -- -- -- -- -- --     fSec : ∀ {n} → ∀ (k : Fin n) → section (f k) (f k)
-- -- -- -- -- -- -- -- -- -- -- -- --     fSec k b = Σ≡Prop (λ _ → isSetℕ _ _) (fSec' k b)

-- -- -- -- -- -- -- -- -- -- -- -- --     fBraid : ∀ n k → ∀ l → (p : length l ≡ suc (k + suc (suc n))) → 
-- -- -- -- -- -- -- -- -- -- -- -- --                      f (+k one)
-- -- -- -- -- -- -- -- -- -- -- -- --                        (f (+k zero)
-- -- -- -- -- -- -- -- -- -- -- -- --                         (f (+k one) (f (+k zero) (f (+k one) (f (+k zero) (l , p))))))
-- -- -- -- -- -- -- -- -- -- -- -- --                        .fst
-- -- -- -- -- -- -- -- -- -- -- -- --                        ≡ l
-- -- -- -- -- -- -- -- -- -- -- -- --     fBraid n k [] p = ⊥.rec (ℕznots p )
-- -- -- -- -- -- -- -- -- -- -- -- --     fBraid n k (x ∷ []) p = ⊥.rec (ℕznots (injSuc (p ∙ cong suc (+-suc k (suc n)))) )
-- -- -- -- -- -- -- -- -- -- -- -- --     fBraid n k (x ∷ x₁ ∷ []) p = ⊥.rec (ℕznots (injSuc (injSuc (p ∙ {!!})) ))
-- -- -- -- -- -- -- -- -- -- -- -- --     fBraid n zero (x ∷ x₁ ∷ x₂ ∷ l) p = refl
-- -- -- -- -- -- -- -- -- -- -- -- --     fBraid n (suc k) (x ∷ x₁ ∷ x₂ ∷ l) p =
-- -- -- -- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --       ∙ cong (x ∷_) (fBraid n (k) (x₁ ∷ x₂ ∷ l) (injSuc p))
    
-- -- -- -- -- -- -- -- -- -- -- -- --     w : ∀ n → Fin n → ListOfLen A (suc n) ≃ ListOfLen A (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- --     fst (w n k) = f k
-- -- -- -- -- -- -- -- -- -- -- -- --     snd (w n k) = isoToIsEquiv i
-- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- --         i : Iso _ _
-- -- -- -- -- -- -- -- -- -- -- -- --         Iso.fun i = f k
-- -- -- -- -- -- -- -- -- -- -- -- --         Iso.inv i = f k
-- -- -- -- -- -- -- -- -- -- -- -- --         Iso.rightInv i = fSec k
-- -- -- -- -- -- -- -- -- -- -- -- --         Iso.leftInv i = fSec k

-- -- -- -- -- -- -- -- -- -- -- -- --     w' : ∀ n → (ix : PermR' n) → ∀ l → ∀ p →
-- -- -- -- -- -- -- -- -- -- -- -- --                 fst (foldr
-- -- -- -- -- -- -- -- -- -- -- -- --                 (GroupStr._·_
-- -- -- -- -- -- -- -- -- -- -- -- --                  (Symmetric-Group (ListOfLen A (suc n)) (isOfHLevelListOfLen 0 isSetA (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --                   .snd)
-- -- -- -- -- -- -- -- -- -- -- -- --                  ∘
-- -- -- -- -- -- -- -- -- -- -- -- --                  ⊎.elim (w n)
-- -- -- -- -- -- -- -- -- -- -- -- --                  (λ y →
-- -- -- -- -- -- -- -- -- -- -- -- --                     GroupStr.inv
-- -- -- -- -- -- -- -- -- -- -- -- --                     (Symmetric-Group (ListOfLen A (suc n)) (isOfHLevelListOfLen 0 isSetA (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --                      .snd)
-- -- -- -- -- -- -- -- -- -- -- -- --                     (w n y)))
-- -- -- -- -- -- -- -- -- -- -- -- --                 (w n (snd ((relatorPerm (suc n)) ix)))
-- -- -- -- -- -- -- -- -- -- -- -- --                 (fst ((map-fst (mapList _⊎_.inl) ∘ permRel' n) ix))) (l , p)
-- -- -- -- -- -- -- -- -- -- -- -- --                 ≡
-- -- -- -- -- -- -- -- -- -- -- -- --                 fst (GroupStr.1g
-- -- -- -- -- -- -- -- -- -- -- -- --                 (Symmetric-Group (ListOfLen A (suc n)) (isOfHLevelListOfLen 0 isSetA (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --                  .snd)) (l , p)
-- -- -- -- -- -- -- -- -- -- -- -- --     w' .(k + suc _) (zero {k = k} invo) l p = fSec (+k zero) (l , p)
-- -- -- -- -- -- -- -- -- -- -- -- --     w' .(k + suc (suc _)) (zero {k = k} braid) l p = Σ≡Prop (λ _ → isSetℕ _ _) (fBraid _ k l p)
-- -- -- -- -- -- -- -- -- -- -- -- --     w' .(k + suc (suc _)) (zero {k = k} (comm x)) = {!!}




-- -- -- -- -- -- -- -- -- -- -- -- -- ListSymHom : ∀ {ℓ} {A : Type ℓ} → (isSetA : isSet A) → ∀ n →
-- -- -- -- -- -- -- -- -- -- -- -- --    GroupHom (Perm (suc n)) (Symmetric-Group (List A) (isOfHLevelList 0 isSetA))
-- -- -- -- -- -- -- -- -- -- -- -- -- ListSymHom {A = A} isSetA n = Eliminators.recPG (Eli n) _  (w n) {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- --     f : ∀ {n} → Fin n → List A → List A
-- -- -- -- -- -- -- -- -- -- -- -- --     f _ [] = []
-- -- -- -- -- -- -- -- -- -- -- -- --     f _ (x₁ ∷ []) = (x₁ ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- --     f zero (x ∷ y ∷ l) = (y ∷ x ∷ l)
-- -- -- -- -- -- -- -- -- -- -- -- --     f (suc k) (x ∷ y ∷ l) = x ∷ f k (y ∷ l)

-- -- -- -- -- -- -- -- -- -- -- -- --     fSec : ∀ {n} → ∀ (k : Fin n) → section (f k) (f k) 
-- -- -- -- -- -- -- -- -- -- -- -- --     fSec k [] = refl
-- -- -- -- -- -- -- -- -- -- -- -- --     fSec k (x ∷ []) = refl
-- -- -- -- -- -- -- -- -- -- -- -- --     fSec zero (x ∷ x₁ ∷ b) = refl
-- -- -- -- -- -- -- -- -- -- -- -- --     fSec (suc k) (x ∷ x₁ ∷ b) =  {!!} ∙ cong (x ∷_) (fSec k (x₁ ∷ b)) 
 
-- -- -- -- -- -- -- -- -- -- -- -- --     w : ∀ n → Fin n → List A ≃ List A
-- -- -- -- -- -- -- -- -- -- -- -- --     fst (w n k) = f k
-- -- -- -- -- -- -- -- -- -- -- -- --     snd (w n k) = isoToIsEquiv i
-- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- --         i : Iso (List A) (List A)
-- -- -- -- -- -- -- -- -- -- -- -- --         Iso.fun i = f k
-- -- -- -- -- -- -- -- -- -- -- -- --         Iso.inv i = f k
-- -- -- -- -- -- -- -- -- -- -- -- --         Iso.rightInv i = fSec k
-- -- -- -- -- -- -- -- -- -- -- -- --         Iso.leftInv i = fSec k


-- -- -- -- -- -- -- -- -- -- -- -- -- module _ (n : ℕ) where 

-- -- -- -- -- -- -- -- -- -- -- -- --   module zz =
-- -- -- -- -- -- -- -- -- -- -- -- --     IsoOnGens' (Fin n) (Perm (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --               η (PresentedGeneratedBy' _ _ _ (Eli n) λ _ → _ , Perm-inv n _) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --               (to≃ (suc n)) _ (generatedSym n) refl (sym (generatedSymId n))
-- -- -- -- -- -- -- -- -- -- -- -- --                {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --                {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- IdsOfG : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (f : A → B) → isGroupoid B →
-- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- IdsOfG f isGB = {!!}
-- -- -- -- -- -- -- -- -- -- -- --  -- makeGroup {G = ∀ (x : A) → singl x}
-- -- -- -- -- -- -- -- -- -- -- --  --  (λ x → x , refl)
-- -- -- -- -- -- -- -- -- -- -- --  --  (λ x x₁ x₂ → (fst (x₁ (fst (x x₂))) ) , (snd (x x₂)) ∙ {!!})
-- -- -- -- -- -- -- -- -- -- -- --  --  {!!} {!!} {!!} {!!} {!!} {!!} {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- LoopsOfG : ∀ {ℓ} {A : Type ℓ} → isGroupoid A →
-- -- -- -- -- -- -- -- -- -- -- -- --      A → Group ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- LoopsOfG isG x =
-- -- -- -- -- -- -- -- -- -- -- -- --  makeGroup {G = x ≡ x} refl
-- -- -- -- -- -- -- -- -- -- -- -- --   _∙_ sym (isG x x) GL.assoc (sym ∘ GL.rUnit) (sym ∘ GL.lUnit) rCancel lCancel  

-- -- -- -- -- -- -- -- -- -- -- -- module Mon2Loops {ℓ} (A : Type ℓ) (isSetA : isSet A) where
-- -- -- -- -- -- -- -- -- -- -- --   open import Cubical.HITs.FreeGroup

-- -- -- -- -- -- -- -- -- -- -- --   -- private
-- -- -- -- -- -- -- -- -- -- -- --   --   variable
-- -- -- -- -- -- -- -- -- -- -- --   --     ℓ : Level
-- -- -- -- -- -- -- -- -- -- -- --   --     A : Type ℓ


-- -- -- -- -- -- -- -- -- -- -- --   infixr 5 _∷2_

-- -- -- -- -- -- -- -- -- -- -- --   data FMSet2  : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- --     []    : FMSet2
-- -- -- -- -- -- -- -- -- -- -- --     _∷2_   : (x : A) → (xs : FMSet2) → FMSet2
-- -- -- -- -- -- -- -- -- -- -- --     comm  : ∀ x y xs → x ∷2 y ∷2 xs ≡ y ∷2 x ∷2 xs
-- -- -- -- -- -- -- -- -- -- -- --     comm-inv : ∀ x y xs → 
-- -- -- -- -- -- -- -- -- -- -- --                 comm x y xs ≡ sym (comm y x xs)
-- -- -- -- -- -- -- -- -- -- -- --     hexDiag : ∀ x y z xs → x ∷2 y ∷2 z ∷2  xs ≡ z ∷2 y ∷2 x ∷2 xs
-- -- -- -- -- -- -- -- -- -- -- --     hexU : ∀ x y z xs →
-- -- -- -- -- -- -- -- -- -- -- --                Square
-- -- -- -- -- -- -- -- -- -- -- --                  (cong (y ∷2_) (comm _ _ _))
-- -- -- -- -- -- -- -- -- -- -- --                  (hexDiag x y z xs)
-- -- -- -- -- -- -- -- -- -- -- --                  (comm _ _ _)
-- -- -- -- -- -- -- -- -- -- -- --                  (comm _ _ _)
-- -- -- -- -- -- -- -- -- -- -- --     hexL : ∀ x y z xs →
-- -- -- -- -- -- -- -- -- -- -- --                Square
-- -- -- -- -- -- -- -- -- -- -- --                  (hexDiag x y z xs)
-- -- -- -- -- -- -- -- -- -- -- --                  (comm _ _ _)
-- -- -- -- -- -- -- -- -- -- -- --                  (cong (x ∷2_) (comm _ _ _))
-- -- -- -- -- -- -- -- -- -- -- --                  (cong (z ∷2_) (comm _ _ _))
-- -- -- -- -- -- -- -- -- -- -- --     trunc : isGroupoid (FMSet2)

-- -- -- -- -- -- -- -- -- -- -- --   module RecSet {ℓ'} {B : Type ℓ'} (BSet : isSet B)
-- -- -- -- -- -- -- -- -- -- -- --     ([]* : B) (_∷*_ : A → B → B)
-- -- -- -- -- -- -- -- -- -- -- --     (comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b))
-- -- -- -- -- -- -- -- -- -- -- --     (hexDiag* : ∀ x y z b → x ∷* (y ∷* (z ∷* b)) ≡ z ∷* (y ∷* (x ∷* b)) )
-- -- -- -- -- -- -- -- -- -- -- --     where

-- -- -- -- -- -- -- -- -- -- -- --     f : FMSet2 → B
-- -- -- -- -- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- -- -- -- -- --     f (x ∷2 x₁) = x ∷* f x₁
-- -- -- -- -- -- -- -- -- -- -- --     f (comm x y x₁ i) = comm* x y (f x₁) i
-- -- -- -- -- -- -- -- -- -- -- --     f (comm-inv x y x₁ i i₁) =
-- -- -- -- -- -- -- -- -- -- -- --         isSet→isSet' BSet
-- -- -- -- -- -- -- -- -- -- -- --           (comm* x y (f x₁))
-- -- -- -- -- -- -- -- -- -- -- --           (sym (comm* y x (f x₁)))
-- -- -- -- -- -- -- -- -- -- -- --           refl
-- -- -- -- -- -- -- -- -- -- -- --           refl i i₁
-- -- -- -- -- -- -- -- -- -- -- --     f (hexDiag x y z x₁ i) = hexDiag* x y z (f x₁) i
-- -- -- -- -- -- -- -- -- -- -- --     f (hexU x y z x₁ i i₁) =
-- -- -- -- -- -- -- -- -- -- -- --         isSet→isSet' BSet
-- -- -- -- -- -- -- -- -- -- -- --           (λ i₂ → y ∷* comm* x z (f x₁) i₂)
-- -- -- -- -- -- -- -- -- -- -- --           (λ i₂ → hexDiag* x y z (f x₁) i₂)
-- -- -- -- -- -- -- -- -- -- -- --           (λ i₂ → comm* y x (z ∷* f x₁) i₂)
-- -- -- -- -- -- -- -- -- -- -- --           (λ i₂ → comm* y z (x ∷* f x₁) i₂)
-- -- -- -- -- -- -- -- -- -- -- --           i i₁
-- -- -- -- -- -- -- -- -- -- -- --     f (hexL x y z xs i i₁) =
-- -- -- -- -- -- -- -- -- -- -- --          isSet→isSet' BSet
-- -- -- -- -- -- -- -- -- -- -- --          (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- -- -- -- -- --          (comm* x z (y ∷* f xs))
-- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ → x ∷* comm* y z (f xs) i₁)
-- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ → z ∷* comm* y x (f xs) i₁)
-- -- -- -- -- -- -- -- -- -- -- --           i i₁
-- -- -- -- -- -- -- -- -- -- -- --     f (trunc x y p r g h i i₁ i₂) =
-- -- -- -- -- -- -- -- -- -- -- --       isSet→isGroupoid BSet _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- --        (λ i j → f (g i j)) (λ i j → f (h i j))
-- -- -- -- -- -- -- -- -- -- -- --          i i₁ i₂


-- -- -- -- -- -- -- -- -- -- -- --   module ElimSet {ℓ'} {B : FMSet2 → Type ℓ'}
-- -- -- -- -- -- -- -- -- -- -- --     ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2} → B xs → B (x ∷2 xs))
-- -- -- -- -- -- -- -- -- -- -- --     (comm* : (x y : A) {xs : FMSet2} (b : B xs)
-- -- -- -- -- -- -- -- -- -- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
-- -- -- -- -- -- -- -- -- -- -- --     (hexDiag* : (x y z : A) {xs : FMSet2} (b : B xs)
-- -- -- -- -- -- -- -- -- -- -- --            → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b))))
-- -- -- -- -- -- -- -- -- -- -- --     (trunc* : (xs : FMSet2) → isSet (B xs)) where

-- -- -- -- -- -- -- -- -- -- -- --     f : (xs : FMSet2) → B xs
-- -- -- -- -- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- -- -- -- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- -- -- -- -- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- -- -- -- -- -- --     f (comm-inv x y xs i j) =
-- -- -- -- -- -- -- -- -- -- -- --        isOfHLevel→isOfHLevelDep 2 trunc*
-- -- -- -- -- -- -- -- -- -- -- --            (x ∷* (y ∷* f xs)) (y ∷* (x ∷* f xs))
-- -- -- -- -- -- -- -- -- -- -- --            (comm* x y (f xs)) (symP (comm* y x (f xs)))
-- -- -- -- -- -- -- -- -- -- -- --            (comm-inv x y xs) i j
-- -- -- -- -- -- -- -- -- -- -- --     f (hexDiag x y z xs i) = hexDiag* x y z (f xs) i
-- -- -- -- -- -- -- -- -- -- -- --     f (hexU x y z xs i j) =
-- -- -- -- -- -- -- -- -- -- -- --       isSet→SquareP 
-- -- -- -- -- -- -- -- -- -- -- --          (λ i j → trunc* (hexU x y z xs i j))
-- -- -- -- -- -- -- -- -- -- -- --          (λ j → y ∷* comm* x z (f xs) j)
-- -- -- -- -- -- -- -- -- -- -- --          (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- -- -- -- -- --          (comm* y x (z ∷* f xs))
-- -- -- -- -- -- -- -- -- -- -- --          (comm* y z (x ∷* f xs)) i j
-- -- -- -- -- -- -- -- -- -- -- --     f (hexL x y z xs i j) =
-- -- -- -- -- -- -- -- -- -- -- --          isSet→SquareP 
-- -- -- -- -- -- -- -- -- -- -- --          (λ i j → trunc* (hexL x y z xs i j))
-- -- -- -- -- -- -- -- -- -- -- --          (hexDiag* x y z (f xs))
-- -- -- -- -- -- -- -- -- -- -- --          (comm* x z (y ∷* f xs))
-- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ → x ∷* comm* y z (f xs) i₁)
-- -- -- -- -- -- -- -- -- -- -- --          (λ i₁ → z ∷* comm* y x (f xs) i₁) i j
-- -- -- -- -- -- -- -- -- -- -- --     f (trunc xs zs p q r s i j k) =
-- -- -- -- -- -- -- -- -- -- -- --         isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (trunc* x))
-- -- -- -- -- -- -- -- -- -- -- --             _ _ _ _ (λ j k → f (r j k)) (λ j k → f (s j k)) (trunc xs zs p q r s) i j k

-- -- -- -- -- -- -- -- -- -- -- --   module ElimProp {ℓ'} {B : FMSet2 → Type ℓ'}
-- -- -- -- -- -- -- -- -- -- -- --     ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2} → B xs → B (x ∷2 xs))    
-- -- -- -- -- -- -- -- -- -- -- --     (trunc* : (xs : FMSet2) → isProp (B xs)) where

-- -- -- -- -- -- -- -- -- -- -- --     f : (xs : FMSet2) → B xs
-- -- -- -- -- -- -- -- -- -- -- --     f = ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- --           []*
-- -- -- -- -- -- -- -- -- -- -- --           _∷*_
-- -- -- -- -- -- -- -- -- -- -- --           (λ x y b → isProp→PathP (λ _ → trunc* _) _ _)
-- -- -- -- -- -- -- -- -- -- -- --           (λ x y z b → isProp→PathP (λ _ → trunc* _) _ _)
-- -- -- -- -- -- -- -- -- -- -- --           (isProp→isSet ∘ trunc*)


-- -- -- -- -- -- -- -- -- -- -- --   module Elim {ℓ'} {B : FMSet2 → Type ℓ'}
-- -- -- -- -- -- -- -- -- -- -- --     ([]* : B []) (_∷*_ : (x : A) {xs : FMSet2} → B xs → B (x ∷2 xs))
-- -- -- -- -- -- -- -- -- -- -- --     (comm* : (x y : A) {xs : FMSet2} (b : B xs)
-- -- -- -- -- -- -- -- -- -- -- --            → PathP (λ i → B (comm x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
-- -- -- -- -- -- -- -- -- -- -- --     (comm-inv* : ∀ x y {xs} (b : B xs) → SquareP (λ i j → B (comm-inv x y xs i j))
-- -- -- -- -- -- -- -- -- -- -- --                         (comm* x y b ) (symP (comm* y x b))
-- -- -- -- -- -- -- -- -- -- -- --                         refl refl )
-- -- -- -- -- -- -- -- -- -- -- --     (hexDiag* : (x y z : A) {xs : FMSet2} (b : B xs)
-- -- -- -- -- -- -- -- -- -- -- --            → PathP (λ i → B (hexDiag x y z xs i)) (x ∷* (y ∷* (z ∷* b))) (z ∷* (y ∷* (x ∷* b))))
-- -- -- -- -- -- -- -- -- -- -- --     (hexU* : ∀ x y z {xs : FMSet2} (b : B xs) →
-- -- -- -- -- -- -- -- -- -- -- --                SquareP
-- -- -- -- -- -- -- -- -- -- -- --                ((λ i j → B (hexU x y z xs i j)))
-- -- -- -- -- -- -- -- -- -- -- --                  (congP (λ _ → y ∷*_) (comm* x z b))
-- -- -- -- -- -- -- -- -- -- -- --                  (hexDiag* x y z b)
-- -- -- -- -- -- -- -- -- -- -- --                  (comm* _ _ (z ∷* b))
-- -- -- -- -- -- -- -- -- -- -- --                  (comm* _ _ (x ∷* b))
-- -- -- -- -- -- -- -- -- -- -- --                   )
-- -- -- -- -- -- -- -- -- -- -- --     (hexL* : ∀ x y z {xs : FMSet2} (b : B xs)  →
-- -- -- -- -- -- -- -- -- -- -- --                SquareP
-- -- -- -- -- -- -- -- -- -- -- --                  (λ i j → B (hexL x y z xs i j))
-- -- -- -- -- -- -- -- -- -- -- --                  (hexDiag* _ _ _ b)
-- -- -- -- -- -- -- -- -- -- -- --                  (comm* _ _ _)
-- -- -- -- -- -- -- -- -- -- -- --                  (congP (λ _ → _ ∷*_) (comm* _ _ _))
-- -- -- -- -- -- -- -- -- -- -- --                  (congP (λ _ → _ ∷*_) (comm* _ _ _))
-- -- -- -- -- -- -- -- -- -- -- --                   )

-- -- -- -- -- -- -- -- -- -- -- --     (trunc* : (xs : FMSet2) → isGroupoid (B xs)) where

-- -- -- -- -- -- -- -- -- -- -- --     f : (xs : FMSet2) → B xs
-- -- -- -- -- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- -- -- -- -- --     f (x ∷2 xs) = x ∷* f xs
-- -- -- -- -- -- -- -- -- -- -- --     f (comm x y xs i) = comm* x y (f xs) i
-- -- -- -- -- -- -- -- -- -- -- --     f (comm-inv x y xs i j) =
-- -- -- -- -- -- -- -- -- -- -- --        comm-inv* x y (f xs) i j
-- -- -- -- -- -- -- -- -- -- -- --     f (hexDiag x y z xs i) = hexDiag* x y z (f xs) i
-- -- -- -- -- -- -- -- -- -- -- --     f (hexU x y z xs i j) = hexU* x y z (f xs) i j
-- -- -- -- -- -- -- -- -- -- -- --     f (hexL x y z xs i j) = hexL* x y z (f xs) i j

-- -- -- -- -- -- -- -- -- -- -- --     f (trunc xs ys p q r s i j k) =
-- -- -- -- -- -- -- -- -- -- -- --       isOfHLevel→isOfHLevelDep 3 (λ a → trunc* a)
-- -- -- -- -- -- -- -- -- -- -- --          _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- --          (λ j k → f (r j k)) (λ j k → f (s j k)) 
-- -- -- -- -- -- -- -- -- -- -- --            (trunc xs ys p q r s) i j k


-- -- -- -- -- -- -- -- -- -- -- --   module Rec {ℓ'} {B : Type ℓ'} (BType : isGroupoid B)
-- -- -- -- -- -- -- -- -- -- -- --     ([]* : B) (_∷*_ : A → B → B)
-- -- -- -- -- -- -- -- -- -- -- --     (comm* : (x y : A) (b : B) → x ∷* (y ∷* b) ≡ y ∷* (x ∷* b))
-- -- -- -- -- -- -- -- -- -- -- --     (comm-inv* : ∀ x y b → comm* x y b ≡ sym (comm* y x b) )
-- -- -- -- -- -- -- -- -- -- -- --     (hexDiag* : ∀ x y z b → x ∷* (y ∷* (z ∷* b)) ≡ z ∷* (y ∷* (x ∷* b)) )
-- -- -- -- -- -- -- -- -- -- -- --     (hexU* : ∀ x y z b →
-- -- -- -- -- -- -- -- -- -- -- --                Square (cong (_ ∷*_) (comm* _ _ b)) (hexDiag* x y z b)
-- -- -- -- -- -- -- -- -- -- -- --                       (comm* _ _ _) (comm* _ _ _))
-- -- -- -- -- -- -- -- -- -- -- --     (hexL* : ∀ x y z b →
-- -- -- -- -- -- -- -- -- -- -- --                Square (hexDiag* x y z b) (comm* _ _ _)
-- -- -- -- -- -- -- -- -- -- -- --                       (cong (_ ∷*_) (comm* _ _ b)) (cong (_ ∷*_) (comm* _ _ b)))

-- -- -- -- -- -- -- -- -- -- -- --     where

-- -- -- -- -- -- -- -- -- -- -- --     f : FMSet2 → B
-- -- -- -- -- -- -- -- -- -- -- --     f [] = []*
-- -- -- -- -- -- -- -- -- -- -- --     f (x ∷2 x₁) = x ∷* f x₁
-- -- -- -- -- -- -- -- -- -- -- --     f (comm x y x₁ i) = comm* x y (f x₁) i
-- -- -- -- -- -- -- -- -- -- -- --     f (comm-inv x y x₁ i i₁) = comm-inv* x y (f x₁) i i₁
-- -- -- -- -- -- -- -- -- -- -- --     f (hexDiag x y z x₁ i) = hexDiag* x y z (f x₁) i
-- -- -- -- -- -- -- -- -- -- -- --     f (hexU x y z x₁ i i₁) = hexU* x y z (f x₁) i i₁
-- -- -- -- -- -- -- -- -- -- -- --     f (hexL x y z x₁ i i₁) = hexL* x y z (f x₁) i i₁
-- -- -- -- -- -- -- -- -- -- -- --     f (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- -- -- -- -- -- -- -- -- -- -- --        BType _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- --         (cong (cong f) x₃) (cong  (cong f) y₁) i i₁ x₄

-- -- -- -- -- -- -- -- -- -- -- --   len2 : FMSet2 → ℕ
-- -- -- -- -- -- -- -- -- -- -- --   len2 = RecSet.f isSetℕ zero (λ _ → suc) (λ _ _ _ → refl) (λ _ _ _ _ → refl)

-- -- -- -- -- -- -- -- -- -- -- --   open import Cubical.HITs.EilenbergMacLane1 as EM

  
-- -- -- -- -- -- -- -- -- -- -- --   open import Cubical.Data.List.FinData

-- -- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen : ℕ → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen n = Σ FMSet2 λ x → len2 x ≡ n

-- -- -- -- -- -- -- -- -- -- -- --   isSetLofLA : ∀ n → isSet (ListOfLen A n)
-- -- -- -- -- -- -- -- -- -- -- --   isSetLofLA n = isOfHLevelListOfLen 0 isSetA n 

-- -- -- -- -- -- -- -- -- -- -- --   isGroupoidFMSet2OfLen : ∀ n → isGroupoid (FMSet2OfLen n)
-- -- -- -- -- -- -- -- -- -- -- --   isGroupoidFMSet2OfLen n = 
-- -- -- -- -- -- -- -- -- -- -- --     (isOfHLevelΣ 3 trunc λ _ → isSet→isGroupoid (isProp→isSet (isSetℕ _ _)))

-- -- -- -- -- -- -- -- -- -- -- --   open import Cubical.HITs.GroupoidQuotients as GQ renaming ([_] to [_]//)

-- -- -- -- -- -- -- -- -- -- -- --   ListOfLen→FMSet2OfLen : ∀ n → ListOfLen A n → FMSet2OfLen n
-- -- -- -- -- -- -- -- -- -- -- --   ListOfLen→FMSet2OfLen zero x = [] , refl
-- -- -- -- -- -- -- -- -- -- -- --   ListOfLen→FMSet2OfLen (suc n) ([] , snd₁) = ⊥.rec (ℕznots snd₁)
-- -- -- -- -- -- -- -- -- -- -- --   ListOfLen→FMSet2OfLen (suc n) (x ∷ xs , p) =
-- -- -- -- -- -- -- -- -- -- -- --     let (xs' , p') = ListOfLen→FMSet2OfLen n (xs , injSuc p)
-- -- -- -- -- -- -- -- -- -- -- --     in x ∷2 xs' , cong suc p' 


-- -- -- -- -- -- -- -- -- -- -- --   transposeHeadFM2 : (x : FMSet2) → singl x 
-- -- -- -- -- -- -- -- -- -- -- --   transposeHeadFM2 = ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- --     ([] , refl)
-- -- -- -- -- -- -- -- -- -- -- --     (λ x {xs} → ElimSet.f {B = λ xs → singl xs → singl (x ∷2 xs)}
-- -- -- -- -- -- -- -- -- -- -- --        (λ _ → _ , refl)
-- -- -- -- -- -- -- -- -- -- -- --        (λ y {xs} _ _ → (y ∷2 x ∷2 xs) , (comm x y xs))
-- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ → isProp→PathP (λ _ → isPropΠ λ _ → isPropSingl) _ _)
-- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ _ → isProp→PathP (λ _ → isPropΠ λ _ → isPropSingl) _ _)
-- -- -- -- -- -- -- -- -- -- -- --        (λ _ → isSetΠ λ _ → isProp→isSet (isPropSingl)) xs)
-- -- -- -- -- -- -- -- -- -- -- --     (λ _ _ _ → isProp→PathP (λ _ → isPropSingl) _ _)
-- -- -- -- -- -- -- -- -- -- -- --     (λ _ _ _ _ → isProp→PathP (λ _ → isPropSingl) _ _)
-- -- -- -- -- -- -- -- -- -- -- --     λ _ → isProp→isSet isPropSingl

-- -- -- -- -- -- -- -- -- -- -- --   transposeFM2 : (x : FMSet2) → Fin (len2 x) → singl x 
-- -- -- -- -- -- -- -- -- -- -- --   transposeFM2 = ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- --      (λ _ → [] , refl)
-- -- -- -- -- -- -- -- -- -- -- --      (λ x {xs} → ElimSet.f {B = λ xs → (Fin (len2 xs) → singl xs) → Fin (suc (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- --                   →  singl (x ∷2 xs)}
-- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ → _ , refl)
-- -- -- -- -- -- -- -- -- -- -- --        (λ y {xs} _ g → λ {zero → (y ∷2 x ∷2 xs) , (comm x y xs)
-- -- -- -- -- -- -- -- -- -- -- --                        ; (suc k) → _ , cong (x ∷2_) (snd (g k)) })
-- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ → isProp→PathP (λ _ → isPropΠ2 λ _ _ → isPropSingl) _ _)
-- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ _ → isProp→PathP (λ _ → isPropΠ2 λ _ _ → isPropSingl) _ _)
-- -- -- -- -- -- -- -- -- -- -- --        (λ _ → isSetΠ2 λ _ _ → isProp→isSet (isPropSingl))
-- -- -- -- -- -- -- -- -- -- -- --        xs)
-- -- -- -- -- -- -- -- -- -- -- --     (λ _ _ _ → isProp→PathP (λ _ → isPropΠ λ _ → isPropSingl) _ _)
-- -- -- -- -- -- -- -- -- -- -- --     (λ _ _ _ _ → isProp→PathP (λ _ → isPropΠ λ _ →  isPropSingl) _ _)
-- -- -- -- -- -- -- -- -- -- -- --      λ _ → isSetΠ λ _ → isProp→isSet isPropSingl 


-- -- -- -- -- -- -- -- -- -- -- --   -- singlToSingl≃ : ((x : FMSet2) → singl x) →
-- -- -- -- -- -- -- -- -- -- -- --   --   ∀ n → singl (idEquiv (FMSet2OfLen (suc n)))
-- -- -- -- -- -- -- -- -- -- -- --   -- singlToSingl≃ x n =
-- -- -- -- -- -- -- -- -- -- -- --   --   ((λ (y , p ) → ((fst ∘ x) y) ,
-- -- -- -- -- -- -- -- -- -- -- --   --    (sym (cong len2 ((snd ∘ x) y)) ∙ p)) ,
-- -- -- -- -- -- -- -- -- -- -- --   --    {!!}) , equivEq (funExt λ x' → Σ≡Prop (λ _ → isSetℕ _ _)
-- -- -- -- -- -- -- -- -- -- -- --   --      (snd (x (fst x'))))

-- -- -- -- -- -- -- -- -- -- -- --   transposeFM2≃ : ∀ n → Fin n → singl (idEquiv (FMSet2OfLen n))
-- -- -- -- -- -- -- -- -- -- -- --   fst (fst (transposeFM2≃ n k)) (l , p) =
-- -- -- -- -- -- -- -- -- -- -- --     let (l' , p') = transposeFM2 l (subst Fin (sym p) k)
-- -- -- -- -- -- -- -- -- -- -- --     in l' , (cong len2 (sym p')  ∙  p)
-- -- -- -- -- -- -- -- -- -- -- --   snd (fst (transposeFM2≃ n k)) = subst isEquiv
-- -- -- -- -- -- -- -- -- -- -- --     (funExt (λ (l , p) → Σ≡Prop (λ _ → isSetℕ _ _)
-- -- -- -- -- -- -- -- -- -- -- --       (snd (transposeFM2 l (subst Fin (sym p) k)))))
-- -- -- -- -- -- -- -- -- -- -- --     (idIsEquiv (FMSet2OfLen n))

-- -- -- -- -- -- -- -- -- -- -- --   snd (transposeFM2≃ n k) = equivEq (funExt (λ (l , p) → Σ≡Prop (λ _ → isSetℕ _ _)
-- -- -- -- -- -- -- -- -- -- -- --       (snd (transposeFM2 l (subst Fin (sym p) k)))))
  


-- -- -- -- -- -- -- -- -- -- -- --   transposeFM2Rels : ∀ n → (ix : PermR' n)
-- -- -- -- -- -- -- -- -- -- -- --      → (foldr
-- -- -- -- -- -- -- -- -- -- -- --       (GroupStr._·_ (idEquivsG (FMSet2OfLen (suc n)) .snd) ∘
-- -- -- -- -- -- -- -- -- -- -- --        ⊎.elim (λ x → transposeFM2≃ (suc n) (weakenFin x))
-- -- -- -- -- -- -- -- -- -- -- --        (λ y →
-- -- -- -- -- -- -- -- -- -- -- --           GroupStr.inv (idEquivsG (FMSet2OfLen (suc n)) .snd)
-- -- -- -- -- -- -- -- -- -- -- --           (transposeFM2≃ (suc n) (weakenFin y))))
-- -- -- -- -- -- -- -- -- -- -- --       (transposeFM2≃ (suc n) (weakenFin (snd (relatorPerm (suc n) ix))))
-- -- -- -- -- -- -- -- -- -- -- --       (fst (relatorPerm (suc n) ix))
-- -- -- -- -- -- -- -- -- -- -- --       ≡ GroupStr.1g (idEquivsG (FMSet2OfLen (suc n)) .snd))
-- -- -- -- -- -- -- -- -- -- -- --   transposeFM2Rels _ _ = isPropSingl _ _
-- -- -- -- -- -- -- -- -- -- -- --   -- transposeFM2Rels .(k + suc _) (zero {.(suc _)} {k} invo) =
-- -- -- -- -- -- -- -- -- -- -- --   --  ΣPathP ((equivEq {!!}) , {!!})
-- -- -- -- -- -- -- -- -- -- -- --   -- transposeFM2Rels .(k + suc (suc _)) (zero {.(suc (suc _))} {k} braid) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- transposeFM2Rels .(k + suc (suc _)) (zero {.(suc (suc _))} {k} (comm x)) = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   ww : ∀ n → GroupHom (Perm (suc n))
-- -- -- -- -- -- -- -- -- -- -- --                  (idEquivsG (FMSet2OfLen (suc n)))
-- -- -- -- -- -- -- -- -- -- -- --   ww n = toConst≃ (Fin (n)) _ (relatorPerm (suc n))
-- -- -- -- -- -- -- -- -- -- -- --         (FMSet2OfLen (suc n))
-- -- -- -- -- -- -- -- -- -- -- --         (Eli n)
-- -- -- -- -- -- -- -- -- -- -- --         (transposeFM2≃ (suc n) ∘ weakenFin)
-- -- -- -- -- -- -- -- -- -- -- --         (transposeFM2Rels n)

-- -- -- -- -- -- -- -- -- -- -- --   open import Cubical.Data.FinData.GTrun



-- -- -- -- -- -- -- -- -- -- -- --   module tryList where

-- -- -- -- -- -- -- -- -- -- -- --     -- fromFM : FMSet2 → List//↔ A
-- -- -- -- -- -- -- -- -- -- -- --     -- fromFM =
-- -- -- -- -- -- -- -- -- -- -- --     --   Rec.f
-- -- -- -- -- -- -- -- -- -- -- --     --     squash//
-- -- -- -- -- -- -- -- -- -- -- --     --     [ [] ]//
-- -- -- -- -- -- -- -- -- -- -- --     --     _∷//_
-- -- -- -- -- -- -- -- -- -- -- --     --     (λ x y → GQ.elimSet
-- -- -- -- -- -- -- -- -- -- -- --     --       isTrans↔
-- -- -- -- -- -- -- -- -- -- -- --     --       (λ _ → squash// _ _)
-- -- -- -- -- -- -- -- -- -- -- --     --       (λ _ → eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- --     --       (λ {a} {b} r i j → h x y {a} {b} r j i))
-- -- -- -- -- -- -- -- -- -- -- --     --     (λ x y → GQ.elimProp _ (λ _ → squash// _ _ _ _)
-- -- -- -- -- -- -- -- -- -- -- --     --               (hSym x y ))
-- -- -- -- -- -- -- -- -- -- -- --     --     (λ x y z → GQ.elimSet
-- -- -- -- -- -- -- -- -- -- -- --     --       isTrans↔
-- -- -- -- -- -- -- -- -- -- -- --     --       (λ _ → squash// _ _)
-- -- -- -- -- -- -- -- -- -- -- --     --       (λ _ → eq// overSecondSwap↔)
-- -- -- -- -- -- -- -- -- -- -- --     --       {!!})
-- -- -- -- -- -- -- -- -- -- -- --     --     {!!}
-- -- -- -- -- -- -- -- -- -- -- --     --     {!!}

-- -- -- -- -- -- -- -- -- -- -- --     --      where

-- -- -- -- -- -- -- -- -- -- -- --     --        h'' : ∀ x y → {a b : List A} (r : a ↔ b) →
-- -- -- -- -- -- -- -- -- -- -- --     --                   (λ i → (y ∷// (x ∷// eq// {a = a} {b} r i)))
-- -- -- -- -- -- -- -- -- -- -- --     --                 ≡ eq// (y ∷↔ (x ∷↔ r))
-- -- -- -- -- -- -- -- -- -- -- --     --        h'' x y r =
-- -- -- -- -- -- -- -- -- -- -- --     --             cong eq// (cong₂ prm refl 
-- -- -- -- -- -- -- -- -- -- -- --     --             (funExt λ { zero → refl ; one → refl ; (suc (suc k)) → refl }))


-- -- -- -- -- -- -- -- -- -- -- --     --        h' : ∀ x y → {a b : List A} (r : a ↔ b) → Path (Path (List//↔ A) _ _)
-- -- -- -- -- -- -- -- -- -- -- --     --                ((eq// (x ∷↔ (y ∷↔ r))) ∙ eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- --     --                (eq// headSwap↔ ∙ (eq// (y ∷↔ (x ∷↔ r))))
-- -- -- -- -- -- -- -- -- -- -- --     --        h' x y r = sym (comp'// _ _ _ _) ∙∙
-- -- -- -- -- -- -- -- -- -- -- --     --                    cong eq// (cong₂ prm
-- -- -- -- -- -- -- -- -- -- -- --     --                      (equivEq (funExt λ { zero → refl ; one → refl ; (suc (suc k)) → refl }))
-- -- -- -- -- -- -- -- -- -- -- --     --                      ( (funExt λ { zero → refl ; one → refl
-- -- -- -- -- -- -- -- -- -- -- --     --                        ; (suc (suc k)) → sym (leftright refl _) })))
-- -- -- -- -- -- -- -- -- -- -- --     --                   ∙∙  comp'// _ _ _ _ 

-- -- -- -- -- -- -- -- -- -- -- --     --        h : ∀ x y → {a b : List A} (r : a ↔ b) →
-- -- -- -- -- -- -- -- -- -- -- --     --                Square
-- -- -- -- -- -- -- -- -- -- -- --     --                (λ i → (x ∷// (y ∷// eq// r i)))
-- -- -- -- -- -- -- -- -- -- -- --     --                (λ i → (y ∷// (x ∷// eq// r i)))
-- -- -- -- -- -- -- -- -- -- -- --     --                (eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- --     --                (eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- --     --        h x y r =
-- -- -- -- -- -- -- -- -- -- -- --     --             (h'' y x r) ◁ doubleCompPath-filler (sym (eq// headSwap↔)) _
-- -- -- -- -- -- -- -- -- -- -- --     --                     (eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- --     --            ▷ (doubleCompPath-elim (sym (eq// headSwap↔)) _ _ ∙ sym (GL.assoc _ _ _) ∙ 
-- -- -- -- -- -- -- -- -- -- -- --     --              (cong ((sym (eq// headSwap↔)) ∙_) (h' x y r) ∙ GL.assoc _ _ _ ∙
-- -- -- -- -- -- -- -- -- -- -- --     --                 cong (_∙ (eq// (y ∷↔ (x ∷↔ r)))) (lCancel (eq// headSwap↔)) ∙ sym (lUnit _))
-- -- -- -- -- -- -- -- -- -- -- --     --                  ∙ sym (h'' x y r))

-- -- -- -- -- -- -- -- -- -- -- --     --        hSym : ∀ x y → (a : List A) → 
-- -- -- -- -- -- -- -- -- -- -- --     --                  eq// (headSwap↔ {x = x} {y = y} {a})
-- -- -- -- -- -- -- -- -- -- -- --     --                    ≡ sym (eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- --     --        hSym x y a = invEq (compr≡Equiv _ _ _)
-- -- -- -- -- -- -- -- -- -- -- --     --                        ((sym (comp'// _ _ _ headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- --     --              ∙ cong eq// (cong₂ prm (equivEq (funExt (secEq swap0and1≃)))
-- -- -- -- -- -- -- -- -- -- -- --     --                 (funExt λ { zero → sym compPathRefl
-- -- -- -- -- -- -- -- -- -- -- --     --                           ; one → sym compPathRefl
-- -- -- -- -- -- -- -- -- -- -- --     --                           ; (suc (suc x)) → sym compPathRefl }))
-- -- -- -- -- -- -- -- -- -- -- --     --              ∙ ↔→FMSet2≡Refl _ )
-- -- -- -- -- -- -- -- -- -- -- --     --           ∙ sym (lCancel _))


-- -- -- -- -- -- -- -- -- -- -- --     -- to//-len : (x : FMSet2) → length// (fromFM x) ≡ len2 x
-- -- -- -- -- -- -- -- -- -- -- --     -- to//-len = ElimProp.f
-- -- -- -- -- -- -- -- -- -- -- --     --   refl
-- -- -- -- -- -- -- -- -- -- -- --     --   (λ x {xs} p → length//-∷// x (fromFM xs) ∙  cong suc p)
-- -- -- -- -- -- -- -- -- -- -- --     --   λ _ → isSetℕ _ _
    
-- -- -- -- -- -- -- -- -- -- -- --     -- to// : ∀ n → FMSet2OfLen n → ListOfLen// A n
-- -- -- -- -- -- -- -- -- -- -- --     -- to// n = uncurry
-- -- -- -- -- -- -- -- -- -- -- --     --   λ x p → (fromFM x) , to//-len x ∙ p

-- -- -- -- -- -- -- -- -- -- -- --     prm≡Si : ∀ n → (e : Fin n ≃ Fin n) → singl (ListOfLen→FMSet2OfLen n)
-- -- -- -- -- -- -- -- -- -- -- --     prm≡Si = {!!}

-- -- -- -- -- -- -- -- -- -- -- --     -- prm≡SiComp : ∀ n → (e f : Fin n ≃ Fin n) → singl (ListOfLen→FMSet2OfLen n)
-- -- -- -- -- -- -- -- -- -- -- --     -- prm≡SiComp = {!!}


-- -- -- -- -- -- -- -- -- -- -- --     prm≡ : ∀ n → (e : Fin n ≃ Fin n) → (a : List A) → (p : _) → (p' : _)
-- -- -- -- -- -- -- -- -- -- -- --       → fst (curry (ListOfLen→FMSet2OfLen n) a p) ≡
-- -- -- -- -- -- -- -- -- -- -- --        fst (curry (ListOfLen→FMSet2OfLen n) (permute a (e ∙ₑ ≡→Fin≃ (sym p))) p')
-- -- -- -- -- -- -- -- -- -- -- --     prm≡ = {!!}
    
-- -- -- -- -- -- -- -- -- -- -- --     from// : ∀ n → ListOfLen// A n → FMSet2OfLen n
-- -- -- -- -- -- -- -- -- -- -- --     from// n = uncurry
-- -- -- -- -- -- -- -- -- -- -- --        (GQ.elim isTrans↔
-- -- -- -- -- -- -- -- -- -- -- --         (λ _ → isGroupoidΠ λ _ → isGroupoidFMSet2OfLen n)
-- -- -- -- -- -- -- -- -- -- -- --          (curry (ListOfLen→FMSet2OfLen n))
-- -- -- -- -- -- -- -- -- -- -- --           (λ {a} {b} (prm e p) →
-- -- -- -- -- -- -- -- -- -- -- --             funExtDep λ {x₀} {x₁} p₁ →
-- -- -- -- -- -- -- -- -- -- -- --               funExt⁻ (funExt⁻ (cong curry (snd (prm≡Si n
-- -- -- -- -- -- -- -- -- -- -- --                 (≡→Fin≃ (sym x₀) ∙ₑ e ∙ₑ ≡→Fin≃ x₁ )))) a) x₀ ∙
-- -- -- -- -- -- -- -- -- -- -- --                  {!!} )
-- -- -- -- -- -- -- -- -- -- -- --            -- (λ {a} {b}
-- -- -- -- -- -- -- -- -- -- -- --            --   (prm e p) →
-- -- -- -- -- -- -- -- -- -- -- --               -- funExt⁻ (cong curry (snd (prm≡Si n
-- -- -- -- -- -- -- -- -- -- -- --               --   (≡→Fin≃ {!!} ∙ₑ e ∙ₑ ≡→Fin≃ {!!} )))) a
-- -- -- -- -- -- -- -- -- -- -- --            --     ◁ {!!})
-- -- -- -- -- -- -- -- -- -- -- --             {!!})
-- -- -- -- -- -- -- -- -- -- -- --              -- λ {a} {b} {c} r s _ → {!compPath-filler _ _ ▷ ?!})
-- -- -- -- -- -- -- -- -- -- -- --        where
-- -- -- -- -- -- -- -- -- -- -- --          zz : {!!}
-- -- -- -- -- -- -- -- -- -- -- --          zz = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     -- iso// : ∀ n → Iso (ListOfLen// A n) (FMSet2OfLen n)
-- -- -- -- -- -- -- -- -- -- -- --     -- Iso.fun (iso// n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     -- Iso.inv (iso// n) = to// n
-- -- -- -- -- -- -- -- -- -- -- --     -- Iso.rightInv (iso// n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --     -- Iso.leftInv (iso// n) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   module tryFun where
-- -- -- -- -- -- -- -- -- -- -- -- --     RRperm : ∀ n → (g : ⟨ Perm (suc n) ⟩) →
-- -- -- -- -- -- -- -- -- -- -- -- --                {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     RRperm n = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- flip (uncurry (ind' (⊥.rec ∘ ℕznots)
-- -- -- -- -- -- -- -- -- -- -- -- --     --   (ind' (λ _ p k → {!k!})
-- -- -- -- -- -- -- -- -- -- -- -- --     --     {!!})))



-- -- -- -- -- -- -- -- -- -- -- -- --     -- RRperm' : ∀ n → (g : ⟨ Perm (suc n) ⟩)   
-- -- -- -- -- -- -- -- -- -- -- -- --     --       (a : ListOfLen A (suc n)) →
-- -- -- -- -- -- -- -- -- -- -- -- --     --          ListOfLen→FMSet2OfLen (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- --     --          (fst (ListOfLenSymHom isSetA n) g .fst a)
-- -- -- -- -- -- -- -- -- -- -- -- --     --          ≡
-- -- -- -- -- -- -- -- -- -- -- -- --     --          recEMtrunc.bE (isSetLofLA (suc n)) (ListOfLenSymHom isSetA n)
-- -- -- -- -- -- -- -- -- -- -- -- --     --          (isGroupoidFMSet2OfLen (suc n)) (ListOfLen→FMSet2OfLen (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --     --          (RRperm n) (ww n) g (ListOfLen→FMSet2OfLen (suc n) a)
-- -- -- -- -- -- -- -- -- -- -- -- --     -- RRperm' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --     -- RRperm'' : ∀ n → (g : ⟨ Perm (suc n) ⟩) → (a : ListOfLen A (suc n)) →
-- -- -- -- -- -- -- -- -- -- -- -- --     --     recEMtrunc.p* (isSetLofLA (suc n)) (ListOfLenSymHom isSetA n)
-- -- -- -- -- -- -- -- -- -- -- -- --     --     (isGroupoidFMSet2OfLen (suc n)) (ListOfLen→FMSet2OfLen (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --     --     (RRperm n) (ww n) g (ListOfLen→FMSet2OfLen (suc n) a)
-- -- -- -- -- -- -- -- -- -- -- -- --     --     ∙ sym (RRperm' n g a)
-- -- -- -- -- -- -- -- -- -- -- -- --     --     ≡ RRperm n g a
-- -- -- -- -- -- -- -- -- -- -- -- --     -- RRperm'' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --     -- RRpermSq : ∀ n → (g h : ⟨ Perm (suc n) ⟩) →
-- -- -- -- -- -- -- -- -- -- -- -- --     --                {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- RRpermSq = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --     tabulateFM2OfLen : ∀ n → (Fin n → A) → FMSet2OfLen n
-- -- -- -- -- -- -- -- -- -- -- -- --     tabulateFM2OfLen zero _ = [] , refl 
-- -- -- -- -- -- -- -- -- -- -- -- --     tabulateFM2OfLen (suc n) f =
-- -- -- -- -- -- -- -- -- -- -- -- --       let (x , p) = tabulateFM2OfLen n (f ∘ suc)
-- -- -- -- -- -- -- -- -- -- -- -- --       in (f zero) ∷2 x , cong suc p

-- -- -- -- -- -- -- -- -- -- -- -- --     permuteFM2Hom : ∀ n → GroupHom
-- -- -- -- -- -- -- -- -- -- -- -- --         (SymData (suc n)) 
-- -- -- -- -- -- -- -- -- -- -- -- --         (idEquivsG (FMSet2OfLen (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- --     fst (permuteFM2Hom n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     snd (permuteFM2Hom n) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --     -- module _ (n : ℕ) where

-- -- -- -- -- -- -- -- -- -- -- -- --     --   module RR = recEMtrunc.Rec (isSet→ {A = Fin (suc n)} isSetA)
-- -- -- -- -- -- -- -- -- -- -- -- --     --         (SymmetricGroup→Hom isSetA )
-- -- -- -- -- -- -- -- -- -- -- -- --     --         (isGroupoidFMSet2OfLen (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --     --         (tabulateFM2OfLen (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --     --         {!!} {!!} {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     --         -- (RRperm n) (ww n) (RRperm' n) (RRperm'' n)


-- -- -- -- -- -- -- -- -- -- -- -- --   -- module tryPerm where
-- -- -- -- -- -- -- -- -- -- -- -- --   --   RRperm : ∀ n → (g : ⟨ Perm (suc n) ⟩) →
-- -- -- -- -- -- -- -- -- -- -- -- --   --              (a : ListOfLen A (suc n)) →
-- -- -- -- -- -- -- -- -- -- -- -- --   --                ListOfLen→FMSet2OfLen (suc n) a ≡
-- -- -- -- -- -- -- -- -- -- -- -- --   --                ListOfLen→FMSet2OfLen (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- --   --                (fst (ListOfLenSymHom isSetA n) g .fst a)
-- -- -- -- -- -- -- -- -- -- -- -- --   --   RRperm n = flip (uncurry (ind' (⊥.rec ∘ ℕznots)
-- -- -- -- -- -- -- -- -- -- -- -- --   --     (ind' (λ _ p k → {!k!})
-- -- -- -- -- -- -- -- -- -- -- -- --   --       {!!})))



-- -- -- -- -- -- -- -- -- -- -- -- --   --   RRperm' : ∀ n → (g : ⟨ Perm (suc n) ⟩) 
-- -- -- -- -- -- -- -- -- -- -- -- --   --         (a : ListOfLen A (suc n)) →
-- -- -- -- -- -- -- -- -- -- -- -- --   --            ListOfLen→FMSet2OfLen (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- --   --            (fst (ListOfLenSymHom isSetA n) g .fst a)
-- -- -- -- -- -- -- -- -- -- -- -- --   --            ≡
-- -- -- -- -- -- -- -- -- -- -- -- --   --            recEMtrunc.bE (isSetLofLA (suc n)) (ListOfLenSymHom isSetA n)
-- -- -- -- -- -- -- -- -- -- -- -- --   --            (isGroupoidFMSet2OfLen (suc n)) (ListOfLen→FMSet2OfLen (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --   --            (RRperm n) (ww n) g (ListOfLen→FMSet2OfLen (suc n) a)
-- -- -- -- -- -- -- -- -- -- -- -- --   --   RRperm' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   --   RRperm'' : ∀ n → (g : ⟨ Perm (suc n) ⟩) → (a : ListOfLen A (suc n)) →
-- -- -- -- -- -- -- -- -- -- -- -- --   --       recEMtrunc.p* (isSetLofLA (suc n)) (ListOfLenSymHom isSetA n)
-- -- -- -- -- -- -- -- -- -- -- -- --   --       (isGroupoidFMSet2OfLen (suc n)) (ListOfLen→FMSet2OfLen (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --   --       (RRperm n) (ww n) g (ListOfLen→FMSet2OfLen (suc n) a)
-- -- -- -- -- -- -- -- -- -- -- -- --   --       ∙ sym (RRperm' n g a)
-- -- -- -- -- -- -- -- -- -- -- -- --   --       ≡ RRperm n g a
-- -- -- -- -- -- -- -- -- -- -- -- --   --   RRperm'' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   --   RRpermSq : ∀ n → (g h : ⟨ Perm (suc n) ⟩) →
-- -- -- -- -- -- -- -- -- -- -- -- --   --                  {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --   --   RRpermSq = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   --   module _ (n : ℕ) where

-- -- -- -- -- -- -- -- -- -- -- -- --   --     module RR = recEMtrunc.Rec (isSetLofLA (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --   --           (ListOfLenSymHom isSetA n)
-- -- -- -- -- -- -- -- -- -- -- -- --   --           (isGroupoidFMSet2OfLen (suc n)) (ListOfLen→FMSet2OfLen (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- --   --           (RRperm n) (ww n) (RRperm' n) (RRperm'' n)


-- -- -- -- -- -- -- -- -- -- -- -- -- --           -- (RRperm n) {!!} {!!} {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ZZZ : ∀ n → ListOfLen// A (suc n) → EMtrunc (isSetLofLA (suc n)) ((ListOfLenSymHom isSetA n))  
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ZZZ n = uncurry
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (GQ.elim {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (λ a y → embase , a , y)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (λ r i y → (emloop {!!} i) , {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!})


-- -- -- -- -- -- -- -- -- -- -- -- -- --  -- EMG (isSetLofLA (suc n)) {!ListOfLenSymHom (suc n)!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- FMSet2OfLenHom : ∀ {ℓ} → ∀ n →
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --    GroupHom (Perm (suc n)) (Symmetric-Group (FMSet2OfLen (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (isOfHLevelListOfLen 0 isSetA (suc n)))

-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLenSi : ∀ n → ∀ g → (l : ListOfLen A (suc n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --      singl (ListOfLen→FMSet2OfLen (suc n) l)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLenSi = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen : ∀ n → ∀ g → (l : ListOfLen A (suc n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (ListOfLen→FMSet2OfLen (suc n) l) ≡ 
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (ListOfLen→FMSet2OfLen (suc n) (fst ((fst (ListOfLenSymHom isSetA n) g)) l))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n (η x) l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n (g · g₁) l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n ε l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n (inv g) l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n (PresentedGroup.assoc g g₁ g₂ i) l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n (idr g i) l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n (idl g i) l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n (invr g i) l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n (invl g i) l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n (rel ix i) l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- loopFMSet2OfLen n (trunc g g₁ x y i i₁) l = {!!}
  


-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- IsoEM : ∀ n → (isSetA : isSet A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso (EMtrunc _ (isOfHLevelListOfLen 0 isSetA (suc n)) (Perm (suc n)) (ListOfLenSymHom isSetA n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (FMSet2OfLen (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- IsoEM zero isSetA = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- IsoEM one isSetA = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- IsoEM (suc (suc n)) isSetA = w
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w : Iso {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (FMSet2OfLen (suc (suc (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --     Iso.fun w = uncurry (EM.elim
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --       _ (λ _ → isGroupoidΠ λ _ → isOfHLevelΣ 3 trunc {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --         ({!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --         {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --         {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --     Iso.inv w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --     Iso.rightInv w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --     Iso.leftInv w = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 : (x : FMSet2) → Fin (predℕ (len2 x)) → FMSet2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (x ∷2 x₂ ∷2 x₃) zero = (x₂ ∷2 x ∷2 x₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (x ∷2 x₂ ∷2 x₃) (suc x₁) = x ∷2 permFM2 (x₂ ∷2 x₃) x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (x ∷2 comm x₂ y x₃ i) zero = hexDiag x₂ x y x₃ i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (x ∷2 comm x₂ y x₃ i) (suc x₁) = x ∷2 (permFM2 (comm x₂ y x₃ i) x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (x ∷2 comm-inv x₂ y x₃ i i₁) x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (x ∷2 hexDiag x₂ y z x₃ i) x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (x ∷2 hexU x₂ y z x₃ i i₁) x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (x ∷2 hexL x₂ y z x₃ i i₁) x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (x ∷2 trunc x₂ x₃ x₄ y x₅ y₁ i i₁ x₆) x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (comm x y x₂ i) x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (comm-inv x y x₂ i i₁) x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (hexDiag x y z x₂ i) x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (hexU x y z x₂ i i₁) x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (hexL x y z x₂ i i₁) x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 (trunc x x₂ x₃ y x₄ y₁ i i₁ x₅) x₁ = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isoELM : (x : FMSet2) → (EM₁ (Perm (len2 x))) → singl x 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isoELM x embase = x , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isoELM x (emloop x₁ i) = {!permFM2 x₁!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isoELM x (emcomp g h j i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isoELM x (emsquash x₁ x₂ p q r s i i₁ i₂) = {!!}


  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 : (x : FMSet2) → Fin (predℕ (len2 x)) → (x ≡ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- permFM2 = ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (λ ())
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (λ a {xs} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      ElimSet.f {B = λ xs → (Fin (predℕ (len2 xs)) → xs ≡ xs) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              (RecSet.f isSetℕ zero (λ _ → suc) (λ _ _ z _ → suc (suc z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (λ _ _ _ z _ → suc (suc (suc z))) xs) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              a ∷2 xs ≡ a ∷2 xs}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (λ _ ())
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (λ b f ff → λ {zero → {!comm a b!} ; (suc j) → {!!} })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       {!!} xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   λ _ → isSetΠ λ _ → trunc _ _ 
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- FMSet2Loops : GroupHom (Perm (len2 x)) ?  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- FMSet2Loops x = ?
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- Eliminators.recPG (Eli (predℕ (len2 x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --  _ (λ k → {!snd (permFM2 x k)!}) {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsoSP : ∀ n → Iso ⟨ SymData (suc n) ⟩ ⟨ Perm (suc n) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (IsoSP n) = concatG (Perm (suc n)) ∘ mapList η ∘ fst ∘ generatedSym n 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (IsoSP n) = fst (to≃ (suc n)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (IsoSP n) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (IsoSP n) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (GeneratedElim (SymData (suc n)) {f = adjTransposition}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} (λ _ → {!!}) (equivEq ∘ (w n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      w : ∀ n → (l : List (Fin n)) → Path (Fin (suc n) →  Fin (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (  (fst ∘ fst (to≃ (suc n)) ∘ (concatG (Perm (suc n)) ∘ mapList η ∘ fst ∘ generatedSym n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            ((concatG (SymData (suc n)) (mapList adjTransposition l))) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (fst (concatG (SymData (suc n)) (mapList adjTransposition l)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      w zero [] = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      w (suc n) [] i x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- w (suc n) (zero ∷ l) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      w (suc n) (x ∷ l) = {!w (suc n) l!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- from≃ : ∀ n → GroupHom (SymData (suc n)) (Perm (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (from≃ n) = concatG (Perm (suc n)) ∘ mapList η ∘ fst ∘ generatedSym n 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (from≃ n) = record { pres· = pComp ; pres1 = p1 ; presinv = pI }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz : ∀ n → (fst (generatedSym n (idEquiv (Fin (suc n))))) ≡ []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz zero = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz (suc n) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       cong ((_++ []) ∘ mapList suc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong (fst ∘ (generatedSym n)) (equivEq refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ zz n) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     p1 : fst (from≃ n) (GroupStr.1g (SymData (suc n) .snd)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            GroupStr.1g (Perm (suc n) .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     p1 = cong (concatG (Perm (suc n)) ∘ (mapList η)) (zz n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pI : (x : fst (SymData (suc n))) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            fst (from≃ n) (GroupStr.inv (SymData (suc n) .snd) x) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            GroupStr.inv (Perm (suc n) .snd) (fst (from≃ n) x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pI = GeneratedElim (SymData (suc n)) {f = adjTransposition} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!} (ind {!!} {!!})  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pComp : (x y : fst (SymData (suc n))) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               fst (from≃ n) ((SymData (suc n) .snd GroupStr.· x) y) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (Perm (suc n) .snd GroupStr.· fst (from≃ n) x) (fst (from≃ n) y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pComp x = GeneratedElim (SymData (suc n)) {f = adjTransposition} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!} (ind {!!} {!!})  



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ : ∀ {n} → ⟨ Perm (suc n) ⟩ → Fin (suc n) ≃ Fin (suc n) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (η x) = adjTransposition x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (x · y) = to≃ x ∙ₑ to≃ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ ε = idEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (inv x) = invEquiv (to≃ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (assoc x x₁ x₂ i) = (compEquiv-assoc (to≃ x) (to≃ x₁) (to≃ x₂)) i 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (idr x i) = compEquivEquivId (to≃ x) (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (idl x i) = compEquivIdEquiv (to≃ x) (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (invr x i) = invEquiv-is-rinv (to≃ x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (invl x i) = invEquiv-is-linv (to≃ x) i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (zero invo) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (zero braid) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (zero (comm x)) i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (trunc x x₁ x₂ y i i₁) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1≃=invEquivSwap0and1 i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel braid i) = swap0and1Braid i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (comm x) i) = commTranspositions x i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (suc {suc n} ix) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel invo i) = swap0and1≃=invEquivSwap0and1 i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel braid i) = swap0and1Braid i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (comm x) i) = commTranspositions x i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (suc {suc n} invo) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (suc {suc .(suc _)} braid) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (suc {suc .(suc _)} (comm x)) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (suc {suc n} (suc ix)) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- ({!!} ∙∙ (λ i → sucPerm (to≃ (rel ix i))) ∙∙ equivEq {!!}) i



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators : ∀ {n} → ⟨ Perm (suc n) ⟩  → PT.∥ List (Fin n) ∥₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (η x) = PT.∣ [ x ] ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (x · x₁) = PT.map2 _++_ (toGenerators x) (toGenerators x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators ε = PT.∣ [] ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (inv x) = PT.map rev (toGenerators x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (assoc x x₁ x₂ i) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PT.squash₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (PT.map2 _++_ (toGenerators x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (PT.map2 _++_ (toGenerators x₁) (toGenerators x₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (PT.map2 _++_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (PT.map2 _++_ (toGenerators x) (toGenerators x₁)) (toGenerators x₂))  i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (idr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (idl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (invr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (invl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (rel i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (trunc x x₁ x₂ y i i₁) = {!!}




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucConcat : ∀ n → ∀ l →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            concatG (SymData (suc (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ((map adjTransposition (map suc l)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ≡ sucPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (concatG (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (map adjTransposition l)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucConcat n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ind (equivEq λ { _ zero → zero ; _ (suc k) → suc k })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ {a} p → equivEq (
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ { i zero → fst (p i) zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ; i (suc k) → fst (p i) (suc (adjTransposition a .fst k))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             }))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- punchHeadInOutL : ∀ {n} (k : Fin (suc n)) → Σ (List (Fin n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   λ l → concatG (SymData _) (map adjTransposition l) ≡ rot≃ k 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- punchHeadInOutL {n} zero = [] , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (punchHeadInOutL {suc n} (suc k)) = zero ∷ map suc (fst (punchHeadInOutL k))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (punchHeadInOutL {suc n} (suc k)) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cong ( swap0and1≃ ∙ₑ_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (sucConcat n (fst (punchHeadInOutL k)) ∙ cong sucPerm (snd (punchHeadInOutL k)))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym : ∀ n → ⟨ GeneratedBy (SymData (suc n)) adjTransposition ⟩ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym zero = λ _ → PT.∣ [] , equivEq (funExt λ x → isContr→isProp isContrFin1 _ _) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym (suc n) e = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in PT.map (λ (l , p') → map suc l ++ fst (punchHeadInOutL (equivFun e zero))   ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (cong (concatG (SymData (suc (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (map-++ (adjTransposition) (map suc l)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           ((fst (punchHeadInOutL (fst e zero)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ sym (concatG· {G = (SymData (suc (suc n)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (map adjTransposition (map suc l))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (map adjTransposition (fst (punchHeadInOutL (equivFun e zero)))))
           
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙ cong₂ _∙ₑ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (sucConcat n l ∙ cong sucPerm p') (snd (punchHeadInOutL (equivFun e zero)))) ∙ sym p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (generatedSym n e')

  


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators : ∀ n → ⟨ GeneratedBy (Perm n) η ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (η x) = PT.∣ [ x ] , (sym (idr _)) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (x · x₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (PT.map2 λ (x , p) (y , q) → x ++ y ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (concatG (Perm n)) (map-++ η x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ∙∙ sym (concatG· {G = (Perm n)} (map η x) (map η y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ∙∙ cong₂ _·_ p q ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (PermGenerators n x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (PermGenerators n x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n ε = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (inv x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (assoc x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (idr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (idl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (invr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (invl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators (suc (suc n)) (rel invo i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators (suc (suc .(suc _))) (rel braid i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators (suc (suc .(suc _))) (rel (comm x) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators (suc (suc n)) (rel (suc ix) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (trunc x x₁ x₂ y i i₁) = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- HHH : ∀ n → GroupIso (Perm (suc n)) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- HHH n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   GIso _ _ _ (PermGenerators (suc n)) _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (generatedSym n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!} {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (η x) = PT.∣ [ x ] , sym (idr (η x)) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (x · x₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PT.map2 (λ (x , p) (y , q) → (x ++ y) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ({!!} ∙ cong₂ _·_ p q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (PermGenerators n x) (PermGenerators n x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n ε =  PT.∣ [] , refl ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (inv x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    PT.map (λ (x , p) → rev x ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (PermGenerators n x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (assoc x x₁ x₂ i) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    isProp→PathP {!!} {!!} {!!} i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ PermGenerators n (x · (x₁ · x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ PermGenerators n ((x · x₁) · x₂)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (idr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (idl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (invr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (invl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (rel i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ : ∀ {n} → ⟨ Perm (suc n) ⟩  → Fin (suc n) ≃ Fin (suc n) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (η x) = adjTransposition x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (x · y) = to≃ x ∙ₑ to≃ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ ε = idEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (inv x) = invEquiv (to≃ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (assoc x x₁ x₂ i) = (compEquiv-assoc (to≃ x) (to≃ x₁) (to≃ x₂)) i 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (idr x i) = compEquivEquivId (to≃ x) (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (idl x i) = compEquivIdEquiv (to≃ x) (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (invr x i) = invEquiv-is-rinv (to≃ x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (invl x i) = invEquiv-is-linv (to≃ x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel invo i) = swap0and1≃=invEquivSwap0and1 i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel braid i) = swap0and1Braid i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (comm x) i) = commTranspositions x i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (suc {suc n} ix) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel invo i) = swap0and1≃=invEquivSwap0and1 i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel braid i) = swap0and1Braid i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (comm x) i) = commTranspositions x i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (suc {suc n} invo) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (suc {suc .(suc _)} braid) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (suc {suc .(suc _)} (comm x)) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (suc {suc n} (suc ix)) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- ({!!} ∙∙ (λ i → sucPerm (to≃ (rel ix i))) ∙∙ equivEq {!!}) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL : ∀ {ℓ} {A : Type ℓ} {n} → V.Vec A n → ⟨ Perm n ⟩ → V.Vec A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL (x₁ V.∷ x₂ V.∷ l) (η zero) = (x₂ V.∷ x₁ V.∷ l)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL (x₁ V.∷ x₂ V.∷ l) (η (suc x)) = (x₁ V.∷ (onL (x₂ V.∷ l) (η x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (x · x₁) = onL (onL l x) x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l ε = l
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (inv x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (assoc x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (idr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (idl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (invr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (invl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (rel ix i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (trunc x x₁ x₂ y i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ to≃ (fromFree (mapFG suc (fst (permRel (suc n) ix))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ to≃ (fromFree (mapFG suc (snd (permRel (suc n) ix))))





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GeneratedBy : ∀ {ℓ ℓg} → (G : Group ℓ) → (A : Type ℓg) → (A → fst G) → hProp (ℓ-max ℓ ℓg)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (GeneratedBy G A f) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (x : fst G) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∃ (List A) (λ l → x ≡ foldr (GroupStr._·_ (snd G) ∘ f) (GroupStr.1g (snd G)) l )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (GeneratedBy G A f) = isPropΠ λ _ → PT.squash₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GeneratedBy' : ∀ {ℓ ℓg} → (G : Group ℓ) → (A : Type ℓg) → (A → fst G) → hProp (ℓ-max ℓ ℓg)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (GeneratedBy' G A f) = PT.∥ (  (x : fst G) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Σ (List A) (λ l → x ≡ foldr (GroupStr._·_ (snd G) ∘ f) (GroupStr.1g (snd G)) l )) ∥₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (GeneratedBy' G A f) = PT.squash₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasS→≃ : ∀ {ℓ} → {A B : Type ℓ} → (f : A → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → PT.∥ Σ (B → A) (λ g → section f g × retract f g ) ∥₁ → isEquiv f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasS→≃ f = PT.rec (isPropIsEquiv _) λ x → isoToIsEquiv (iso f (fst x) (fst (snd x)) (snd (snd x)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasSR→≃ : ∀ {ℓ} → {A B : Type ℓ} → (f : A → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → PT.∥ hasSection f ∥₁ → PT.∥ hasRetract f ∥₁ → isEquiv f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasSR→≃ f = PT.rec2 (isPropIsEquiv _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  λ x x₁ → isoToIsEquiv (biInvEquiv→Iso-right (biInvEquiv _ (fst x) (snd x) (fst x₁) (snd x₁))) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ} (G H : Group ℓ) (A : Type ℓ) (g : _ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (genG : ⟨ GeneratedBy' G A g ⟩ ) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (m : GroupHom G H)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (genH : ⟨ GeneratedBy' H A (fst m ∘ g) ⟩ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (f : H .fst → G .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (pp : ∀ a → f (fst m (g a)) ≡ g a )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           -- (m' : GroupHom H G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open GroupStr (snd G)  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isEquivM : isEquiv (fst m)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isEquivM = hasS→≃ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (PT.map2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ gH gG →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           let s = λ b → cong (fst m ∘ f) (snd (gH b)) ∙∙ {!!} ∙∙ sym (snd (gH b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              , (s
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               , λ a → cong (f ∘ (fst m)) ((snd (gG a)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ∙∙ sym (snd (gG a))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         genH genG)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- (PT.map
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   (λ gH →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      let f' = (λ x → foldr (GroupStr._·_ (snd G) ∘ g) (GroupStr.1g (snd G)) (fst (gH x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      in f' , (λ b → {!!} ∙ sym (snd (gH b)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   genH ) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- (PT.map2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   (λ gH gG →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      let f'' : H .fst → G .fst 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          f'' = (λ x → foldr (GroupStr._·_ (snd G) ∘ g) (GroupStr.1g (snd G)) (fst (gH x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          -- f' = λ x → foldr (GroupStr._·_ (snd G) ∘ g) (GroupStr.1g (snd G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          --   (fst (gG (f'' x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      in f'' , λ a → {!sym (snd (gH (fst m a)))!}  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   genH genG ) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- genH' : ⟨ GeneratedBy H A (fst m ∘ g) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- genH' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM : ∀ xs → fst m (foldr (λ x₂ → snd G GroupStr.· g x₂) 1g xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      foldr (λ x₂ → snd H GroupStr.· h x₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (GroupStr.1g (snd H)) xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM = {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM' : ∀ xs → fst m' (foldr (λ x₂ → snd H GroupStr.· h x₂) (GroupStr.1g (snd H)) xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      foldr (λ x₂ → snd G GroupStr.· g x₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (GroupStr.1g (snd G)) xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM' = {!!} 




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- sec : section (fst m) (fst m')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- sec x = PT.rec2 {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ (xs , p) (ys , q) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      let z = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      in cong (fst m ∘ fst m') p ∙ {!!} ∙ sym p ) (genH x) (genH (fst m (fst m' x)))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   sec : section (fst m) (fst m')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   sec x = PT.rec2 {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ (x , p) (y , q) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        let z = sym q ∙ cong (fst m') p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        in {!!} ∙ (foldM x) ∙ sym p ) (genH x) (genG (fst m' x))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isInjectiveGen : isInjective m
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isInjectiveGen x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   PT.rec2 (isPropΠ λ _ → is-set _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (λ x₂ x₃ p →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       let pp = sym p ∙ snd x₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       in snd x₂ ∙ {!pp!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (genG x) (genH (fst m x))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermFDMorphism : ∀ n → GroupHom (SymData n) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermFDMorphism n) = sucPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermFDMorphism n)) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (y .fst (x .fst k)) }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermFDMorphism n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc k }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermFDMorphism n)) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (snd x .equiv-proof k .fst .fst) }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PLaws  : {n : ℕ} → List (Fin n) → List (Fin n) → Type where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pInvo : ∀ {n} → PLaws {suc n} (zero ∷ zero ∷ []) []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pComm : ∀ {n} → ∀ k → PLaws {suc (suc n)} (zero ∷ suc (suc k) ∷ []) (suc (suc k) ∷ zero ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pBraid : ∀ {n} → PLaws {suc (suc n)} (zero ∷ one ∷ zero ∷ []) (one ∷ zero ∷ one ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p↑ : ∀ {n k k'} → PLaws {n} k k' → PLaws {suc n} (map suc k) (map suc k')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p← : ∀ {n k k' x} → PLaws {n} k k' → PLaws {n} (x ∷ k) (x ∷ k')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p→ : ∀ {n k k' x} → PLaws {n} k k' → PLaws {n} (k ∷ʳ x) (k' ∷ʳ x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPL : ∀ {n} → (_ / PLaws {n}) → (_ / PLaws {suc n}) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPL =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   rec/ squash/ ([_]/ ∘ map suc) (λ _ _ → eq/ _ _ ∘ p↑)
  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷ʳPL : ∀ {n} → ∀ x → (_ / PLaws {n}) → (_ / PLaws {n}) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷ʳPL x = rec/ squash/ ([_]/ ∘ (_∷ʳ x)) (λ _ _ → eq/ _ _ ∘ p→)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷PL : ∀ {n} → ∀ x → (_ / PLaws {n}) → (_ / PLaws {n}) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷PL x = rec/ squash/ ([_]/ ∘ (x ∷_)) (λ _ _ → eq/ _ _ ∘ p←)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- map-++ : ∀ {ℓ} {A B : Type ℓ} (f : A → B) → ∀ xs ys → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- map-++ f [] ys = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- map-++ f (x ∷ xs) ys = cong (_ ∷_) (map-++ f xs ys)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- rev-map : ∀ {ℓ} {A B : Type ℓ} (f : A → B) → ∀ xs → map f (rev xs) ≡ rev (map f xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- rev-map f = ind refl λ {a} {l} p → map-++ f (rev l) [ a ] ∙ cong (_∷ʳ f a) p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w : ∀ n → (a b : List (Fin n)) → PLaws {n} a b → Path (_ / PLaws {n}) [ rev a ]/ [ rev b ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ pInvo = eq/ _ _ pInvo
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (pComm k) = sym (eq/ _ _ (pComm k))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ pBraid = eq/ _ _ pBraid
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (p↑ {n} {a} {b} p) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let w' = w _ _ _ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      p' = cong sucPL w'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in cong [_]/ (sym (rev-map _ a)) ∙∙ p' ∙∙ cong [_]/ (rev-map _ b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (p← {x = x} p) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let w' = w _ _ _ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in cong (∷ʳPL x) w'

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (p→ {k = k} {k' = k'} {x = x} p) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let w' = w _ _ _ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in cong [_]/ (rev-snoc k _) ∙∙ cong (∷PL x) w' ∙∙  sym (cong [_]/ (rev-snoc k' _))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www : ∀ n → (a b c : List (Fin n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PLaws b c → Path (_ / PLaws {n}) [ a ++ b ]/ [ a ++ c ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www n [] b c x = eq/ _ _ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www n (x₁ ∷ a) b c x = cong (∷PL x₁) (www n a b c x)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www2 : ∀ n → (a b c : List (Fin n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PLaws a b → Path (_ / PLaws {n}) [ a ++ c ]/ [ b ++ c ]/

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www2 n a b [] x = cong [_]/ (++-unit-r _) ∙∙ eq/ _ _ x ∙∙ cong [_]/ (sym (++-unit-r _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www2 n a b (x₁ ∷ c) x = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong [_]/ (sym (++-assoc a [ x₁ ] c)) ∙∙ www2 _ _ _ c (p→ {x = x₁} x) ∙∙ cong [_]/ (++-assoc b [ x₁ ] c)  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∙Perm_ : ∀ {n} → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∙Perm_ {n} = rec2 squash/ (λ x y → [ x ++ y ]/) (www2 n) (www n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePerm : ∀ {n} → (k : Fin (suc n)) →  (_ / PLaws {n})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePerm {n} zero = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePerm {suc n} (suc k) = [  [ zero ]  ]/ ∙Perm sucPL (cyclePerm k)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assocPerm : ∀ {n} → (x y z : List (Fin n) / PLaws) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (x ∙Perm (y ∙Perm z)) ≡ ((x ∙Perm y) ∙Perm z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assocPerm = elimProp3 (λ _ _ _ → squash/ _ _) λ a b c → cong [_]/ (sym (++-assoc a b c))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permInvo : ∀ {n} → ∀ a → PLaws {n} (a ∷ a ∷ []) []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permInvo zero = pInvo
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permInvo (suc a) = p↑ (permInvo a)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm' : ℕ → Group ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Perm' n) = _ / PLaws {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.1g (snd (Perm' n)) = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr._·_ (snd (Perm' n)) = _∙Perm_ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.inv (snd (Perm' n)) = rec/ squash/ ([_]/ ∘ rev) (λ a b p → w n a b p)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.isGroup (snd (Perm' n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   makeIsGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     squash/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     assocPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (elimProp/ (λ _ → squash/ _ _) λ _ → cong ([_]/) (++-unit-r _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ((elimProp/ (λ _ → squash/ _ _) λ _ → refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (elimProp/ (λ _ → squash/ _ _) (ind refl λ {a = a} {l}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p → sym (assocPerm [ [ a ] ]/ [ l ]/ [ rev ([ a ] ++ l) ]/)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∙ cong ([ [ a ] ]/ ∙Perm_) ( assocPerm [ l ]/ [ rev l ]/ [ _ ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∙ cong (_∙Perm [ [ a ] ]/) p) ∙ eq/ _ _ (permInvo a)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (elimProp/ (λ _ → squash/ _ _) (ind refl λ {a = a} {l}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p → sym (assocPerm [ rev l ]/ [ [ a ] ]/ [ _ ]/)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∙ cong ([ rev l ]/ ∙Perm_) ( assocPerm [ [ a ] ]/ [ [ a ] ]/ [ _ ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∙ cong (_∙Perm [ l ]/) (eq/ _ _ (permInvo a))) ∙ p))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evenTest : ℕ → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evenTest zero = true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evenTest (suc x) = not (evenTest x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm : ℕ → Group ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm = Perm' ∘ predℕ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermMorphism : ∀ n → GroupHom (Perm n) (Perm (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermMorphism zero = idGroupHom
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermMorphism (suc n)) = sucPL
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermMorphism (suc n))) =  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp2 (λ _ _ → squash/ _ _ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    λ a b → cong [_]/ (map-++ suc a b)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermMorphism (suc n))) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermMorphism (suc n))) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp/ (λ _ → squash/ _ _) λ a → cong [_]/ (rev-map suc a)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermMorphism : ∀ n → isInjective (sucPermMorphism n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermMorphism zero = λ _ → idfun _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermMorphism (suc n) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimProp/ (λ _ → isPropΠ λ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} --(ind (λ _ → refl) λ x x₁ → {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermFDMorphism : ∀ n → isInjective (sucPermFDMorphism n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermFDMorphism = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedPerm : ∀ n → ⟨ GeneratedBy (Perm' n) (Fin n) ([_]/ ∘ [_]) ⟩ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedPerm n = elimProp/ (λ _ → PT.squash₁ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (ind PT.∣ [] , refl ∣₁ (λ {a} → PT.map λ x → a ∷ fst x , cong ([ [ a ] ]/ ∙Perm_) (snd x)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym : ∀ n → ⟨ GeneratedBy (SymData (suc n)) (Fin n) adjTransposition ⟩ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym zero = λ _ → PT.∣ [] , equivEq (funExt λ x → isContr→isProp isContrFin1 _ _) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in PT.map (λ (l , p') → map suc l ++ {!!}  , p ∙ {!!}) (generatedSym n e')

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH : ∀ n → (a b : List (Fin n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PLaws a b → ∀ k →  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fst (foldr (λ k y → adjTransposition k ∙ₑ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (idEquiv (Fin (suc n))) a) k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fst (foldr (λ k y → adjTransposition k ∙ₑ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (idEquiv (Fin (suc n))) b) k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ pInvo = λ { zero → refl ; one → refl ; (suc (suc k)) → refl }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (pComm k') = λ { zero → refl ; one → refl ; (suc (suc k)) → refl }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ pBraid = λ { zero → refl ; one → refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ; (suc (suc zero)) → refl ; (suc (suc (suc k))) → refl}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p↑ {k = k} {k'} x) zero = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p↑ {k = k} {k'} x) (suc j) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!} ∙∙ cong suc (PermHomH _ k k' x j) ∙∙ {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p← x) k = {!PermHomH _ _ _ (x) k!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p→ x) k = {!PermHomH _ _ _ (x) k!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm : ∀ n → fst (SymData (suc n)) → fst (Perm' n) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm zero x = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in  sucPL (toPerm n e') ∙Perm cyclePerm (equivFun e zero) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev : ∀ {ℓ} (G : Group ℓ) → (xs : List (fst G)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foldr (GroupStr._·_ (snd G)) (GroupStr.1g (snd G)) (rev xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     GroupStr.inv (snd G) (foldr ((GroupStr._·_ (snd G))) ((GroupStr.1g (snd G))) xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev' : ∀ {ℓ ℓg} (G : Group ℓ) (A : Type ℓg) (f : A → fst G) → (xs : List A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foldr (GroupStr._·_ (snd G) ∘ f) (GroupStr.1g (snd G)) (rev xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     GroupStr.inv (snd G) (foldr ((GroupStr._·_ (snd G)) ∘ f) ((GroupStr.1g (snd G))) xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev' G A f [] = sym (GroupTheory.inv1g G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev' G A f (x ∷ xs) = {!!} ∙ sym ((GroupTheory.invDistr G) _ _)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHom : ∀ n → GroupHom (Perm' n) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom n) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   rec/ (isSetΣ (isSet→ isSetFin) (λ _ → isProp→isSet (isPropIsEquiv _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (foldr (λ k y → adjTransposition k ∙ₑ y ) (idEquiv _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b x → equivEq (funExt (PermHomH n a b x)))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimProp2 (λ _ _ → isSetΣ (isSet→ isSetFin) (λ _ → isProp→isSet (isPropIsEquiv _)) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (ind (λ _ → sym (compEquivIdEquiv _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        λ {a} p b → cong (compEquiv (adjTransposition a)) (p b) ∙ compEquiv-assoc _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom n)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp/ (λ _ → isSetΣ (isSet→ isSetFin) (λ _ → isProp→isSet (isPropIsEquiv _)) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   λ l → fold-rev' (SymData (suc n)) (Fin n) adjTransposition l


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHL : ∀ n → ∀ e → PermHom (suc n) .fst (sucPL (toPerm _ e)) ≡ sucPerm e 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHL = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRRR : ∀ n → ∀ k → [ [ k ] ]/ ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (toPerm n (fst (PermHom _) [ [ k ] ]/))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRRR (suc n) k = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRRR (suc n) (suc k) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRR : ∀ n → ∀ k → cyclePerm (suc k) ≡ (toPerm n (fst (PermHom _) (cyclePerm (suc k))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRR .(suc _) zero = isSurPermHomHRRR _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRR .(suc (suc n)) (suc {suc n} k) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- cong (λ x → ([ [ zero ] ]/ ∙Perm sucPL x)) (isSurPermHomHRR _ k) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  {!!} ∙ cong (toPerm _) (sym (IsGroupHom.pres· (snd (PermHom (suc _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   [ [ zero ] ]/ (sucPL (cyclePerm (fst {!!} {!!})))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR : ∀ n → ∀ k → fst (PermHom n) (cyclePerm k) ≡ (rot≃ {suc n} k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR n zero = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR .(suc _) one = equivEq refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR .(suc _) (suc (suc k)) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IsGroupHom.pres· (snd (PermHom (suc _))) [ [ zero ] ]/ (sucPL (cyclePerm (suc k) ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∙ cong₂ _∙ₑ_ (compEquivEquivId _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ((cong {x = (cyclePerm (suc k) )} {y = (toPerm _ (fst (PermHom _) (cyclePerm (suc k))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ((fst (PermHom _)) ∘ sucPL) (isSurPermHomHRR _ k) ∙ isSurPermHomHL _ (fst (PermHom _) (cyclePerm (suc k))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙ (cong sucPerm (isSurPermHomHR _ (suc k))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomH : ∀ n → ∀ x → PermHom n .fst (toPerm n x) ≡ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomH zero x = equivEq (funExt λ x → isContr→isProp isContrFin1 _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomH (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in  (IsGroupHom.pres· (snd (PermHom (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (sucPL (toPerm _ e')) (cyclePerm (equivFun e zero))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∙ cong₂ {x = PermHom _ .fst (sucPL (toPerm _ e'))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            {y = sucPerm e'}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      _∙ₑ_ {!!} {!!}) ∙ sym p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- (isSurPermHomHL _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- (isSurPermHomHR _ (equivFun e zero))) ∙ sym p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHom : ∀ n → isSurjective (PermHom n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHom n x =  PT.∣ (toPerm _ x) , isSurPermHomH n x ∣₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjPermHom : ∀ n → isInjective (PermHom n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjPermHom n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp/ (λ _ → isPropΠ λ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (ind (λ _ → refl) λ {a} _ p →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- ∙ eq/ _ _ (permInvo a))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm : ∀ n → (a : (_ / PLaws {suc n})) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  Σ (Fin (suc (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    λ k → Σ ((_ / PLaws {n})) λ e' → sucPL e' ∙Perm cyclePerm k ≡ a 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHom : ∀ n → GroupHom (Perm (suc n)) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom zero) _ = idEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom zero)) _ _ = equivEq refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom zero)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom zero)) _ = equivEq refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom (suc n)) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (k , e' , p) = unwindPerm _ e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in sucPerm ((fst (PermHom n)) e') ∙ₑ rot≃ k 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom (suc n))) = {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom (suc n))) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom (suc n))) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHom⁻ : ∀ n → GroupHom (SymData (suc n)) (Perm (suc n)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom⁻ zero) _ = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom⁻ zero)) _ _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom⁻ zero)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom⁻ zero)) _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom⁻ (suc n)) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in  sucPL ((fst (PermHom⁻ n)) e') ∙Perm cyclePerm (equivFun e zero) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom⁻ (suc n))) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom⁻ (suc n))) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (GroupStr.·IdR (snd (Perm (suc (suc n)))) (sucPL
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (fst (PermHom⁻ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          _ ))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- cong sucPL (GroupStr.·IdR (snd (Perm (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   {!(fst (PermHom⁻ n) _)!}) ∙ {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom⁻ (suc n))) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in {!!}  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePermAgree : ∀ n → ∀ k → (rot≃ k) ≡ fst (PermHom (suc n)) (cyclePerm k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePermAgree = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP : ∀ n → (a b : List (Fin n)) → PLaws a b → evenTest (length a) ≡ evenTest (length b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc _) .(zero ∷ zero ∷ []) .[] pInvo = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc (suc _)) .(zero ∷ suc (suc k) ∷ []) .(suc (suc k) ∷ zero ∷ []) (pComm k) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc (suc _)) .(zero ∷ one ∷ zero ∷ []) .(one ∷ zero ∷ one ∷ []) pBraid = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc _) .(map suc _) .(map suc _) (p↑ {k = k} {k'} x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  cong evenTest (length-map suc k) ∙∙ wPP _ _ _ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∙∙ sym (cong evenTest (length-map suc k'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP n .(_ ∷ _) .(_ ∷ _) (p← x) = cong not (wPP _ _ _ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP n .(_ ∷ʳ _) .(_ ∷ʳ _) (p→ x) = {!!} ∙∙ cong not (wPP _ _ _ x) ∙∙ {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- parity : ∀ {n} → (_ / PLaws {n}) → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- parity {n} = rec/ isSetBool (evenTest ∘ length ) (wPP n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm : ∀ n → (a : (_ / PLaws {suc n})) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  Σ (Fin (suc (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    λ k → Σ ((_ / PLaws {n})) λ e' → sucPL e' ∙Perm cyclePerm k ≡ a 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm zero x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   if parity x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   then zero , [ [] ]/ , {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   else one , [ [] ]/ , {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm (suc n) a = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermFDMorphism n) = sucPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermFDMorphism n)) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (y .fst (x .fst k)) }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermFDMorphism n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc k }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermFDMorphism n)) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (snd x .equiv-proof k .fst .fst) }




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermParity : ∀ n → GroupHom (Perm' n) BoolGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermParity n) = rec/ isSetBool (evenTest ∘ length ) (wPP n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermParity n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimProp2 (λ _  _ → isSetBool _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- elimProp/ {!!} (ind (elimProp/ (λ _ → isSetBool _ _) (λ _ → refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   λ {a} {l} → ind {B = λ l → ((y : List (Fin n) / PLaws) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       rec/ isSetBool (λ x → evenTest (length x)) (wPP n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       ((Perm n .snd GroupStr.· [ l ]/) y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       (BoolGroup .snd GroupStr.· evenTest (length l))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       (rec/ isSetBool (λ x → evenTest (length x)) (wPP n) y)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (y : List (Fin n) / PLaws) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      rec/ isSetBool (λ x → evenTest (length x)) (wPP n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      ((Perm n .snd GroupStr.· [ a ∷ l ]/) y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (BoolGroup .snd GroupStr.· not (evenTest (length l)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (rec/ isSetBool (λ x → evenTest (length x)) (wPP n) y)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       (λ p → elimProp/ {!!} {!!}) (λ p p' → elimProp/ {!!} {!!}) l) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermParity n)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermParity n)) = elimProp/ (λ _ → isSetBool _ _) {!!}
