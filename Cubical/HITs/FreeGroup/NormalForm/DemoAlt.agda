{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.NormalForm.DemoAlt where

-- open import Cubical.HITs.FreeGroup.Base renaming (assoc to ·assoc)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv.Properties
-- open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Relation.Nullary

open import Cubical.Functions.Involution
open import Cubical.Functions.FunExtEquiv

open import Cubical.Functions.Embedding
import Cubical.Functions.Logic as L

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive as OR
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe as Mb
import Cubical.Data.Int as Int
import Cubical.Data.Fin as Fin

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/₂_ ; [_] to [_]/)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
-- open import Cubical.HITs.TypeQuotients as TQ renaming ([_] to [_]/ₜ ; eq/ to eq/ₜ )


open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.FreeGroup.NormalForm.Base

open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Groups
open import Cubical.Categories.NaturalTransformation

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R
open import Agda.Builtin.String

import Cubical.Algebra.Group.Instances.Int as ℤG

private
  variable
    ℓ : Level
    A : Type ℓ
module FGT (A : Type₀) where
 data GroupTerm : Type₀ where
   η     : A → GroupTerm
   ε     : GroupTerm
   inv   : GroupTerm → GroupTerm
   _·_   : GroupTerm → GroupTerm → GroupTerm

 atoms : GroupTerm → List A
 atoms (η x) = [ x ]
 atoms ε = []
 atoms (inv x) = atoms x
 atoms (x · x₁) = atoms x ++ atoms x₁

module _ (G : Group ℓ) where 

 open GroupStr (snd G)


 open import Cubical.HITs.FreeGroup.NormalForm.EqEps

 open HIT-FG ℕ
 open NFmore isSetℕ
 module nfℕ =  NormalForm.NF ℕ
 
 look : List ⟨ G ⟩ → ℕ → ⟨ G ⟩ 
 look [] _ = 1g
 look (x ∷ x₂) zero = x
 look (x ∷ x₂) (suc k) = look x₂ k

 -- term→FG : FGT.GroupTerm ℕ → (FreeGroup ℕ × ℕ)
 -- term→FG (FGT.η x) = η x , x
 -- term→FG FGT.ε = (ε , zero)
 -- term→FG (FGT.inv x) = map-fst FreeGroup.inv (term→FG x)
 -- term→FG (x FGT.· x₁) = let (y , k) = term→FG x ; (y' , k') = term→FG x₁
 --   in y FreeGroup.· y' , max k k'

 term→FG : FGT.GroupTerm ℕ → FreeGroup ℕ
 term→FG (FGT.η x) = η x
 term→FG FGT.ε = ε
 term→FG (FGT.inv x) = FreeGroup.inv (term→FG x)
 term→FG (x FGT.· x₁) = term→FG x FreeGroup.· term→FG x₁

 module _ (gs : List ⟨ G ⟩) where
  lk = look gs

  gh = HIT-FG.recFG {Group = G} lk

  [[_]] : HIT-FG.freeGroupGroup ℕ .fst → ⟨ G ⟩
  [[_]] = fst gh

  Solve' : (g h : FreeGroup ℕ) → Dec (g ≡ h) → Type ℓ
  Solve' g h (yes p) = [[ g ]] ≡ [[ h ]]
  Solve' g h (no ¬p) = Unit*

  Solve : FreeGroup ℕ → FreeGroup ℕ → Type ℓ
  Solve g h = Solve' g h (discreteFreeGroup discreteℕ g h)

  solve' : ∀ (g h : FreeGroup ℕ) w → Solve' g h w
  solve' _ _ (yes p) = cong [[_]] p
  solve' _ _ (no ¬p) = tt*

  solve* : ∀ (g h : _) → Solve (term→FG g) (term→FG h)
  solve* g h  =
    solve'
     (term→FG g)
     (term→FG h)
     (discreteFreeGroup discreteℕ _ _)




travTC : {A B : Type₀} → (f : A → R.TC B) →
             FGT.GroupTerm A
             → R.TC (FGT.GroupTerm B )
travTC f = w
 where
 w : FGT.GroupTerm _ → R.TC (FGT.GroupTerm _)
 w (FGT.η x) = (f x) >>= R.returnTC ∘ FGT.η
 w FGT.ε = R.returnTC FGT.ε
 w (FGT.inv x) = w x >>= R.returnTC ∘ FGT.inv
 w (x FGT.· x₁) = do x' ← w x ; x₁' ← w x₁ ; R.returnTC (x' FGT.· x₁')


-- *> : {A : Type₀} → FGT.GroupTerm A → FGT.GroupTerm ℕ 
-- *> (FGT.η x) = FGT.η 0
-- *> FGT.ε = FGT.ε
-- *> (FGT.inv x) = FGT.inv (*> x)
-- *> (x FGT.· x₁) = (*> x) FGT.· (*> x₁)



data Is1g {ℓ} {A : Type ℓ} (a : A) : A → Type ℓ where
 is1g : Is1g a a

data IsInv {ℓ} {A : Type ℓ} (inv : A → A) : A → Type ℓ where
 isInv : ∀ x → IsInv inv (inv x) 


data IsOp {ℓ} {A : Type ℓ} (_·_ : A → A → A) : A → Type ℓ where
 isOp : ∀ x y → IsOp _·_ (_·_ x y)
 

module GR where
 -- module GS = GroupStr (snd G)
 open FGT R.Term

 h'2 : List (R.Arg R.Term) → R.TC (R.Term × R.Term)
 h'2 (harg _ ∷ xs) = h'2 xs
 h'2 (varg t1 ∷ varg t2 ∷ []) = R.returnTC (t1 , t2)
 h'2 _ = R.typeError []


 module _ (t1g tInv t· : R.Term) where
  tryG : ℕ → R.Term → R.TC GroupTerm

  try1g : R.Term → R.TC GroupTerm
  try1g t = do
        R.noConstraints
         (R.checkType (R.con (quote is1g) []) (R.def (quote Is1g) 
            ((varg t1g) ∷ [ varg t ])))

        R.returnTC ε

  tryOp : ℕ → R.Term → R.TC GroupTerm
  tryOp zero _ = R.typeError []
  tryOp (suc k) t = do
        tm ← R.noConstraints
         (R.checkType (R.con (quote isOp)
           (varg R.unknown ∷ [ varg R.unknown ])) (R.def (quote IsOp) 
            ((varg t·) ∷ [ varg t ])))
        (t1 , t2) ← h tm
        t1' ← tryG k t1
        t2' ← tryG k t2
        R.returnTC (t1' · t2')

   where
   
   h : R.Term → R.TC (R.Term × R.Term)
   h (R.con (quote isOp) l) = h'2 l
   h _ = R.typeError []
   
  tryInv : ℕ → R.Term → R.TC GroupTerm
  tryInv zero _ = R.typeError []
  tryInv (suc k) t =  do
        tm ← R.noConstraints
         (R.checkType (R.con (quote isInv)
           ([ varg R.unknown ])) (R.def (quote IsInv) 
            ((varg tInv) ∷ [ varg t ])))
        t1 ← h tm
        t1' ← tryG k t1        
        R.returnTC (inv t1')

   where
   h' : List (R.Arg R.Term) → R.TC (R.Term)
   h' (harg _ ∷ xs) = h' xs
   h' (varg t1 ∷ []) = R.returnTC t1
   h' _ = R.typeError []
   
   h : R.Term → R.TC (R.Term)
   h (R.con (quote isInv) l) = h' l
   h _ = R.typeError []


  atom : R.Term → R.TC GroupTerm
  atom x = R.returnTC (η x)


   
  tryG zero _ = R.typeError []
  tryG (suc k) t =
    R.catchTC
     (try1g t)
     (R.catchTC (tryInv k t)
                (R.catchTC (tryOp k t)
                            (atom t)))

 uniqeAtoms : List R.Term → R.TC (List R.Term) 
 uniqeAtoms [] = R.returnTC []
 uniqeAtoms (x ∷ x₁) = do
   notIn ← ensureNotIn x₁
   xs' ← uniqeAtoms x₁
   R.returnTC (if notIn then x ∷ xs' else xs')
  where
  ensureNotIn : List R.Term → R.TC Bool
  ensureNotIn [] = R.returnTC true
  ensureNotIn (x' ∷ xs) =
    R.catchTC (R.unify x x' >> R.returnTC false)
              (ensureNotIn xs)

 unifies? : R.Term → R.Term → R.TC Bool
 unifies? t1 t2 =
   R.catchTC (R.unify t1 t2 >> R.returnTC true)
          (R.returnTC false)

 
 lookT : List R.Term → R.Term → R.TC ℕ
 lookT [] _ = R.typeError []
 lookT (x ∷ x₂) x₁ =
      R.catchTC (R.unify x x₁ >> R.returnTC zero)
          (lookT x₂ x₁ >>= R.returnTC ∘ suc)

 inferEnds : R.Term → R.TC (R.Type × (R.Term × R.Term)) 
 inferEnds hole = do
   ty ← R.inferType hole
   e ← ends ty
   R.returnTC (ty , e)
  where
  ends : R.Term → R.TC (R.Term × R.Term) 
  ends (R.def (quote _≡_) l) = h'2 l
  ends _ = R.typeError []
  
 quoteList : List R.Term → R.Term
 quoteList [] = R.con (quote []) []
 quoteList (x ∷ x₁) = R.con (quote _∷_)
   (varg x ∷ varg (quoteList x₁) ∷ [])

 macro
  infGT : R.Term → R.Term → R.Term →  R.Term → R.Term → R.TC Unit
  infGT tG t1g tInv t· hole = do
   (pTy , (t0 , t1)) ← inferEnds hole
   r0 ← tryG t1g tInv t· 100 t0
   r1 ← tryG t1g tInv t· 100 t1
   ul ← uniqeAtoms (atoms r0 ++ atoms r1)
   r0' ← travTC (lookT ul) r0 >>= R.quoteTC
   r1' ← travTC (lookT ul) r1 >>= R.quoteTC
   
   
   let final = (R.def (quote solve*)
          ( varg tG ∷
            varg (quoteList ul) ∷
            varg r0' ∷
            [ varg r1' ] ))
   tOk ← R.checkType final pTy

   R.unify hole tOk
   R.returnTC tt



-- module TestGeneric0 (G : Group ℓ) (A : Type ℓ) (f : A → ⟨ G ⟩)
--         (g1 g2 g3 : ⟨ G ⟩) (a1 a2 : A) where


--  -- zzz : inv (g1 · (g2 · (f a1 · f a2))) ≡
--  --         ((inv (f a2) · (inv (f a1) · (inv g2 · inv g1))))
--  -- zzz = GR.infGT G --GR.infGT G

--  _·_ = GroupStr._·_ (snd G)
 
--  zzz' : GroupStr.inv (snd G) (g1 · (g2 · (f a1 · f a2))) ≡
--          ((GroupStr.inv (snd G) (f a2)
--            · (GroupStr.inv (snd G) (f a1) ·
--             (GroupStr.inv (snd G) g2 · GroupStr.inv (snd G) g1))))
--  zzz' = (GR.infGT G GroupStr.1g GroupStr.inv GroupStr._·_) --GR.infGT G

data pth {ℓ} {A : Type ℓ} : A → A → Type ℓ where
 [_,_,_] : ∀ x y → x ≡ y → pth x y 
 
module TestGeneric (G : Group ℓ) (A : Type ℓ) (f : A → ⟨ G ⟩)
        (g1 g2 g3 : ⟨ G ⟩) (a1 a2 : A) where

 open GroupStr (snd G)

 -- zzz : inv (g1 · (g2 · (f a1 · f a2))) ≡
 --         ((inv (f a2) · (inv (f a1) · (inv g2 · inv g1))))
 -- zzz = GR.infGT G --GR.infGT G


 zzz' : inv (g1 · (g2 · (f a1 · f a2))) ≡
         ((inv (f a2) · (inv (f a1) · (inv g2 · inv g1))))
 zzz' = GR.infGT G 1g inv _·_ --GR.infGT G


-- --  -- uuu : inv (g3 · g2 · g2) ≡ inv g3 · inv (g1 · g2)
-- --  -- uuu = {!!}

-- -- -- -- instance
-- -- -- --  HasFromNatGroupTerm : HasFromNat GroupTerm
-- -- -- --  HasFromNat.Constraint HasFromNatGroupTerm _ = Unit
-- -- -- --  HasFromNat.fromNat HasFromNatGroupTerm k = η k

-- -- -- -- instance
-- -- -- --  HasFromNegGroupTerm : HasFromNeg GroupTerm
-- -- -- --  HasFromNeg.Constraint HasFromNegGroupTerm _ = Unit
-- -- -- --  HasFromNeg.fromNeg HasFromNegGroupTerm k = inv (η k)

-- -- -- module _ (A : Type ℓ) where
-- -- --  listCurryTy : ℕ → (List A → Type ℓ) → Type ℓ
-- -- --  listCurryTy zero T = T [] 
-- -- --  listCurryTy (suc n) T = ∀ a → listCurryTy n (T ∘ (a ∷_))

-- -- --  listCurry : ∀ {T} → (∀ xs → T xs) → ∀ k → listCurryTy k T 
-- -- --  listCurry x zero = x _
-- -- --  listCurry x (suc k) a = listCurry (x ∘ (a ∷_)) k

-- -- --  lem : ∀ xs (T : List A → Type ℓ) {x} →
-- -- --         listCurryTy (length xs) (λ k → T (x ∷ k))
-- -- --      → T (x ∷ xs)
-- -- --  lem = Li.elim (λ _ x → x)
-- -- --      λ x T {v} z → x (T ∘ (v ∷_)) (z _)
 
-- -- --  listUncurry : ∀ {T} → (∀ k → listCurryTy k T) → ∀ xs → T xs 
-- -- --  listUncurry f [] = f 0
-- -- --  listUncurry {T} f (x ∷ xs) = lem _ T (f (suc (length xs)) x)

-- -- --  currUncurr : ∀ {T : List A → Type ℓ} → (b : (∀ xs → T xs)) → ∀ xs →
-- -- --    listUncurry (listCurry b) xs ≡ b xs
-- -- --  currUncurr b [] = refl
-- -- --  currUncurr b (x ∷ []) = refl
-- -- --  currUncurr {T} b (x ∷ xs@(_ ∷ _)) =
-- -- --    currUncurr {T = T ∘ (x ∷_)} (b ∘ (x ∷_)) (_ ∷ _)

-- -- --  uncurrCurr : ∀ {T : List A → Type ℓ} →
-- -- --    (a : (∀ k → listCurryTy k T)) → ∀ k →
-- -- --    listCurry (listUncurry a) k ≡ a k
-- -- --  uncurrCurr a zero = refl
-- -- --  uncurrCurr a (suc zero) = refl
-- -- --  uncurrCurr {T} a (suc (suc k)) =
-- -- --    funExt λ x → uncurrCurr {T = T ∘ (x ∷_)}
-- -- --       (λ k → a (suc k) _) (suc k)
 
-- -- --  listCurryIso : ∀ {T} → Iso (∀ k → listCurryTy k T) (∀ xs → T xs)
-- -- --  Iso.fun listCurryIso = listUncurry
-- -- --  Iso.inv listCurryIso = listCurry
-- -- --  Iso.rightInv (listCurryIso) = funExt ∘ currUncurr
-- -- --  Iso.leftInv listCurryIso = funExt ∘ uncurrCurr


-- -- -- -- module _ (G : Group ℓ) where 

-- -- -- --  open GroupStr (snd G)


-- -- -- --  open import Cubical.HITs.FreeGroup.NormalForm.EqEps

-- -- -- --  open HIT-FG ℕ
-- -- -- --  open NFmore isSetℕ
-- -- -- --  module nfℕ =  NormalForm.NF ℕ
 
-- -- -- --  look : List ⟨ G ⟩ → ℕ → ⟨ G ⟩ 
-- -- -- --  look [] _ = 1g
-- -- -- --  look (x ∷ x₂) zero = x
-- -- -- --  look (x ∷ x₂) (suc k) = look x₂ k

-- -- -- --  -- term→FG : FGT.GroupTerm ℕ → (FreeGroup ℕ × ℕ)
-- -- -- --  -- term→FG (FGT.η x) = η x , x
-- -- -- --  -- term→FG FGT.ε = (ε , zero)
-- -- -- --  -- term→FG (FGT.inv x) = map-fst FreeGroup.inv (term→FG x)
-- -- -- --  -- term→FG (x FGT.· x₁) = let (y , k) = term→FG x ; (y' , k') = term→FG x₁
-- -- -- --  --   in y FreeGroup.· y' , max k k'

-- -- -- --  term→FG : FGT.GroupTerm ℕ → FreeGroup ℕ
-- -- -- --  term→FG (FGT.η x) = η x
-- -- -- --  term→FG FGT.ε = ε
-- -- -- --  term→FG (FGT.inv x) = FreeGroup.inv (term→FG x)
-- -- -- --  term→FG (x FGT.· x₁) = term→FG x FreeGroup.· term→FG x₁

-- -- -- --  module _ (gs : List ⟨ G ⟩) where
-- -- -- --   lk = look gs

-- -- -- --   gh = HIT-FG.recFG {Group = G} lk

-- -- -- --   [[_]] : HIT-FG.freeGroupGroup ℕ .fst → ⟨ G ⟩
-- -- -- --   [[_]] = fst gh

-- -- -- --   Solve' : (g h : FreeGroup ℕ) → Dec (g ≡ h) → Type ℓ
-- -- -- --   Solve' g h (yes p) = [[ g ]] ≡ [[ h ]]
-- -- -- --   Solve' g h (no ¬p) = Unit*

-- -- -- --   Solve : FreeGroup ℕ → FreeGroup ℕ → Type ℓ
-- -- -- --   Solve g h = Solve' g h (discreteFreeGroup discreteℕ g h)

-- -- -- --   solve' : ∀ (g h : FreeGroup ℕ) w → Solve' g h w
-- -- -- --   solve' _ _ (yes p) = cong [[_]] p
-- -- -- --   solve' _ _ (no ¬p) = tt*

-- -- -- --   solve* : ∀ (g h : FreeGroup ℕ) → Solve g h
-- -- -- --   solve* _ _  = solve' _ _ (discreteFreeGroup discreteℕ _ _)

-- -- -- --  -- solve : ∀ (g h : FGT.GroupTerm ℕ) → {!!}
-- -- -- --  -- solve g' h' = {!!}
-- -- -- --    -- let (g , k) = term→FG g' ; (h , k') = term→FG h'
-- -- -- --    --     -- mK = suc (max k k')
-- -- -- --    -- in {!!}

 

-- -- -- -- -- module GroupSolver (G : Group ℓ) where
-- -- -- -- --  open import Cubical.HITs.FreeGroup as fg

  
-- -- -- -- --  term→FG : FGT.GroupTerm → (FreeGroup ℕ × ℕ)
-- -- -- -- --  term→FG (η x) = η x , x
-- -- -- -- --  term→FG ε = (ε , zero)
-- -- -- -- --  term→FG (inv x) = map-fst inv (term→FG x)
-- -- -- -- --  term→FG (x · x₁) = let (y , k) = term→FG x ; (y' , k') = term→FG x₁
-- -- -- -- --    in y · y' , max k k'

-- -- -- -- --  𝑺 : (g h : GroupTerm) → _
-- -- -- -- --  𝑺 g' h' = let (g , k) = term→FG g' ; (h , k') = term→FG h'
-- -- -- -- --   in listCurry ⟨ G ⟩ 
-- -- -- -- --        (λ xs → solve G xs g h) (suc (max k k'))

-- -- -- -- --  module 𝒈 = GroupStr (snd G)
 

-- -- -- -- --  test : (a a₁ a₂ : fst G) →
-- -- -- -- --           (((𝒈.inv a₁ 𝒈.· a₁) 𝒈.· a) 𝒈.· a₂ 𝒈.· 𝒈.1g)
-- -- -- -- --            ≡ (a 𝒈.· (𝒈.1g 𝒈.· a₁) 𝒈.· 𝒈.inv a₁) 𝒈.· a₂
-- -- -- -- --  test = 𝑺 (((-1 · 1) · 0) · (2 · ε))
-- -- -- -- --           ((0 · ((ε · 1) · -1)) · 2)
