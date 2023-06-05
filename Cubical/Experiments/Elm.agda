{-# OPTIONS --safe #-}

module Cubical.Experiments.Elm where

open import Cubical.Foundations.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (ℤ to Int)
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe as ℙ renaming (Maybe to ℙ ; nothing to ₋₋ ; just to ⌞_) 
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Relation.Nullary
import Cubical.Functions.Logic as L
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Agda.Builtin.String

open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommMonoid.CommMonoidProd
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring

open import Cubical.HITs.PropositionalTruncation as T₁

-- data AA (a b c : Type) 



-- data AA : Type where
--  aa1 aa2 aa3 : AA

-- data BB : Type where
--  bb1 bb2 bb3 : AA → AA → BB

-- testAABB' : (BB) → ℕ
-- testAABB' (bb1 aa1 aa1) = {!!}


-- testAABB : (BB × BB) → ℕ
-- testAABB (bb1 aa1 aa1 , bb1 aa1 aa1) = {!!}


-- testAABB (fst₁ , bb1 x x₁) = {!!}
-- testAABB (bb2 x x₁ , bb2 x₂ x₃) = {!!}
-- testAABB (bb3 x x₁ , bb2 x₂ x₃) = {!!}
-- testAABB (fst₁ , bb3 x x₁) = {!!}
-- testAABB (_ , y) = {!!}
-- testAABB (_ , y) = {!!}

DecProp≡ : {A : Type} → {P₀ P₁ : A → DecProp ℓ-zero} →
  (∀ x → (fst (fst (P₀ x))) ≡ (fst (fst (P₁ x)))) → P₀ ≡ P₁  
DecProp≡ =
 funExt ∘ ((λ p → Σ≡Prop (isPropDec ∘ snd) (L.hProp≡ p)) ∘_)

Dec× : ∀ {A B : Type₀} → Dec A → Dec B → Dec (A × B)
Dec× (yes a) (yes b) = yes (a , b)
Dec× (no ¬a) _ = no λ { (a' , b') → ⊥-elim (¬a a') }
Dec× (yes _) (no ¬b) = no λ { (a' , b') → ¬b b' }
-- Dec× (no ¬a) (yes b) = no λ { (a' , b') → ¬a a' }

DecProp⊓ : DecProp ℓ-zero → DecProp ℓ-zero → DecProp ℓ-zero
DecProp⊓ (PA , DA) (PB , DB) =
  PA L.⊓ PB , (Dec× DA DB)

¬Dec : ∀ {A : Type} → Dec A → Dec (¬ A)
¬Dec (yes p) = no λ x → x p
¬Dec (no ¬p) = yes ¬p

¬P : ∀ {A : Type} → (A → DecProp ℓ-zero)
                  → (A → DecProp ℓ-zero)
¬P x x₁ = (L.¬ fst (x x₁)) , ¬Dec (snd (x x₁))

¬DecProp : DecProp ℓ-zero → DecProp ℓ-zero
¬DecProp (PA , DA) = L.¬ PA , ¬Dec DA

Dec⊔ : ∀ {A B : Type₀} → Dec A → Dec B → Dec ∥ A ⊎ B ∥₁
Dec⊔ (yes p) _ = yes  ∣ inl p ∣₁ 
Dec⊔ (no ¬p) (yes p) = yes ∣ inr p ∣₁
Dec⊔ (no ¬p) (no ¬p₁) = no (T₁.rec isProp⊥ (⊎.rec ¬p ¬p₁))

DecProp⊔ : DecProp ℓ-zero → DecProp ℓ-zero → DecProp ℓ-zero
DecProp⊔ (PA , DA) (PB , DB) =
  PA L.⊔ PB , (Dec⊔ DA DB)

_∪_ : ∀ {A : Type} → (A → DecProp ℓ-zero)
                   → (A → DecProp ℓ-zero)
                   → (A → DecProp ℓ-zero)
(A ∪ B) x = fst (A x) L.⊔ fst (B x) ,
            Dec⊔ (snd (A x)) (snd (B x))
 
commMonoid∪ : ∀ {A : Type} →
  IsCommMonoid (λ _ → (⊥ , isProp⊥) , no λ ()) (_∪_ {A})
commMonoid∪ = w
 where
 open IsCommMonoid
 open IsMonoid
 w : IsCommMonoid (λ _ → (⊥ , isProp⊥) , no λ ()) _∪_
 isSemigroup (isMonoid w) = ww
  where
  open IsSemigroup
  ww : IsSemigroup _∪_
  is-set ww = isSet→ isSetDecProp
  IsSemigroup.·Assoc ww x y z =
    DecProp≡ λ a → cong fst (L.⊔-assoc (fst (x a)) (fst (y a)) (fst (z a))) 
 ·IdR (isMonoid w) x = DecProp≡ λ a → cong fst (L.⊔-identityʳ (fst (x a)))
 ·IdL (isMonoid w) x = DecProp≡ λ a → cong fst (L.⊔-identityˡ (fst (x a)))
 IsCommMonoid.·Comm w x y =
   DecProp≡ λ a → cong fst (L.⊔-comm (fst (x a)) (fst (y a)))


-- isAbGroup∪ : ∀ {A : Type} →
--  IsAbGroup
--   (λ _ → (⊥ , isProp⊥) , no λ ())
--   (_∪_ {A})
--   ¬P
-- IsAbGroup.isGroup isAbGroup∪ = w
--  where
--  w : IsGroup (λ z → (⊥ , isProp⊥) , no (λ ())) _∪_ ¬P
--  IsGroup.isMonoid w = IsCommMonoid.isMonoid commMonoid∪
--  IsGroup.·InvR w x = {!!}
--  IsGroup.·InvL w x = {!!}
-- IsAbGroup.+Comm isAbGroup∪ = IsCommMonoid.·Comm commMonoid∪


_∩_ : ∀ {A : Type} → (A → DecProp ℓ-zero)
                   → (A → DecProp ℓ-zero)
                   → (A → DecProp ℓ-zero)
(A ∩ B) x = (fst (A x) L.⊓ fst (B x)) , Dec× (snd (A x)) (snd (B x))


abs∩∪ : ∀ {ℓ} (P : hProp ℓ) (Q : hProp ℓ) → (P L.⊔ (P L.⊓ Q)) ≡ P
abs∩∪ P Q =
 L.⇔toPath
  (T₁.rec (snd P) (⊎.rec (idfun _) fst))
  λ x → ∣ inl x  ∣₁

abs∪∩ : ∀ {ℓ} (P : hProp ℓ) (Q : hProp ℓ) → (P L.⊓ (P L.⊔ Q)) ≡ P
abs∪∩ P Q =
 L.⇔toPath
  (λ x → fst x)
  λ x → x , ∣ inl x ∣₁


commMonoid∩ : ∀ {A : Type} →
  IsCommMonoid (λ _ → (Unit , isPropUnit) , yes _) (_∩_ {A})
commMonoid∩ = w
 where
 open IsCommMonoid
 open IsMonoid
 w : IsCommMonoid (λ _ → (Unit , isPropUnit) , yes _) _∩_
 isSemigroup (isMonoid w) = ww
  where
  open IsSemigroup
  ww : IsSemigroup _∩_
  is-set ww = isSet→ isSetDecProp
  IsSemigroup.·Assoc ww _ _ _ =
    DecProp≡ λ _ → sym (ua Σ-assoc-≃) 
 ·IdR (isMonoid w) x = DecProp≡ λ _ → isoToPath rUnit×Iso
 ·IdL (isMonoid w) x = DecProp≡ λ _ → isoToPath lUnit×Iso
 IsCommMonoid.·Comm w _ _ =
   DecProp≡ λ _ → isoToPath Σ-swap-Iso

-- RingDecPred : ∀ {A : Type} → RingStr (A → DecProp ℓ-zero)
-- RingDecPred = {!!}

DecPredLat : ∀ {A : Type} → LatticeStr (A → DecProp ℓ-zero)
LatticeStr.0l DecPredLat = λ _ → (⊥ , isProp⊥) , no λ ()
LatticeStr.1l DecPredLat = λ _ → (Unit , isPropUnit) , yes _
LatticeStr._∨l_ DecPredLat = _∪_
LatticeStr._∧l_ DecPredLat = _∩_
LatticeStr.isLattice DecPredLat = w
 where
 open IsLattice
 w : IsLattice (LatticeStr.0l DecPredLat) (LatticeStr.1l DecPredLat)
       (LatticeStr._∨l_ DecPredLat) (LatticeStr._∧l_ DecPredLat)
 joinSemilattice w = ww
  where
  open IsSemilattice
  ww : IsSemilattice (LatticeStr.0l DecPredLat)
         (LatticeStr._∨l_ DecPredLat)
  isCommMonoid ww = commMonoid∪
  idem ww x = DecProp≡ λ a → cong fst (L.⊔-idem (fst (x a)))
 meetSemilattice w = ww
  where
  open IsSemilattice
  ww : IsSemilattice (LatticeStr.1l DecPredLat)
         (LatticeStr._∧l_ DecPredLat)
  isCommMonoid ww = commMonoid∩
  idem ww x = DecProp≡ λ a → cong fst (L.⊓-idem (fst (x a)))
 fst (absorb w x y) = DecProp≡ λ a → cong fst (abs∩∪ (fst (x a)) (fst (y a)))
 snd (absorb w x y) = DecProp≡ λ a → cong fst (abs∪∩ (fst (x a)) (fst (y a)))



ElmRecord : List (String × Type) → Type
ElmRecord [] = Unit
ElmRecord ((_ , x) ∷ xs) = x × ElmRecord xs

data File : Type  where
 File' : File

-- _≮≯_ : {!!}
-- _≮≯_ = {!!}



record DecPoset (P : Poset ℓ-zero ℓ-zero) : Type₁ where
 -- open PosetStr (snd P) renaming (_≤_ to _≤ₚ_)
 _≤ₚ_ : ⟨ P ⟩ → ⟨ P ⟩ → hProp ℓ-zero
 x ≤ₚ y = PosetStr._≤_ (snd P) x y , PosetStr.is-prop-valued (snd P) x y

 

 largestSuch : (X : ⟨ P ⟩ → hProp ℓ-zero) → ⟨ P ⟩ → hProp ℓ-zero
 largestSuch X x = X x L.⊓ (L.∀[ y ] X y L.⇒ (y ≤ₚ x))


 field
  patOrdDec : ∀ x y → Dec ⟨ x ≤ₚ y ⟩


 _≤ᵈ_ : ⟨ P ⟩ → ⟨ P ⟩ → DecProp ℓ-zero 
 x ≤ᵈ y = x ≤ₚ y , patOrdDec x y

 _≮≯ₚ_ : ⟨ P ⟩ → ⟨ P ⟩ → hProp ℓ-zero 
 x ≮≯ₚ y = L.¬ (L.∃[ z ] (z ≤ₚ x) L.⊓ (z ≤ₚ y))


 field
  _⊓?_ : ∀ x y → (Σ _ λ z → ⟨ largestSuch (λ z → (z ≤ₚ x) L.⊓ (z ≤ₚ y)) z ⟩) ⊎ ⟨ x ≮≯ₚ y ⟩ 

 _≮≯_ : ⟨ P ⟩ → ⟨ P ⟩ → DecProp ℓ-zero 
 x ≮≯ y = (x ≮≯ₚ y) ,
     ⊎.rec
       (no ∘ (λ p ¬p → ¬p ∣ fst p , fst (snd p) ∣₁))
       yes
       (x ⊓? y)


 module _ (Pred : ⟨ P ⟩ → hProp ℓ-zero) where
  data StrAntiChain : Type₀


  ∀≮≯ : StrAntiChain → ⟨ P ⟩ → DecProp ℓ-zero

  data StrAntiChain where
   [] : StrAntiChain
   _∷_[_,_]s : (pa : StrAntiChain) →
     (p : ⟨ P ⟩) → ⟨ Pred p ⟩ → (True (snd (∀≮≯ pa p))) → StrAntiChain

  sacTail : StrAntiChain → StrAntiChain
  sacTail [] = []
  sacTail (x ∷ p [ x₁ , _ ]s) = x

  isEmptySAC : StrAntiChain →  DecProp ℓ-zero
  isEmptySAC [] = ((Unit , isPropUnit) , yes _)
  isEmptySAC (x ∷ p [ _ , _ ]s) = ((⊥ , isProp⊥) , no λ ())

  isNotEmptySAC : StrAntiChain →  DecProp ℓ-zero
  isNotEmptySAC [] = ((⊥ , isProp⊥) , no λ ())
  isNotEmptySAC (x ∷ p [ _ , _ ]s) = ((Unit , isPropUnit) , yes _)

  -- _∈sac_ : {!!} → StrAntiChain →  DecProp ℓ-zero
  -- y ∈sac [] = ((⊥ , isProp⊥) , no λ ())
  -- y ∈sac (xs ∷ x [ p ]s) = DecProp⊔ ({!!} ≤ᵈ x) (y ∈sac xs)


  ∀≮≯ [] x₁ = ((Unit , isPropUnit) , yes _)
  ∀≮≯ (xs ∷ x [ _ , _ ]s) y = DecProp⊓ (∀≮≯ xs y) (x ≮≯ y)

  isFull : StrAntiChain → hProp ℓ-zero
  isFull sac = L.∀[ x ] L.¬ (Pred x L.⊓ fst (∀≮≯ sac x)) 

  Full : Type₀
  Full = Σ _ (fst ∘ isFull)

  -- _++AC_ : StrAntiChain → StrAntiChain → StrAntiChain
  -- _++AC_ = {!!}
  
 SAC⊂ : ⟨ P ⟩ → Type₀
 SAC⊂ x = Full (_≤ₚ x)

 ─Ty : Type₀ 
 ─Ty = ∀ x y → Full λ z → z ≤ₚ x L.⊓ L.¬ (z ≤ₚ y)

 mapSAC : ∀ {A B} → (∀ x → ⟨ A x ⟩ → ⟨ B x ⟩)
              →  StrAntiChain A → StrAntiChain B

 map∀≮≯  : ∀ {A B} → (f : ∀ x → ⟨ A x ⟩ → ⟨ B x ⟩)
              → ∀ xs p
              → ⟨ fst (∀≮≯ A xs p) ⟩
              → ⟨ fst (∀≮≯ B (mapSAC f xs) p) ⟩ 
 
 

 mapSAC _ [] = []
 mapSAC f (x₁ ∷ p [ x₂ , x₃ ]s) =
  (mapSAC f x₁) ∷ p [ f _ x₂ ,
    fromWitness (map∀≮≯ f x₁ p (toWitness x₃)) ]s

 map∀≮≯ f [] p x = tt
 map∀≮≯ f (xs ∷ p₁ [ x₁ , x₂ ]s) p x =
  (map∀≮≯ f xs p (fst x)) , snd x



module _ {POA POB : Poset ℓ-zero ℓ-zero}
    {DPA : DecPoset POA}
    {DPB : DecPoset POB}
    {P : ⟨ POA ⟩ → hProp ℓ-zero}
    {Q : ⟨ POB ⟩ → hProp ℓ-zero}
    (f : ⟨ POA ⟩ → ⟨ POB ⟩)
    (g : ∀ x → ⟨ P x ⟩ → ⟨ Q (f x) ⟩)
    
    where

 module DA = DecPoset DPA
 module DB = DecPoset DPB

 SAC-poset-map : (pres≮≯ : ∀ x y → ⟨ x DA.≮≯ₚ y  L.⇒ ((f x) DB.≮≯ₚ (f y)) ⟩ ) → 
      DA.StrAntiChain P → DB.StrAntiChain Q

 SAC-poset-map∀≮≯ : ∀ pres≮≯ xs p 
              → ⟨ fst (DA.∀≮≯ P xs p) ⟩
              → ⟨ fst (DB.∀≮≯ Q (SAC-poset-map pres≮≯ xs) (f p)) ⟩

 SAC-poset-map pres≮≯ DecPoset.[] = DecPoset.[]
 SAC-poset-map pres≮≯ (x DecPoset.∷ p [ x₁ , x₂ ]s) =
    (SAC-poset-map pres≮≯ x) DecPoset.∷ (f p)
      [ g _ x₁ , fromWitness (SAC-poset-map∀≮≯ pres≮≯ x p (toWitness x₂))  ]s

 SAC-poset-map∀≮≯ pres≮≯ DecPoset.[] p x = tt
 SAC-poset-map∀≮≯ pres≮≯ (xs DecPoset.∷ p₁ [ x₁ , x₂ ]s) p x =
   SAC-poset-map∀≮≯ pres≮≯ xs p (fst x) ,  (pres≮≯ _ _) (snd x)

 SAC-poset-map∀≮≯⁻ : ∀ pres≮≯
    (pres≮≯' : ∀ x y → ⟨ ((f x) DB.≮≯ₚ (f y))  L.⇒ x DA.≮≯ₚ y ⟩)
              →  ∀ xs p 
              → ⟨ fst (DB.∀≮≯ Q (SAC-poset-map pres≮≯ xs) (f p)) ⟩
              → ⟨ fst (DA.∀≮≯ P xs p) ⟩

 SAC-poset-map∀≮≯⁻ pres≮≯ pres≮≯' DecPoset.[] p x = tt
 SAC-poset-map∀≮≯⁻ pres≮≯ pres≮≯' (xs DecPoset.∷ p₁ [ x₁ , x₂ ]s) p x =
   SAC-poset-map∀≮≯⁻ pres≮≯ pres≮≯' xs p (fst x) ,
     pres≮≯' _ _ (snd x)


--  -- [_─_]⊂⊃[_] : ⟨ P ⟩ → ⟨ P ⟩ → StrAntiChain → hProp ℓ-zero
--  -- [ x ─ y ]⊂⊃[ sac ] =
--  --    {!!}
--  --   -- L.∀[ z ] (((z ≤ₚ x) L.⊔ (z ≤ₚ y))
--  --   --         L.⇔ (fst (z ∈sac sac)))
 
--  -- _─_ : (x y : ⟨ P ⟩) → Σ StrAntiChain
--  --                        λ sac → ⟨ [ x ─ y ]⊂⊃[ sac ] ⟩ 
--  -- _─_ = {!!}

--  ∀inSAC : (Atom → hProp ℓ-zero) → StrAntiChain → hProp ℓ-zero 
--  ∀inSAC P [] = (Unit , isPropUnit) 
--  ∀inSAC P (sac ∷ p [ _ ]s) = (∀inSAC P sac) L.⊓ (L.∀[ x ] (fromAtom x ≤ₚ p L.⇒ P x  ))

--  ∀inSAC-tail : ∀ P sac → ⟨ ∀inSAC P sac L.⇒ ∀inSAC P (sacTail sac) ⟩
--  ∀inSAC-tail P [] x = tt
--  ∀inSAC-tail P (sac ∷ p [ x₁ ]s) = fst

 -- AC++ : (sc sc' : StrAntiChain) → ⟨ ∀inSAC (L.¬_ ∘ fst ∘ (_∈sac sc) ) sc' ⟩ → StrAntiChain
 -- AC++ sc [] x = sc
 -- AC++ sc (sc' ∷ y [ x₁ ]s) x =
 --   (AC++ sc sc' (fst x)) ∷ y [ fromWitness {!snd x!} ]s
 -- -- AC++ [] sc' _ = sc'
 -- -- AC++ (xs ∷ x [ p ]s) sc' q =
 -- --   AC++ xs (sc' ∷ x [ fromWitness {!toWitness p!} ]s) ({!q!} , {!!})
 -- -- AC++ (sc ∷ p [ x₁ ]s) (sc' ∷ p₁ [ x₂ ]s) x = {!!}


--  DecScan : Type (ℓ-suc ℓ-zero)
--  DecScan =
--    (p : Atom → DecProp ℓ-zero)
--    (mbDecP : ∀ x → Maybe ( (
--          (∀ a → ⟨ (fromAtom a ≤ₚ x) L.⇒ fst (p a)  ⟩)
--        ⊎ (∀ a → ⟨ (fromAtom a ≤ₚ x) L.⇒ L.¬ (fst (p a)) ⟩) )))
--       → Σ StrAntiChain
--          λ sac → ∀ a → ⟨  fst (a ∈sac sac) L.⇔ fst (p a) ⟩ 

--  ∀DecScan : ∀  (p : Atom → DecProp ℓ-zero) sac → (∀ a → ⟨  fst (a ∈sac sac) L.⇒ fst (p a) ⟩)
--               → ⟨ ∀inSAC (fst ∘ p) sac ⟩ 
--  ∀DecScan P [] _ = tt
--  ∀DecScan P (xs ∷ x [ p ]s) q =
--     ∀DecScan P xs ((_∘ ∣_∣₁ ∘ inr) ∘ q) , ((_∘ ∣_∣₁ ∘ inl)) ∘ q
      
 
module _ (Pat : Type)
       (PO : PosetStr ℓ-zero Pat)
       (DP :  DecPoset (_ , PO))
       (_─_ : DecPoset.─Ty DP )
       where

 open PosetStr
 open IsPoset
 open DecPoset


 _≤ℙ_ : ℙ Pat → ℙ Pat → DecProp ℓ-zero
 x ≤ℙ ₋₋ = ((Unit , isPropUnit) , yes _)
 ₋₋ ≤ℙ ⌞_ x₁ = ((⊥ , isProp⊥) , no λ ())
 ⌞_ x ≤ℙ ⌞_ x₁ = (_≤ᵈ_ DP) x x₁
 
 Posetℙ : PosetStr ℓ-zero (ℙ Pat)
 Posetℙ = w
  where
  
  w : PosetStr ℓ-zero (ℙ Pat)
  PosetStr._≤_ w = λ x y → fst (fst (x ≤ℙ y))
  is-set (isPoset w) = ℙ.isOfHLevelMaybe 0 (is-set PO)
  is-prop-valued (isPoset w) = λ x y → snd (fst (x ≤ℙ y)) 
  is-refl (isPoset w) ₋₋ = tt
  is-refl (isPoset w) (⌞_ x) = is-refl (isPoset PO) x
  is-trans (isPoset w) a b ₋₋ x x₁ = tt
  is-trans (isPoset w) (⌞_ a) (⌞_ b) (⌞_ c) x x₁ =
     is-trans (isPoset PO) a b c x x₁
  is-antisym (isPoset w) ₋₋ ₋₋ x x₁ = refl
  is-antisym (isPoset w) (⌞_ a) (⌞_ b) x x₁ =
    cong (⌞_) (is-antisym (isPoset PO) a b x x₁)

 DecPosetℙ : DecPoset (_ , Posetℙ)
 patOrdDec DecPosetℙ = λ x y → snd (x ≤ℙ y) 
 (DecPosetℙ ⊓? ₋₋) ₋₋ = inl (₋₋ , _)
 (DecPosetℙ ⊓? ₋₋) (⌞_ x) = inl (⌞ x , (_ , is-refl (isPoset PO) x) , z)
  where
   z : (x₁ : ℙ Pat) →
         Σ Unit (λ _ → fst (fst (x₁ ≤ℙ (⌞ x)))) → fst (fst (x₁ ≤ℙ (⌞ x)))
   z (⌞_ x₁) = snd

 (DecPosetℙ ⊓? ⌞_ x) ₋₋ = inl (⌞ x , (is-refl (isPoset PO) x , _) , z)
  where
   z : (x₁ : ℙ Pat) → _
   z (⌞_ x₁) = fst
 (DecPosetℙ ⊓? ⌞_ x) (⌞_ x₁) =
    ⊎.map z (_∘ T₁.map z') (_⊓?_ DP x x₁) 
   where
    z : _
    fst (z (y , _)) = ⌞ y
    fst (snd (z (y , q))) = fst q
    snd (snd (z (y , q))) (⌞_ x) x₁ = snd q x x₁

    z' : _
    z' (⌞_ x , q) = x , q

 

 ─ℙ : ─Ty DecPosetℙ
 ─ℙ x ₋₋ = [] , λ _ x →  snd (fst x) _
 ─ℙ ₋₋ (⌞ x₁) = {!!}
 ─ℙ (⌞ x) (⌞ x₁) =
   SAC-poset-map {P = P'} {Q = Q'} ⌞_ (λ _ → idfun _)
     (λ x y → _∘ T₁.map (zz x y) ) (fst zz') , zz''
  where
   P' : _
   P' = _

   Q' : _
   Q' = _

   zz : ∀ x y → _
   zz x y (⌞_ x₁ , snd₁) = x₁ , snd₁

   zz' : _
   zz' = x ─ x₁  

   zz'' : _
   zz'' (⌞_ x) x'' = snd zz' x
     ((fst x'') ,
     SAC-poset-map∀≮≯⁻ {_} {_} {DP} {DecPosetℙ}
       {P'}
       {Q'}
      ⌞_ (λ _ → idfun _)
     (λ x y → _∘' T₁.map (zz x y) )
      zz''' (fst zz') x (snd x''))
    where
    zz''' : _
    zz''' x y = _∘' T₁.map λ w → ⌞ fst w , snd w
    
--  StrAntiChainℙ : StrAntiChain DP → StrAntiChain DecPosetℙ

--  ∀≮≯ℙ : ∀ x p → (fst (fst (∀≮≯ DP x p))) → fst (fst (∀≮≯ DecPosetℙ (StrAntiChainℙ x) (⌞ p)) )

--  -- ℙ≥Atom : ∀ x a → ⟨  _≤ₚ_ DP (fromAtom DP a) x L.⇔ _≤ₚ_ DecPosetℙ (fromAtom DecPosetℙ a) (⌞ x) ⟩ 
--  -- ℙ≥Atom = {!!}

--  StrAntiChainℙ [] = []
--  StrAntiChainℙ (x ∷ p [ x₁ ]s) = StrAntiChainℙ x ∷ ⌞ p [ fromWitness (∀≮≯ℙ x p (toWitness x₁)) ]s

--  ∀≮≯ℙ [] p x₁ = tt
--  ∀≮≯ℙ (x ∷ p₁ [ x₂ ]s) p q =
--   let z = ∀≮≯ℙ x p (fst q)
--   in z , snd q ∘ T₁.map w 
--    where
--    w : Σ (ℙ Pat)
--          (λ x₁ →
--             Σ (fst (fst (x₁ ≤ℙ (⌞ p₁)))) (λ _ → fst (fst (x₁ ≤ℙ (⌞ p))))) →
--          Σ Pat
--          (λ x₁ → Σ ((PO PosetStr.≤ x₁) p₁) (λ _ → (PO PosetStr.≤ x₁) p))
--    w (⌞_ x₁ , x) = x₁ , x

--  DecScanℙ-lem : (x : DecScan DP) → (p :  Atom DP → DecProp ℓ-zero) → ∀ ss
--        → ((a : Atom DP) →
--          Σ
--          (fst (fst ((DP ∈sac a) ss)) →
--           fst (fst (p a)))
--          (λ _ →
--             fst (fst (p a)) →
--             fst (fst ((DP ∈sac a) ss))))
--        → (a : Atom DP) →
--       Σ
--       (fst
--        (fst
--         ((DecPosetℙ ∈sac a) (StrAntiChainℙ ss) )) →
--        fst (fst (p a)))
--       (λ _ →
--          fst (fst (p a)) →
--          fst
--          (fst
--           ((DecPosetℙ ∈sac a) (StrAntiChainℙ ss))))
--  fst (DecScanℙ-lem x p [] _ _) ()
--  snd (DecScanℙ-lem x p [] zz a) = snd (zz a) 
--  DecScanℙ-lem x p (ss ∷ p₁ [ x₁ ]s) zz a =
--    (fst (zz a) ∘ T₁.map (⊎.map (idfun _) {!!})) ,
--    T₁.map ((⊎.map (idfun _) {!!})) ∘ snd (zz a)
--   -- let (qqq) = DecScanℙ-lem x p ss {!zz!} a
--   -- in {!!}
 
--  DecScanℙ : DecScan DP → DecScan DecPosetℙ
--  DecScanℙ x p mbDecP with mbDecP ₋₋
--  ... | nothing =
--    let (z , zz) = x p (mbDecP ∘ ⌞_)
--    in StrAntiChainℙ z , DecScanℙ-lem x p z zz

--  ... | just (inl q) = ([] ∷ ₋₋ [ tt ]s) , λ a → (λ _ → q a _) , (λ _ → ∣ inl _ ∣₁)
--  ... | just (inr q) = [] , λ a → (λ ()) , (q a _)

--  module _ (Pat' : Type)
--         (PO' : PosetStr ℓ-zero Pat')
--         (DP' :  DecPoset (_ , PO'))  
--         where

  

--   _≤×_ : Pat × Pat' → Pat × Pat' → DecProp ℓ-zero
--   (x , x') ≤× (y , y') = DecProp⊓ (_≤ᵈ_ DP x y) (_≤ᵈ_ DP' x' y') 

--   open PosetStr
--   open IsPoset
--   open DecPoset

--   ProdPoset : PosetStr ℓ-zero (Pat × Pat')
--   PosetStr._≤_ ProdPoset = λ x y → (fst (fst (x ≤× y)))
--   is-set (isPoset ProdPoset) = isSet× (is-set (isPoset PO)) ((is-set (isPoset PO')))
--   is-prop-valued (isPoset ProdPoset) = λ x y → (snd (fst (x ≤× y)))
--   is-refl (isPoset ProdPoset) (x , x') =
--     is-refl (isPoset PO) x , is-refl (isPoset PO') x'
--   is-trans (isPoset ProdPoset) x y z (p , p') (q , q') =
--     is-trans (isPoset PO) _ _ _ p q ,
--      is-trans (isPoset PO') _ _ _ p' q'
--   is-antisym (isPoset ProdPoset) _ _ (p , p') (q , q') =
--     cong₂ _,_
--      (is-antisym (isPoset PO) _ _ p q)
--      (is-antisym (isPoset PO') _ _ p' q')

--   DecPoset× : DecPoset (_ , ProdPoset)
--   Atom DecPoset× = Atom DP × Atom DP' 
--   fromAtom DecPoset× = map-× (fromAtom DP) (fromAtom DP')
--   isAtom? DecPoset× (x , x') =
--     mapDec
--      (λ ((y , p) , (y' , p')) → (y , y') , ΣPathP (p , p'))
--      (_∘ (λ ((y , y') , p ) → (y , cong fst p) , (y' , cong snd p)))
--      (Dec× (isAtom? DP x) (isAtom? DP' x'))  
--   fromAtomInj DecPoset× = {!!}
--   patOrdDec DecPoset× = {!!}
--   atomsMinimal DecPoset× = {!!}
--   _⊓?_ DecPoset× = {!!}

  
-- record HasPat (A : Type) : Type₁ where
--  field
--   Pat : Type
--   patData : Pat → Type
  
--   -- patPred : Pat → A → DecProp ℓ-zero
--   patOrd : PosetStr ℓ-zero Pat
--   patDecPoset : DecPoset (_ , patOrd)
--  open DecPoset (DecPosetℙ _ _ patDecPoset)
--  field
--   toAtomPat : A → Atom
--   patDataEquiv : ∀ p →
--      (Σ _
--        λ a →
--        ⟨ DecPoset._≤ₚ_
--          patDecPoset (DecPoset.fromAtom patDecPoset (toAtomPat a)) p ⟩)
--          ≃ patData p
--   patDecScan : DecScan


-- -- --   -- genLat : Pat → ⟨ Lat ⟩
-- -- --   -- isGenLat : 
-- -- --   --    ⟨ (IsLattice.∨MGeneratedBy  (LatticeStr.isLattice (snd Lat))) genLat ⟩  
-- -- --   -- latHom : LatticeHom Lat (_ , DecPredLat {A})

--  ℙat : Type
--  ℙat = ℙ Pat

 

--  data PatChain : Type₀

--  patChainTail : PatChain → (ℙ Pat) → DecProp ℓ-zero

--  data PatChain where
--   [] : PatChain
--   _∷_[_]p : (pc : PatChain) → (p : ℙ Pat) → ⟨ fst (patChainTail pc p) ⟩   → PatChain

--  patChainTail [] y = ((Unit , isPropUnit) , yes _)
--  patChainTail (xs ∷ x [ p ]p) y =
--    DecProp⊓ (patChainTail xs y) (¬DecProp (y ≤ᵈ x)) 

--  patChainCompltₚ : PatChain → hProp ℓ-zero 
--  patChainCompltₚ pc = L.¬ (L.∃[ x ] (fst (patChainTail pc x)))

--  -- patChainCompltₚ' : PatChain → hProp ℓ-zero 
--  -- patChainCompltₚ' pc = ∀


--  patChainCompltₚLawHlp : ∀ pc → _
--  patChainCompltₚLawHlp [] x = just (inl λ _ _ → tt)
--  patChainCompltₚLawHlp pc@(xs ∷ x [ q ]p) y with snd (patChainTail pc y)
--  ... | yes p = nothing
--  ... | no ¬p = just (inr λ a v vv → ¬p ({!!} , {!!}) )
 
--  -- patChainCompltₚLawHlp pc x with snd (patChainTail pc x)


--  patChainCompltₚLaw : ∀ pc →
--    ⟨ patChainCompltₚ pc L.⇔
--      fst (isEmptySAC (fst
--        ((patDecScan (λ a → patChainTail pc (fromAtom a)) (patChainCompltₚLawHlp pc))))) ⟩ 
--  fst (patChainCompltₚLaw []) = {!!}
--  snd (patChainCompltₚLaw []) = {!!}
--  patChainCompltₚLaw (pc ∷ p [ x ]p) = {!!}

-- patData' : ∀ {A} → {{hpA : HasPat A}}
--               →  HasPat.ℙat hpA  → Type₀
-- patData' {A} ₋₋ = A
-- patData' ⦃ hpA = hpA ⦄ (⌞ x) = HasPat.patData hpA x

-- patDataEquiv' : ∀ {A} → {{hpA : HasPat A}}
--               → ∀ p
--               → (Σ _ λ a → ⟨ DecPoset._≤ₚ_ (DecPosetℙ _ _ (HasPat.patDecPoset hpA))
--                 (DecPoset.fromAtom (DecPosetℙ _ _ (HasPat.patDecPoset hpA)) ((HasPat.toAtomPat hpA a))) p ⟩) ≃ patData' p

-- patDataEquiv' ₋₋ = isoToEquiv rUnit×Iso
-- patDataEquiv' ⦃ hpA = hpA ⦄ (⌞ x) = HasPat.patDataEquiv hpA x


-- instance
--  HasPat× : ∀ {A B} → {{HasPat A}} → {{HasPat B}} → HasPat (A × B)
--  HasPat× {A} {B} {{hpA}} {{hpB}} = w
--   where
--   module HPA = HasPat hpA
--   module HPB = HasPat hpB



--   open HasPat
--   w : HasPat (A × B)
--   Pat w = ℙ (HPA.Pat) × ℙ (HPB.Pat) 
--   patData w (a , b) = patData' a × patData' b 
--   patOrd w = _
--   patDecPoset w = 
--     DecPoset×
--      _ _  (DecPosetℙ _ _ (HPA.patDecPoset))
--       _ _ (DecPosetℙ _ _ (HPB.patDecPoset))  

--   toAtomPat w (a , b) = HPA.toAtomPat a , HPB.toAtomPat b
 
--   patDataEquiv w (𝕡A , 𝕡B) = 
--     isoToEquiv ws
--       ∙ₑ ≃-× (patDataEquiv' 𝕡A) (patDataEquiv' 𝕡B)
--    where
--    ws : Iso _ _
--    Iso.fun ws ((a , b) , (a' , b')) = (a , a') , (b , b')
--    Iso.inv ws = _
--    Iso.rightInv ws _ = refl
--    Iso.leftInv ws _ = refl
  
--   patDecScan w p mbDecP = sacAB , {!!}
--    where

--    -- dsB : (aA : _) → DecProp ℓ-zero
--    -- dsB aA =
--    --   DecPoset.isEmptySAC _ (fst (HPB.patDecScan (λ bA → p (aA , bA))
--    --     (map-Maybe (⊎.map (λ x a x₁ → x (aA , a)
--    --      (IsPoset.is-refl (PosetStr.isPoset HPA.patOrd) ((DecPoset.fromAtom ((HPA.patDecPoset)) aA))  , x₁))
--    --         λ x b x₁ y → x (aA , b)
--    --          ((IsPoset.is-refl (PosetStr.isPoset HPA.patOrd) ((DecPoset.fromAtom ((HPA.patDecPoset)) aA)))
--    --           , x₁) y) ∘ mbDecP ∘
--    --      λ bP → ⌞ ((⌞ DecPoset.fromAtom ((HPA.patDecPoset)) aA) , bP) )))


--    dsB' : (aA : DecPoset.Atom HPA.patDecPoset) → {!!}
--    dsB' aA = (HPB.patDecScan (λ bA → p (aA , bA))
--        (map-Maybe (⊎.map (λ x a x₁ → x (aA , a)
--         (IsPoset.is-refl (PosetStr.isPoset HPA.patOrd) ((DecPoset.fromAtom ((HPA.patDecPoset)) aA))  , x₁))
--            λ x b x₁ y → x (aA , b)
--             ((IsPoset.is-refl (PosetStr.isPoset HPA.patOrd) ((DecPoset.fromAtom ((HPA.patDecPoset)) aA)))
--              , x₁) y) ∘ mbDecP ∘
--         λ bP → ⌞ ((⌞ DecPoset.fromAtom ((HPA.patDecPoset)) aA) , bP) ))


--    dsB : (aA : _) → DecProp ℓ-zero
--    dsB aA =
--      DecPoset.isNotEmptySAC _ (fst (dsB' aA))


--    dsA : Σ _ λ sac → ∀ a → _ 
--    dsA = HPA.patDecScan dsB λ _ → nothing

--    ∀dsA : Σ _ λ sac → ∀ a → _ → _ 
--    ∀dsA = map-snd (fst ∘_) dsA
   
--    -- chainAll : _
--    -- chainAll =
--    --   fst (HPB.patDecScan (λ _ → (Unit , isPropUnit) , yes _) λ _ → nothing)

--    open DecPoset

--    step-aAC→abAC : {!!}
--    step-aAC→abAC = {!!}

--    aAC→abAC : ∀ _ → _ →  _
--    aAC→abAC []  ∀a = []
--    aAC→abAC (xs ∷ p [ x ]s) ∀a =
--      AC++ ((DecPosetℙ (Pat w) (patOrd w) (patDecPoset w)))
--       (aAC→abAC xs (λ a x₁ → (∀a a ∣ inr x₁ ∣₁ )))
--        {!∀a!}
--        {!!}

--    sacAB : DecPoset.StrAntiChain
--              (DecPosetℙ (Pat w) (patOrd w) (patDecPoset w))
--    sacAB = uncurry aAC→abAC ∀dsA

-- -- -- -- -- instance
-- -- -- -- --  HasPat× : ∀ {A B} → {{HasPat A}} → {{HasPat B}} → HasPat (A × B)
-- -- -- -- --  HasPat× {A} {B} {{hpA}} {{hpB}} = w
-- -- -- -- --   where
-- -- -- -- --   module HPA = HasPat hpA
-- -- -- -- --   module HPB = HasPat hpB
-- -- -- -- --   open HasPat
-- -- -- -- --   w : HasPat (A × B)
-- -- -- -- --   Pat w = ℙ (HPA.Pat) × ℙ (HPB.Pat)  
-- -- -- -- --   patData w (𝕡A , 𝕡B) = patData' 𝕡A × patData' 𝕡B
-- -- -- -- --   patPred w (𝕡A , 𝕡B) (a , b) =
-- -- -- -- --    DecProp× (patPred' 𝕡A a) (patPred' 𝕡B b)
-- -- -- -- --   patDataEquiv w (𝕡A , 𝕡B) =
-- -- -- -- --      isoToEquiv ww
-- -- -- -- --     ∙ₑ ≃-× (patDataEquiv' 𝕡A) (patDataEquiv' 𝕡B)
    
-- -- -- -- --    where
-- -- -- -- --    ww : Iso _ (Σ A (λ a → ⟨ fst (patPred' 𝕡A a) ⟩) ×
-- -- -- -- --                 Σ B (λ a → ⟨ fst (patPred' 𝕡B a) ⟩))
-- -- -- -- --    Iso.fun ww ((a , b) , (a' , b')) = (a , a') , (b , b')
-- -- -- -- --    Iso.inv ww _ = _
-- -- -- -- --    Iso.rightInv ww _ = refl
-- -- -- -- --    Iso.leftInv ww _ = refl
-- -- -- -- --   Lat w = _ , Lat× (snd (Lat' {A})) (snd (Lat' {B}))
-- -- -- -- --   genLat w (pA , pB) =
-- -- -- -- --       (ℙ.map-Maybe HPA.genLat pA)
-- -- -- -- --     , (ℙ.map-Maybe HPB.genLat pB)
-- -- -- -- --   latHom w = _ ,
-- -- -- -- --    isLatHom× _ _ _ _ _ _
-- -- -- -- --      (snd latHom')
-- -- -- -- --      (snd latHom'


--  -- patChainComplt : PatChain → DecProp ℓ-zero 
--  -- fst (patChainComplt pc) = L.¬ (L.∃[ x ] (fst (patChainTail pc x)))
--  -- snd (patChainComplt []) = no λ x → x ∣ (₋₋ , _) ∣₁
--  -- snd (patChainComplt (pc ∷ p [ x ])) =
--  --   ?
 
-- -- --  data Partition  where
-- -- --   [] : Partition
-- -- --   _∷_ : (pa : Partition) → (p : Pat) → {True (snd (isApart pa p))} → Partition

 

-- -- -- ℙ≃ : {!!}
-- -- -- ℙ≃ = {!!}

-- -- -- data ℙ (X : Type₀) : Type₀



-- -- -- module _ (Pat : Type)
-- -- --        (patOrd : PosetStr ℓ-zero Pat)
-- -- --        (patOrdDec : ∀ x y → Dec (PosetStr._≤_ patOrd x y))
-- -- --        where
-- -- --  module PS = PosetStr patOrd

-- -- --  _≤DP_ : Pat → Pat → DecProp ℓ-zero
-- -- --  x ≤DP x₁ = (x PS.≤ x₁ , PS.is-prop-valued x x₁ ) , patOrdDec x x₁
 
-- -- --  _∼'_ : Pat → Pat → Type
-- -- --  x ∼' y = (¬ x PS.≤ y) × (¬ y PS.≤ x) 

-- -- --  _∼_ : Pat → Pat → DecProp ℓ-zero
-- -- --  x ∼ y = DecProp⊓ (¬DecProp (x ≤DP y)) (¬DecProp (y ≤DP x))

-- -- --  PatTri' : ∀ x y → (Dec (x PS.≤ y)) → (Dec (y PS.≤ x)) →
-- -- --    ⟨ fst (x ∼ y ) ⟩  ⊎ ((x PS.≤ y ) ⊎ (y PS.≤ x))
-- -- --  PatTri' x y (yes p) (yes p₁) = inr (inl p)
-- -- --  PatTri' x y (yes p) (no ¬p) = inr (inl p)
-- -- --  PatTri' x y (no ¬p) (yes p) = inr (inr p)
-- -- --  PatTri' x y (no ¬p) (no ¬p₁) = inl (¬p , ¬p₁)


-- -- --  PatTri : ∀ x y → ⟨ fst (x ∼ y ) ⟩  ⊎ ((x PS.≤ y ) ⊎ (y PS.≤ x))
-- -- --  PatTri x y = PatTri' x y (patOrdDec x y) (patOrdDec y x)

-- -- --  data Partition : Type

-- -- --  isApart : Partition → Pat → DecProp ℓ-zero 
 

-- -- --  data Partition  where
-- -- --   [] : Partition
-- -- --   _∷_ : (pa : Partition) → (p : Pat) → {True (snd (isApart pa p))} → Partition

-- -- --  isApart [] x₁ = ((Unit , isPropUnit) , yes _)
-- -- --  isApart (x ∷ p) x₁ = DecProp⊓ (isApart x x₁) (p ∼ x₁)

-- -- --  isCovered : Partition → Pat → DecProp ℓ-zero 
-- -- --  isCovered [] _ = (⊥ , isProp⊥) , no λ ()
-- -- --  isCovered (xs ∷ x) y = DecProp⊔ (y ≤DP x) (isCovered xs y)  


-- -- --  isCovered⇒¬isApart : ∀ xs y →
-- -- --    ⟨ fst (isCovered xs y) L.⇒ L.¬ (fst (isApart xs y)) ⟩  
-- -- --  isCovered⇒¬isApart (xs ∷ p) y =
-- -- --    T₁.rec (isProp→ isProp⊥) (⊎.elim (λ z z' → snd (snd z') z)
-- -- --      λ z z' → isCovered⇒¬isApart xs y z (fst z'))

-- -- --  isApart⇒¬isCovered : ∀ xs y →
-- -- --    ⟨ fst (isApart xs y) L.⇒ L.¬ (fst (isCovered xs y)) ⟩  
-- -- --  isApart⇒¬isCovered (xs ∷ p) y x =
-- -- --    T₁.rec isProp⊥ (⊎.rec (snd (snd x)) (isApart⇒¬isCovered xs y (fst x)))

-- -- --  _⊆Pa_ : Partition → Partition → hProp ℓ-zero
-- -- --  a ⊆Pa b = L.∀[ x ] fst (isCovered a x) L.⇒ fst (isCovered b x)

-- -- --  ⊆Pa→Ap : ∀ a b → ⟨ a ⊆Pa b 
-- -- --            L.⇒ (L.∀[ x ] fst (isApart b x) L.⇒ fst (isApart a x)) ⟩
                 
-- -- --  ⊆Pa→Ap a b x x₁ x₂ = {!!}


-- -- --  consAp : (xs : Partition) → (y : Pat) →
-- -- --     Σ Partition λ xs' → ⟨ fst (isCovered xs' y) L.⊓ (xs ⊆Pa xs')⟩  
-- -- --  consAp [] x = [] ∷ x , ∣ inl (PS.is-refl x) ∣₁ , λ _ ()
-- -- --   -- ∣ (inl (PS.is-refl x)) , ? ∣₁
-- -- --  consAp xxs@(_∷_ xs x {xs~x}) y with PatTri x y 
-- -- --  ... | inl x₂ = let (xs' , q) = consAp xs y
-- -- --                     z = (⊆Pa→Ap xs xs' (snd q) x {!!})
-- -- --                 in _∷_ xs' x {fromWitness {!!}} ,
-- -- --                     {!!}
-- -- --                  -- _∷_ xs' x {fromWitness {!!}} , ∣ inr q ∣₁ 
-- -- --  ... | inr (inl x₂) = let (xs' , q) = consAp xs y
-- -- --                       in xs' , fst q ,
-- -- --                           λ x' → T₁.rec
-- -- --                            (snd (fst (isCovered (fst (consAp xs y)) x')))
-- -- --                              (⊎.rec (λ z → {!PS.is-trans x' x y z x₂!} )
-- -- --                                    (snd q x'))
-- -- --  -- consAp xs y  
-- -- --  ... | inr (inr x₂) = xxs , ∣ inl x₂ ∣₁ , λ _ → idfun _
 
-- -- -- -- record HasPat (A : Type) : Type₁ where
-- -- -- --  field
-- -- -- --   Pat : Type
-- -- -- --   patData : Pat → Type
-- -- -- --   patPred : Pat → A → DecProp ℓ-zero
-- -- -- --   patDataEquiv : ∀ p → (Σ _ λ a → ⟨ fst (patPred p a) ⟩) ≃ patData p
-- -- -- --   patOrd : PosetStr ℓ-zero Pat
-- -- -- --   patOrdDec : ∀ x y → Dec (PosetStr._≤_ patOrd x y) 
-- -- -- --   -- genLat : Pat → ⟨ Lat ⟩
-- -- -- --   -- isGenLat : 
-- -- -- --   --    ⟨ (IsLattice.∨MGeneratedBy  (LatticeStr.isLattice (snd Lat))) genLat ⟩  
-- -- -- --   -- latHom : LatticeHom Lat (_ , DecPredLat {A})
  
-- -- -- --  ℙat : Type
-- -- -- --  ℙat = ℙ Pat

-- -- -- --  record Case (A B : Type₀) : Type where
-- -- -- --   field
-- -- -- --    𝑝 : Pat
-- -- -- --    𝑓 : patData 𝑝 → B

-- -- -- -- -- -- data ℙ X where
-- -- -- -- -- --  ₋₋ : ℙ X
-- -- -- -- -- --  ⌞_ : X → ℙ X


-- -- -- -- -- open LatticeStr

-- -- -- -- -- ∨ℙ : ∀ {A : Type} →
-- -- -- -- --    (A → A → A) → (ℙ A → ℙ A → ℙ A)
-- -- -- -- -- ∨ℙ f = w
-- -- -- -- --  where
-- -- -- -- --  w : ℙ _ → ℙ _ → ℙ _
-- -- -- -- --  w (⌞_ x) (⌞_ x₁) = ⌞_ (f x x₁)
-- -- -- -- --  w _ _ = ₋₋

-- -- -- -- -- ∧ℙ : ∀ {A : Type} →
-- -- -- -- --    (A → A → A) → (ℙ A → ℙ A → ℙ A)
-- -- -- -- -- ∧ℙ f = w
-- -- -- -- --  where
-- -- -- -- --  w : ℙ _ → ℙ _ → ℙ _
-- -- -- -- --  w (⌞_ x) (⌞_ x₁) = ⌞_ (f x x₁)
-- -- -- -- --  w ₋₋ ₋₋ = ₋₋
-- -- -- -- --  w ₋₋ (⌞_ x) = (⌞_ x)
-- -- -- -- --  w (⌞_ x) ₋₋ = (⌞_ x)


-- -- -- -- -- ℙLat : ∀ {A : Type} → LatticeStr A → LatticeStr (ℙ A)
-- -- -- -- -- ℙLat (latticestr 0l 1l _∨l_ _∧l_ isL) = w
-- -- -- -- --  where
-- -- -- -- --  w : LatticeStr (ℙ _)
-- -- -- -- --  LatticeStr.0l w = ⌞ 0l
-- -- -- -- --  LatticeStr.1l w = ₋₋
-- -- -- -- --  LatticeStr._∨l_ w = ∨ℙ _∨l_
-- -- -- -- --  LatticeStr._∧l_ w = ∧ℙ _∧l_
 
-- -- -- -- --  LatticeStr.isLattice w = ww
-- -- -- -- --   where
-- -- -- -- --   open IsLattice
-- -- -- -- --   ww : IsLattice (⌞ 0l) ₋₋ (LatticeStr._∨l_ w) (LatticeStr._∧l_ w)
-- -- -- -- --   joinSemilattice ww = www
-- -- -- -- --    where
-- -- -- -- --    open IsSemilattice
   
-- -- -- -- --    www : IsSemilattice (⌞ 0l) (LatticeStr._∨l_ w)
-- -- -- -- --    isCommMonoid www = wwww
-- -- -- -- --     where
-- -- -- -- --     wwww : IsCommMonoid (⌞ 0l) (LatticeStr._∨l_ w)
-- -- -- -- --     IsCommMonoid.isMonoid wwww = qq
-- -- -- -- --      where
-- -- -- -- --      open IsMonoid
-- -- -- -- --      qq : IsMonoid (⌞ 0l) (LatticeStr._∨l_ w)
-- -- -- -- --      isSemigroup qq = qqq
-- -- -- -- --       where
-- -- -- -- --       open IsSemigroup
-- -- -- -- --       qqq : IsSemigroup (LatticeStr._∨l_ w)
-- -- -- -- --       is-set qqq = ℙ.isSetMaybe (is-set isL)
-- -- -- -- --       IsSemigroup.·Assoc qqq = qw
-- -- -- -- --        where
-- -- -- -- --        qw : _
-- -- -- -- --        qw ₋₋ y z = refl
-- -- -- -- --        qw (⌞_ x) ₋₋ z = refl
-- -- -- -- --        qw (⌞_ x) (⌞_ x₁) ₋₋ = refl
-- -- -- -- --        qw (⌞_ x) (⌞_ x₁) (⌞_ x₂) =
-- -- -- -- --         cong ⌞_
-- -- -- -- --          (IsCommMonoid.·Assoc ((joinSemilattice isL) .isCommMonoid) x x₁ x₂)
-- -- -- -- --      ·IdR qq ₋₋ = refl
-- -- -- -- --      ·IdR qq (⌞_ x) =
-- -- -- -- --        cong ⌞_
-- -- -- -- --          (IsCommMonoid.·IdR ((joinSemilattice isL) .isCommMonoid) x)
-- -- -- -- --      ·IdL qq ₋₋ = refl
-- -- -- -- --      ·IdL qq (⌞_ x) =
-- -- -- -- --               cong ⌞_
-- -- -- -- --          (IsCommMonoid.·IdL ((joinSemilattice isL) .isCommMonoid) x)
-- -- -- -- --     IsCommMonoid.·Comm wwww ₋₋ ₋₋ = refl
-- -- -- -- --     IsCommMonoid.·Comm wwww ₋₋ (⌞ x) = refl
-- -- -- -- --     IsCommMonoid.·Comm wwww (⌞ x) ₋₋ = refl
-- -- -- -- --     IsCommMonoid.·Comm wwww (⌞ x) (⌞ x₁) =
-- -- -- -- --      cong ⌞_
-- -- -- -- --        (IsCommMonoid.·Comm ((joinSemilattice isL) .isCommMonoid) x x₁)
-- -- -- -- --    idem www ₋₋ = refl
-- -- -- -- --    idem www (⌞ x) = cong ⌞_ (idem (joinSemilattice (isL)) x) 
-- -- -- -- --   meetSemilattice ww = www
-- -- -- -- --    where
-- -- -- -- --    open IsSemilattice
   
-- -- -- -- --    www : IsSemilattice (₋₋) (LatticeStr._∧l_ w)
-- -- -- -- --    isCommMonoid www = qq
-- -- -- -- --      where
-- -- -- -- --      open IsCommMonoid
-- -- -- -- --      qq : IsCommMonoid ₋₋ (LatticeStr._∧l_ w)
-- -- -- -- --      isMonoid qq = qqq
-- -- -- -- --       where
-- -- -- -- --       open IsMonoid
-- -- -- -- --       qqq : IsMonoid ₋₋ (LatticeStr._∧l_ w)
-- -- -- -- --       isSemigroup qqq = wq
-- -- -- -- --        where
-- -- -- -- --        open IsSemigroup
-- -- -- -- --        wq : IsSemigroup (LatticeStr._∧l_ w)
-- -- -- -- --        is-set wq = ℙ.isSetMaybe (is-set isL)
-- -- -- -- --        IsSemigroup.·Assoc wq = zz
-- -- -- -- --         where
-- -- -- -- --         zz : _
-- -- -- -- --         zz ₋₋ ₋₋ ₋₋ = refl
-- -- -- -- --         zz ₋₋ ₋₋ (⌞_ x) = refl
-- -- -- -- --         zz ₋₋ (⌞_ x) ₋₋ = refl
-- -- -- -- --         zz ₋₋ (⌞_ x) (⌞_ x₁) = refl
-- -- -- -- --         zz (⌞_ x) ₋₋ ₋₋ = refl
-- -- -- -- --         zz (⌞_ x) ₋₋ (⌞_ x₁) = refl
-- -- -- -- --         zz (⌞_ x) (⌞_ x₁) ₋₋ = refl
-- -- -- -- --         zz (⌞_ x) (⌞_ x₁) (⌞_ x₂) =
-- -- -- -- --                   cong ⌞_
-- -- -- -- --          (IsCommMonoid.·Assoc ((meetSemilattice isL) .isCommMonoid) x x₁ x₂)
       
-- -- -- -- --       ·IdR qqq ₋₋ = refl
-- -- -- -- --       ·IdR qqq (⌞_ x) = refl
-- -- -- -- --       ·IdL qqq ₋₋ = refl
-- -- -- -- --       ·IdL qqq (⌞_ x) = refl
 
-- -- -- -- --      IsCommMonoid.·Comm qq ₋₋ ₋₋ = refl
-- -- -- -- --      IsCommMonoid.·Comm qq ₋₋ (⌞_ x) = refl
-- -- -- -- --      IsCommMonoid.·Comm qq (⌞_ x) ₋₋ = refl
-- -- -- -- --      IsCommMonoid.·Comm qq (⌞_ x) (⌞_ x₁) =
-- -- -- -- --             cong ⌞_
-- -- -- -- --        (IsCommMonoid.·Comm ((meetSemilattice isL) .isCommMonoid) x x₁)
-- -- -- -- --    idem www ₋₋ = refl
-- -- -- -- --    idem www (⌞ x) = cong ⌞_ (idem (meetSemilattice (isL)) x) 

-- -- -- -- --   absorb ww ₋₋ ₋₋ = refl , refl
-- -- -- -- --   absorb ww ₋₋ (⌞_ x) = refl , refl
-- -- -- -- --   absorb ww (⌞_ x) ₋₋ =
-- -- -- -- --     cong ⌞_ (IsSemilattice.idem (joinSemilattice (isL)) x)  , refl
-- -- -- -- --   absorb ww (⌞_ x) (⌞_ x₁) =
-- -- -- -- --     cong ⌞_ (fst (absorb isL x x₁)) ,
-- -- -- -- --     cong ⌞_ (snd (absorb isL x x₁))

-- -- -- -- -- patData' : ∀ {A} → {{hpA : HasPat A}}
-- -- -- -- --               →  HasPat.ℙat hpA  → Type₀
-- -- -- -- -- patData' {A} ₋₋ = A
-- -- -- -- -- patData' ⦃ hpA = hpA ⦄ (⌞ x) = HasPat.patData hpA x

-- -- -- -- -- patPred' : ∀ {A} → {{hpA : HasPat A}}
-- -- -- -- --               →  HasPat.ℙat hpA  → A → DecProp ℓ-zero
-- -- -- -- -- patPred' ₋₋ x₁ = (Unit , isPropUnit) , (yes _)
-- -- -- -- -- patPred' ⦃ hpA = hpA ⦄ (⌞ x) x₁ = HasPat.patPred hpA x x₁

-- -- -- -- -- patDataEquiv' : ∀ {A} → {{hpA : HasPat A}}
-- -- -- -- --               → ∀ p
-- -- -- -- --               → (Σ A λ a → ⟨ fst (patPred' {A} {{hpA}} p a) ⟩) ≃ patData' p 
-- -- -- -- -- patDataEquiv' ₋₋ = isoToEquiv rUnit×Iso
-- -- -- -- -- patDataEquiv' ⦃ hpA = hpA ⦄ (⌞ x) = HasPat.patDataEquiv hpA x


-- -- -- -- -- -- Lat' : ∀ {A} → {{hpA : HasPat A}} → Lattice ℓ-zero
-- -- -- -- -- -- fst Lat' = _
-- -- -- -- -- -- snd (Lat' ⦃ hpA = hpA ⦄) = ℙLat (snd (HasPat.Lat hpA))

-- -- -- -- -- -- latHom' : ∀ {A} → {{hpA : HasPat A}} →
-- -- -- -- -- --    LatticeHom (Lat' {{hpA}}) (_ , DecPredLat {A})
-- -- -- -- -- -- fst latHom' ₋₋ = (λ _ → (Unit , isPropUnit) , yes _)
-- -- -- -- -- -- fst (latHom' ⦃ hpA = hpA ⦄) (⌞_ x) = fst (HasPat.latHom hpA) x
-- -- -- -- -- -- snd (latHom' ⦃ hpA = hpA ⦄) = w
-- -- -- -- -- --  where
-- -- -- -- -- --  open IsLatticeHom
-- -- -- -- -- --  module ilm = IsLatticeHom (snd (HasPat.latHom hpA))
-- -- -- -- -- --  w : IsLatticeHom (Lat' .snd) (fst latHom') DecPredLat
-- -- -- -- -- --  pres0 w = ilm.pres0 
-- -- -- -- -- --  pres1 w = refl
-- -- -- -- -- --  pres∨l w ₋₋ ₋₋ = DecProp≡ λ a → cong fst (sym (L.⊔-idem (Unit , isPropUnit))) 
-- -- -- -- -- --  pres∨l w ₋₋ (⌞_ x) = {!!}
-- -- -- -- -- --  pres∨l w (⌞_ x) ₋₋ = {!!}
-- -- -- -- -- --  pres∨l w (⌞_ x) (⌞_ x₁) = {!!}
-- -- -- -- -- --  pres∧l w = {!!}


-- -- -- -- -- -- Lat× : ∀ {A B : Type₀} → LatticeStr A → LatticeStr B → LatticeStr (A × B)
-- -- -- -- -- -- Lat× lA lB = w
-- -- -- -- -- --  where
-- -- -- -- -- --  open LatticeStr
-- -- -- -- -- --  w : LatticeStr (_ × _)
-- -- -- -- -- --  0l w = 0l lA , 0l lB
-- -- -- -- -- --  1l w = 1l lA , 1l lB
-- -- -- -- -- --  (w ∨l (a , b)) (a' , b') = _∨l_ lA a a'  , _∨l_ lB b b'
-- -- -- -- -- --  (w ∧l (a , b)) (a' , b') = _∧l_ lA a a'  , _∧l_ lB b b'
-- -- -- -- -- --  isLattice w = ww
-- -- -- -- -- --   where
-- -- -- -- -- --   open IsLattice

-- -- -- -- -- --   module lA = IsLattice (LatticeStr.isLattice lA)
-- -- -- -- -- --   module lB = IsLattice (LatticeStr.isLattice lB)

-- -- -- -- -- --   ww : IsLattice (0l w) (1l w) (_∨l_ w) (_∧l_ w)
-- -- -- -- -- --   joinSemilattice ww = www
-- -- -- -- -- --    where
-- -- -- -- -- --    open IsSemilattice
-- -- -- -- -- --    www : IsSemilattice (0l w) (_∨l_ w)
-- -- -- -- -- --    isCommMonoid www = CommMonoidStr.isCommMonoid (snd (CommMonoidProd
-- -- -- -- -- --           (_ , commmonoidstr _ _
-- -- -- -- -- --                  (isCommMonoid (joinSemilattice (isLattice lA))))
-- -- -- -- -- --           (_ , commmonoidstr _ _
-- -- -- -- -- --                  (isCommMonoid (joinSemilattice (isLattice lB))))))
-- -- -- -- -- --    idem www (a , b) =
-- -- -- -- -- --      cong₂ _,_
-- -- -- -- -- --        (idem (joinSemilattice (isLattice lA)) a)
-- -- -- -- -- --        (idem (joinSemilattice (isLattice lB)) b)
   
-- -- -- -- -- --   meetSemilattice ww = www
-- -- -- -- -- --    where
-- -- -- -- -- --    open IsSemilattice
-- -- -- -- -- --    www : IsSemilattice (1l w) (_∧l_ w)
-- -- -- -- -- --    isCommMonoid www = CommMonoidStr.isCommMonoid (snd (CommMonoidProd
-- -- -- -- -- --           (_ , commmonoidstr _ _
-- -- -- -- -- --                  (isCommMonoid (meetSemilattice (isLattice lA))))
-- -- -- -- -- --           (_ , commmonoidstr _ _
-- -- -- -- -- --                  (isCommMonoid (meetSemilattice (isLattice lB))))))
-- -- -- -- -- --    idem www (a , b) =
-- -- -- -- -- --      cong₂ _,_
-- -- -- -- -- --        (idem (meetSemilattice (isLattice lA)) a)
-- -- -- -- -- --        (idem (meetSemilattice (isLattice lB)) b)
   
-- -- -- -- -- --   fst (absorb ww x y) =
-- -- -- -- -- --     cong₂ _,_
-- -- -- -- -- --      (fst (absorb lA (fst x) (fst y)))
-- -- -- -- -- --      (fst (absorb lB (snd x) (snd y)))
-- -- -- -- -- --   snd (absorb ww x y) =
-- -- -- -- -- --     cong₂ _,_
-- -- -- -- -- --      (snd (absorb lA (fst x) (fst y)))
-- -- -- -- -- --      (snd (absorb lB (snd x) (snd y)))
     



-- -- -- -- -- -- isLatHom× : (A B : Type) (L L' : Lattice ℓ-zero) → ∀ f f' →  
-- -- -- -- -- --    (lhA : IsLatticeHom (snd L) f (DecPredLat {A})) →
-- -- -- -- -- --    (lhB : IsLatticeHom (snd L') f' (DecPredLat {B})) →
-- -- -- -- -- --    IsLatticeHom (Lat× (snd L) (snd L'))
-- -- -- -- -- --      (λ ll' x → DecProp× (f (fst ll') (fst x)) (f' (snd ll') (snd x)))
-- -- -- -- -- --       (DecPredLat {A × B})
   
-- -- -- -- -- -- isLatHom× A B L L' f f' lhA lhB = w
-- -- -- -- -- --  where
-- -- -- -- -- --  open IsLatticeHom
-- -- -- -- -- --  w : IsLatticeHom _ _ _
-- -- -- -- -- --  pres0 w = (funExt
-- -- -- -- -- --   λ ab → cong₂ DecProp× (funExt⁻ (pres0 lhA) (fst ab))
-- -- -- -- -- --                         ((funExt⁻ (pres0 lhB) (snd ab))))
-- -- -- -- -- --    ∙ DecProp≡ λ x → cong fst (L.⊓-idem (⊥ , isProp⊥))
-- -- -- -- -- --  pres1 w = (funExt
-- -- -- -- -- --   λ ab → cong₂ DecProp× (funExt⁻ (pres1 lhA) (fst ab))
-- -- -- -- -- --                         ((funExt⁻ (pres1 lhB) (snd ab))))
-- -- -- -- -- --    ∙ DecProp≡ λ x → cong fst (L.⊓-idem (Unit , isPropUnit))
-- -- -- -- -- --  pres∨l w (l , l') (r , r') =
-- -- -- -- -- --    (funExt
-- -- -- -- -- --     λ ab → cong₂ DecProp× (funExt⁻ (pres∨l lhA l r) (fst ab))
-- -- -- -- -- --                         ((funExt⁻ (pres∨l lhB l' r') (snd ab)))) ∙ 
-- -- -- -- -- --    DecProp≡ λ ab → {!!}
-- -- -- -- -- --  pres∧l w (l , l') (r , r') =
-- -- -- -- -- --    (funExt
-- -- -- -- -- --     λ ab → cong₂ DecProp× (funExt⁻ (pres∧l lhA l r) (fst ab))
-- -- -- -- -- --                         ((funExt⁻ (pres∧l lhB l' r') (snd ab)))) ∙ 
-- -- -- -- -- --    DecProp≡ λ ab → {!!}


-- -- -- -- -- -- -- -- -- Case A B ⦃ hpA ⦄ = Σ (HasPat.ℙat hpA) × {!? → B!}

-- -- -- -- -- -- -- -- CasesL : ∀ {A} {B : Type₀} {{hpA : HasPat A}} → List {!!} → Type
-- -- -- -- -- -- -- -- CasesL = {!!}

-- -- -- -- -- -- -- -- -- data Cases {A} {B : Type₀} {{hpA : HasPat A}} : Type where
-- -- -- -- -- -- -- -- --  _c→_ : ?
 
-- -- -- -- -- -- -- -- case : ∀ {A} {B : Type₀} → {{hpA : HasPat A}} →
-- -- -- -- -- -- -- --   {!? , ?!} →
-- -- -- -- -- -- -- --   A → B
-- -- -- -- -- -- -- -- case = {!!}


-- -- -- -- -- -- -- -- -- Dec× : ∀ {A B : Type₀} → Dec A → Dec B → (Dec (A × B))
-- -- -- -- -- -- -- -- -- Dec× x x₁ = {!!}

 
-- -- -- -- -- -- instance
-- -- -- -- -- --  HasPat× : ∀ {A B} → {{HasPat A}} → {{HasPat B}} → HasPat (A × B)
-- -- -- -- -- --  HasPat× {A} {B} {{hpA}} {{hpB}} = w
-- -- -- -- -- --   where
-- -- -- -- -- --   module HPA = HasPat hpA
-- -- -- -- -- --   module HPB = HasPat hpB
-- -- -- -- -- --   open HasPat
-- -- -- -- -- --   w : HasPat (A × B)
-- -- -- -- -- --   Pat w = ℙ (HPA.Pat) × ℙ (HPB.Pat)  
-- -- -- -- -- --   patData w (𝕡A , 𝕡B) = patData' 𝕡A × patData' 𝕡B
-- -- -- -- -- --   patPred w (𝕡A , 𝕡B) (a , b) =
-- -- -- -- -- --    DecProp× (patPred' 𝕡A a) (patPred' 𝕡B b)
-- -- -- -- -- --   patDataEquiv w (𝕡A , 𝕡B) =
-- -- -- -- -- --      isoToEquiv ww
-- -- -- -- -- --     ∙ₑ ≃-× (patDataEquiv' 𝕡A) (patDataEquiv' 𝕡B)
    
-- -- -- -- -- --    where
-- -- -- -- -- --    ww : Iso _ (Σ A (λ a → ⟨ fst (patPred' 𝕡A a) ⟩) ×
-- -- -- -- -- --                 Σ B (λ a → ⟨ fst (patPred' 𝕡B a) ⟩))
-- -- -- -- -- --    Iso.fun ww ((a , b) , (a' , b')) = (a , a') , (b , b')
-- -- -- -- -- --    Iso.inv ww _ = _
-- -- -- -- -- --    Iso.rightInv ww _ = refl
-- -- -- -- -- --    Iso.leftInv ww _ = refl
-- -- -- -- -- --   Lat w = _ , Lat× (snd (Lat' {A})) (snd (Lat' {B}))
-- -- -- -- -- --   genLat w (pA , pB) =
-- -- -- -- -- --       (ℙ.map-Maybe HPA.genLat pA)
-- -- -- -- -- --     , (ℙ.map-Maybe HPB.genLat pB)
-- -- -- -- -- --   latHom w = _ ,
-- -- -- -- -- --    isLatHom× _ _ _ _ _ _
-- -- -- -- -- --      (snd latHom')
-- -- -- -- -- --      (snd latHom')

-- -- -- -- -- -- -- instance
-- -- -- -- -- -- --  Maybe× : ∀ {A} → {{HasPat A}} → HasPat (Maybe A)
-- -- -- -- -- -- --  Maybe× {A} {{hpA}} = w
-- -- -- -- -- -- --   where
-- -- -- -- -- -- --   module HPA = HasPat hpA
-- -- -- -- -- -- --   open HasPat
-- -- -- -- -- -- --   w : HasPat (Maybe A)
-- -- -- -- -- -- --   Pat w = Maybe (ℙ (HPA.Pat))
-- -- -- -- -- -- --   patData w nothing = Unit
-- -- -- -- -- -- --   patData w (just x) = patData' x
-- -- -- -- -- -- --   patPred w nothing nothing = (Unit , isPropUnit) , yes _ 
-- -- -- -- -- -- --   patPred w nothing (just x) = (⊥ , isProp⊥) , no λ ()
-- -- -- -- -- -- --   patPred w (just _) nothing = (⊥ , isProp⊥) , no λ ()
-- -- -- -- -- -- --   patPred w (just 𝕡A) (just a) = patPred' 𝕡A a
-- -- -- -- -- -- --   patDataEquiv w nothing = isoToEquiv ww
-- -- -- -- -- -- --    where
-- -- -- -- -- -- --    ww : Iso (Σ (Maybe A) (λ a → ⟨ fst (patPred w nothing a) ⟩))
-- -- -- -- -- -- --           (patData w nothing)
-- -- -- -- -- -- --    Iso.fun ww _ = _
-- -- -- -- -- -- --    Iso.inv ww x = nothing , _
-- -- -- -- -- -- --    Iso.rightInv ww b = refl
-- -- -- -- -- -- --    Iso.leftInv ww (nothing , _) = refl
-- -- -- -- -- -- --   patDataEquiv w (just x) = isoToEquiv ww ∙ₑ patDataEquiv' x   
-- -- -- -- -- -- --    where
-- -- -- -- -- -- --    ww : Iso (Σ (Maybe A) (λ a → ⟨ fst (patPred w (just x) a) ⟩))
-- -- -- -- -- -- --           (Σ A (λ a → ⟨ fst (patPred' x a) ⟩))
-- -- -- -- -- -- --    Iso.fun ww (just a , p) = a , p
-- -- -- -- -- -- --    Iso.inv ww (a , p) = just a , p
-- -- -- -- -- -- --    Iso.rightInv ww b = refl
-- -- -- -- -- -- --    Iso.leftInv ww (just a , p) = refl

-- -- -- -- -- -- -- -- Confirmations : Type
-- -- -- -- -- -- -- -- Confirmations = ElmRecord (("acceptRegulations" , Bool) ∷ ("acceptPaymentsRules" , Bool) ∷ ("acceptInfClause" , Bool) ∷ [] )


-- -- -- -- -- -- -- -- TimeSlotData : Type
-- -- -- -- -- -- -- -- TimeSlotData = ElmRecord (("year" , Int) ∷ ("month" , Int) ∷ ("day" , Int) ∷ ("start" , Int × Int) ∷ ("end" , Int × Int) ∷ [] )


-- -- -- -- -- -- -- -- TimeSlotsForPatientsToChooseFrom : Type
-- -- -- -- -- -- -- -- TimeSlotsForPatientsToChooseFrom = ElmRecord (("days" , List (Int × Int × Int × Int × Int × Int × List (Int × Int × Int) × List (Int × List (List (String × TimeSlotData))))) ∷ [] )



-- -- -- -- -- -- -- -- data Model : Type where
-- -- -- -- -- -- -- --  LoadingDates' : Model
-- -- -- -- -- -- -- --  SlotPicking' : (TimeSlotsForPatientsToChooseFrom) → (Int) → Model
-- -- -- -- -- -- -- --  SigningIn' : (String × Int × TimeSlotData) → (String × String) → (String × String) → (Confirmations) → Model
-- -- -- -- -- -- -- --  RegisterSucesfull' : Model
-- -- -- -- -- -- -- --  RegisterAppError' : (String) → Model
-- -- -- -- -- -- -- --  RescheduleSuccess' : Model
