{-# OPTIONS #-}

module Cubical.Experiments.Elm where

open import Cubical.Foundations.Everything hiding (Sub)

open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (ℤ to Int)
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (elim to ⊥-elim ;rec to ⊥-rec)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe as ℙ renaming (Maybe to ℙ ; nothing to ₋₋ ; just to ⌞_) 
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li

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

postulate
 Float : Type
 File : Type
postulate
 Html : Type → Type
 Attribute : Type → Type
 Style : Type
 
postulate
 Cmd : Type → Type
 Sub* : Type → Type
 
postulate
 Program : Type → Type → Type → Type

module Cmd where
 postulate none : ∀ {msg} → Cmd msg
 -- none = 

module Sub where
 postulate none : ∀ {msg} → Cmd msg
 -- none = 


-- postulate
--  node : ∀ {msg} → List (Attribute msg) → List (Html msg) → Html msg
--  div : ∀ {msg} → List (Attribute msg) → List (Html msg) → Html msg
--  text : ∀ {msg} → String → Html msg 
--  class : ∀ {msg} → String → List (Attribute msg) 
--  css : ∀ {msg} → List Style → Attribute msg
--  FontSize : Type
--  fontSize : FontSize → Style
--  px : ℕ → FontSize
--  _>_ : ∀ {a : Type} → a → a → Bool
--  _<_ : ∀ {a : Type} → a → a → Bool
--  onClick : ∀ {msg} → msg → Attribute msg


-- postulate
--  Decoder : Type → Type
--  Value : Type

module Set where
 postulate
  Set : Type → Type

-- module List where
--  drop : ∀ {a} {A : Type a} → Int → List A → List A
--  drop = ?

-- ElmRecord : List (String × Type) → Type
-- ElmRecord [] = Unit
-- ElmRecord ((_ , x) ∷ xs) = x × ElmRecord xs



-- fieldType' : List (String × Type) → String → Type
-- fieldType' [] x₁ = Unit
-- fieldType' ((fst₁ , snd₁) ∷ x₂) x₁ with primStringEquality fst₁ x₁
-- ... | false = fieldType' x₂ x₁
-- ... | true = snd₁

-- ElmRecord' : (Sig : List (String × Type)) → Type  
-- ElmRecord' Sig = ∀ x → fieldType' Sig x

isJustᵈ : ∀ {ℓ} {A : Type ℓ} → Maybe A → DecProp ℓ-zero
isJustᵈ ₋₋ = (⊥ , isProp⊥) , no λ ()
isJustᵈ (⌞_ x) = (Unit , isPropUnit) , yes _

module ElmRecords (FieldId : Type) (_≟f_ : Discrete FieldId) where


 _≡f_ : FieldId → FieldId → DecProp ℓ-zero
 x ≡f x₁ = ((x ≡ x₁) , Discrete→isSet _≟f_ _ _) , (x ≟f x₁)
 
 Sig : Type₁
 Sig = List (FieldId × Type)


 fieldType : Sig → FieldId → Type
 fieldType' : FieldId → Type → Sig → Bool → FieldId → Type
 fieldType' x x₁ x₂ false x₄ = fieldType x₂ x₄
 fieldType' x x₁ x₂ true x₄ = x₁

 fieldType [] x₁ = ⊥
 fieldType ((nm , ty) ∷ x₂) x =
   fieldType' nm ty x₂ (Dec→Bool (nm ≟f x)) x

 ElmRecordData : (s : Sig) → Type  
 ElmRecordData s = ∀ x → Maybe (fieldType s x)

 erdTail' : ∀ nm ty s w → 
      ∀ x → ℙ (fieldType' nm ty s w x) →  ℙ (fieldType s x)
 erdTail' nm ty s false x x₁  = x₁
 erdTail' nm ty s true x x₁ = nothing
 
 erdTail : ∀ nm ty s → ElmRecordData ((nm , ty) ∷ s) → ElmRecordData s
 erdTail nm ty s r x = erdTail' nm ty s (Dec→Bool (nm ≟f x)) x (r x)  

 isComplete : ∀ s → ElmRecordData s → DecProp ℓ-zero
 isComplete [] _ = (Unit , isPropUnit) , yes _
 isComplete ((nm , ty) ∷ s) r =
   DecProp⊓ (isJustᵈ (r nm))
    (isComplete s (erdTail nm ty s r ))

 record 𝑹_ (sig : Sig) : Type where
  constructor 𝒓_
  field
   rData : ElmRecordData sig
   {rCheck} : True (snd (isComplete sig rData)) 

 haveField : Sig → FieldId → DecProp ℓ-zero
 haveField [] x₁ = (⊥ , isProp⊥) , no λ ()
 haveField (x ∷ x₂) x₁ = DecProp⊔ (fst x ≡f x₁) (haveField x₂ x₁)

 -- _⊙_ : {!!}
 -- _⊙_ = {!!}

 postulate
  𝒖 : ∀ {s} → 𝑹 s → ∀ f  → fieldType s f → {True (snd (haveField s f))}  → 𝑹 s
  _⊙_ : ∀ {s} → 𝑹 s → ∀ f → {True (snd (haveField s f))}  → fieldType s f
  -- 𝒖 = ?

primStringEquality-comm : ∀ {x y} → primStringEquality x y ≡ primStringEquality y x
primStringEquality-comm {x} {y} with primStringEquality x y | primStringEquality y x
... | false | false = refl
... | false | true = imposible-primStringEquality-comm
  where
    postulate imposible-primStringEquality-comm : _ 
... | true | false = imposible-primStringEquality-comm
  where
    postulate imposible-primStringEquality-comm : _
... | true | true = refl


postulate same-strings :
             ∀ {x y : String} →
             Bool→Type (primStringEquality x y) → x ≡ y

postulate different-strings :
             ∀ {x y : String} →
             Bool→Type (not (primStringEquality x y)) → ¬ (x ≡ y)

dichotomyBool' : (x : Bool) → (Bool→Type x) ⊎ (Bool→Type (not x))
dichotomyBool' false = inr _
dichotomyBool' true = inl _


String-Discrete-postulated : Discrete String
String-Discrete-postulated x y = 

   ⊎.elim {C = const (Dec (x ≡ y)) }
      (yes ∘ same-strings {x} {y})
      (no ∘ different-strings {x} {y})
   (dichotomyBool' (primStringEquality x y))


open ElmRecords String String-Discrete-postulated public

--  -- appendField : ∀ f t s → 𝑹 s → t → 𝑹 ((f , t) ∷ s) 
--  -- 𝑹_.rData (appendField f t s x x₁) x₂ = {!!}
--  -- 𝑹_.rCheck (appendField f t s x x₁) = {!!}
 
--  -- 𝒍_ : (xs : List (FieldId × Σ Type λ x → x)) →
--  --          𝑹 Li.map (map-snd fst) xs
--  -- 𝒍 [] = 𝒓 (λ _ → nothing)
--  -- 𝒍 ((nm , (Ty , val)) ∷ xs) = 𝒓_ r {q}
--  --   where
--  --    r' = 𝒍 xs

--  --    r* : ∀ b → (x : FieldId) →
--  --        Maybe (fieldType' nm Ty (Li.map (map-snd fst) xs) b x)
--  --    r* false x = 𝑹_.rData (𝒍 xs) x
--  --    r* true x = just val



--  --    r : ∀ x → _
--  --    r x = r* ((Dec→Bool (nm ≟f x))) x

--  --    q' = (toWitness (𝑹_.rCheck (𝒍 xs)))

--  --    -- q* : ∀ b → ⟨ (fst (isComplete (Li.map (map-snd fst) ((nm , Ty , val) ∷ xs))
--  --    --        {!!})) ⟩
--  --    -- q* = {!!}

--  --    q : True
--  --          (snd (isComplete (Li.map (map-snd fst) ((nm , Ty , val) ∷ xs)) {!!}))
--  --    q = fromWitness ({!!} , {!q'!})



-- -- module TestOnℕ where
-- --  open ElmRecords _ discreteℕ

-- --  sig1 : Sig
-- --  sig1 = (7 , Bool) ∷ (8 , ℕ) ∷ (9 , (Unit × Unit)) ∷ []

-- --  r1 : 𝑹 sig1
-- --  r1 = 𝒓 λ { 7 → just true
-- --           ; 8 → just 4
-- --           ; 9 → just _
-- --           ; _ → nothing
-- --           }
--   -- where
--   -- w : _
--   -- w 7 = just true
--   -- w 8 = just 4
--   -- w 9 = just (tt , tt)
--   -- w _ = nothing
  
-- -- ssssT : String → ℕ
-- -- ssssT = λ { "aaa" → 0
-- --           ; "bbb" → 2
-- --           ; _ → 3
-- --           }

-- -- -- postulate
-- -- --  primStringEquality-refl : ∀ x → primStringEquality x x ≡ true



-- -- -- isComplete : ∀ {Sig} → ElmRecordData Sig → DecProp ℓ-zero
-- -- -- isComplete {[]} x = (Unit , isPropUnit) , yes _
-- -- -- isComplete {(nm , ty) ∷ Sig} x with primStringEquality nm nm | x nm
-- -- -- ... | false | ww = {!!}
-- -- -- ... | true | nothing = (⊥ , isProp⊥) , no λ ()
-- -- -- ... | true | just x₁ = (isComplete {Sig} {!x!})

-- -- -- -- erTest : ElmRecord (("aa" , ℕ) ∷ ("bb" , (Bool × ℕ)) ∷ [])
-- -- -- -- erTest = {!λ {
-- -- -- --             }!}





-- -- -- -- _≮≯_ : {!!}
-- -- -- -- _≮≯_ = {!!}



-- -- -- -- record DecPoset (P : Poset ℓ-zero ℓ-zero) : Type₁ where
-- -- -- --  -- open PosetStr (snd P) renaming (_≤_ to _≤ₚ_)
-- -- -- --  _≤ₚ_ : ⟨ P ⟩ → ⟨ P ⟩ → hProp ℓ-zero
-- -- -- --  x ≤ₚ y = PosetStr._≤_ (snd P) x y , PosetStr.is-prop-valued (snd P) x y

 

-- -- -- --  largestSuch : (X : ⟨ P ⟩ → hProp ℓ-zero) → ⟨ P ⟩ → hProp ℓ-zero
-- -- -- --  largestSuch X x = X x L.⊓ (L.∀[ y ] X y L.⇒ (y ≤ₚ x))

-- -- -- --  minimal : ∀ p → hProp ℓ-zero
-- -- -- --  minimal p = L.∀[ x ] x ≤ₚ p L.⇒ (p ≤ₚ x ) 
 
-- -- -- --  field
-- -- -- --   patOrdDec : ∀ x y → Dec ⟨ x ≤ₚ y ⟩


-- -- -- --  _≤ᵈ_ : ⟨ P ⟩ → ⟨ P ⟩ → DecProp ℓ-zero 
-- -- -- --  x ≤ᵈ y = x ≤ₚ y , patOrdDec x y

-- -- -- --  _≮≯ₚ_ : ⟨ P ⟩ → ⟨ P ⟩ → hProp ℓ-zero 
-- -- -- --  x ≮≯ₚ y = L.¬ (L.∃[ z ] (z ≤ₚ x) L.⊓ (z ≤ₚ y))

-- -- -- --  ≮≯-sym : ∀ x y → ⟨ x ≮≯ₚ y ⟩  → ⟨ y ≮≯ₚ x ⟩ 
-- -- -- --  ≮≯-sym x y = _∘ T₁.map (map-snd (fst Σ-swap-≃))
 
-- -- -- --  field
-- -- -- --   _⊓?_ : ∀ x y → (Σ _ λ z → ⟨ largestSuch (λ z → (z ≤ₚ x) L.⊓ (z ≤ₚ y)) z ⟩) ⊎ ⟨ x ≮≯ₚ y ⟩ 

-- -- -- --  _≮≯_ : ⟨ P ⟩ → ⟨ P ⟩ → DecProp ℓ-zero 
-- -- -- --  x ≮≯ y = (x ≮≯ₚ y) ,
-- -- -- --      ⊎.rec
-- -- -- --        (no ∘ (λ p ¬p → ¬p ∣ fst p , fst (snd p) ∣₁))
-- -- -- --        yes
-- -- -- --        (x ⊓? y)

-- -- -- --  ≮≯-≤ : ∀ x y y' → ⟨ (x ≮≯ₚ y) L.⇒ (y' ≤ₚ y) L.⇒ (x ≮≯ₚ y') ⟩
-- -- -- --  ≮≯-≤ x y y' x₁ x₂  = x₁ ∘ T₁.map λ a → fst a , fst (snd a) ,
-- -- -- --      PosetStr.is-trans (snd P) (fst a) y' y (snd (snd a)) x₂

-- -- -- --  ≤-≮≯ : ∀ x y x' → ⟨ (x ≮≯ₚ y) L.⇒ (x' ≤ₚ x) L.⇒ (x' ≮≯ₚ y) ⟩
-- -- -- --  ≤-≮≯ x y x' x₁ x₂  = 
-- -- -- --    x₁ ∘ T₁.map λ a → fst a , PosetStr.is-trans (snd P) (fst a) x' x (fst (snd a)) x₂  ,
-- -- -- --      snd (snd a)

-- -- -- --  _≮≯ₘ_ : (p : ⟨ P ⟩) → ((p' , pmin) : Σ ⟨ P ⟩ (fst ∘ minimal)) →
-- -- -- --               ⟨ p' ≤ₚ p ⟩ ⊎ ⟨ p ≮≯ₚ p' ⟩ 
-- -- -- --  p ≮≯ₘ (p' , pmin) =
-- -- -- --    decRec inl
-- -- -- --      (inr ∘ λ a → T₁.rec isProp⊥ (uncurry λ p* q → a
-- -- -- --        (PosetStr.is-trans (snd P) _ _ _ (pmin p* (snd q)) (fst q))))
-- -- -- --      (snd (p' ≤ᵈ p))
 
-- -- -- --  module _ (Pred : ⟨ P ⟩ → hProp ℓ-zero) where
-- -- -- --   data StrAntiChain : Type₀


-- -- -- --   ∀≮≯ : StrAntiChain → ⟨ P ⟩ → DecProp ℓ-zero

-- -- -- --   data StrAntiChain where
-- -- -- --    [] : StrAntiChain
-- -- -- --    _∷_[_,_]s : (pa : StrAntiChain) →
-- -- -- --      (p : ⟨ P ⟩) → ⟨ Pred p ⟩ → (True (snd (∀≮≯ pa p))) → StrAntiChain

-- -- -- --   sacTail : StrAntiChain → StrAntiChain
-- -- -- --   sacTail [] = []
-- -- -- --   sacTail (x ∷ p [ x₁ , _ ]s) = x

-- -- -- --   isEmptySAC : StrAntiChain →  DecProp ℓ-zero
-- -- -- --   isEmptySAC [] = ((Unit , isPropUnit) , yes _)
-- -- -- --   isEmptySAC (x ∷ p [ _ , _ ]s) = ((⊥ , isProp⊥) , no λ ())

-- -- -- --   isNotEmptySAC : StrAntiChain →  DecProp ℓ-zero
-- -- -- --   isNotEmptySAC [] = ((⊥ , isProp⊥) , no λ ())
-- -- -- --   isNotEmptySAC (x ∷ p [ _ , _ ]s) = ((Unit , isPropUnit) , yes _)

-- -- -- --   -- _∈sac_ : {!!} → StrAntiChain →  DecProp ℓ-zero
-- -- -- --   -- y ∈sac [] = ((⊥ , isProp⊥) , no λ ())
-- -- -- --   -- y ∈sac (xs ∷ x [ p ]s) = DecProp⊔ ({!!} ≤ᵈ x) (y ∈sac xs)


-- -- -- --   ∀≮≯ [] x₁ = ((Unit , isPropUnit) , yes _)
-- -- -- --   ∀≮≯ (xs ∷ x [ _ , _ ]s) y = DecProp⊓ (∀≮≯ xs y) (x ≮≯ y)

  
-- -- -- --   ∀≮≯-≤ : ∀ xs p p' → ⟨ fst (∀≮≯ xs p) L.⇒ (p' ≤ₚ p) L.⇒ fst (∀≮≯ xs p') ⟩ 
-- -- -- --   ∀≮≯-≤ [] p p' x x₁ = tt
-- -- -- --   ∀≮≯-≤ (xs ∷ p₁ [ x₂ , x₃ ]s) p p' x x₁ =
-- -- -- --     ∀≮≯-≤ xs p p' (fst x) x₁ ,
-- -- -- --      ≮≯-≤ _ _ _ (snd x) x₁ 

-- -- -- --   isFull : StrAntiChain → hProp ℓ-zero
-- -- -- --   isFull sac = L.∀[ x ] L.¬ (Pred x L.⊓ fst (∀≮≯ sac x)) 



-- -- -- --   Full : Type₀
-- -- -- --   Full = Σ _ (fst ∘ isFull)


-- -- -- --   sc∀ : (Pred : ⟨ P ⟩ → hProp ℓ-zero) → StrAntiChain → hProp ℓ-zero 
-- -- -- --   sc∀ _ [] = (Unit , isPropUnit)
-- -- -- --   sc∀ Pred (x ∷ p [ x₁ , x₂ ]s) =
-- -- -- --      sc∀ Pred x L.⊓ Pred p

-- -- -- --   sc∃ : (Pred : ⟨ P ⟩ → hProp ℓ-zero) → StrAntiChain → hProp ℓ-zero 
-- -- -- --   sc∃ _ [] = (⊥ , isProp⊥)
-- -- -- --   sc∃ Pred (x ∷ p [ x₁ , x₂ ]s) =
-- -- -- --      sc∃ Pred x L.⊔ Pred p

-- -- -- --   sc∃? : (Pred : ⟨ P ⟩ → DecProp ℓ-zero) → ∀ xs → Dec ⟨ sc∃ (fst ∘ Pred) xs ⟩ 
-- -- -- --   sc∃? Pred [] = no λ ()
-- -- -- --   sc∃? Pred (xs ∷ p [ x , x₁ ]s) =
-- -- -- --     Dec⊔ (sc∃? Pred xs) (snd (Pred p))
  
-- -- -- --   sc∃Dec : (Pred : ⟨ P ⟩ → DecProp ℓ-zero) → StrAntiChain → DecProp ℓ-zero 
-- -- -- --   sc∃Dec Pred xs = sc∃ (fst ∘ Pred) xs , sc∃? Pred xs

-- -- -- --   sc∃⇒ : ∀ {A B} → (∀ x → ⟨ A x ⟩ → ⟨ B x ⟩) → ∀ xs →  ⟨ sc∃ A xs L.⇒ sc∃ B xs ⟩   
-- -- -- --   sc∃⇒ x (xs ∷ p [ x₂ , x₃ ]s) =
-- -- -- --     T₁.map (⊎.map (sc∃⇒ x xs) (x p)) 
  

-- -- -- --   isFull' : StrAntiChain → hProp ℓ-zero
-- -- -- --   isFull' sc = L.∀[ x ] Pred x L.⇒ (L.∃[ y ] sc∃ (λ z → y ≤ₚ z L.⊓ (y ≤ₚ x)) sc)
-- -- -- --     --  (Pred x L.⇒ sc∃ (λ y → L.¬ (x ≮≯ₚ y)) sc)

-- -- -- --   isFull'⇒isFull-lem : ∀ sc x* x**
-- -- -- --      → ⟨ fst (∀≮≯ sc x*) ⟩
-- -- -- --      → ⟨ sc∃ (λ z → (x** ≤ₚ z) L.⊓ (x** ≤ₚ x*)) sc ⟩ → ⊥ 
-- -- -- --   isFull'⇒isFull-lem [] x* x** _ ()
-- -- -- --   isFull'⇒isFull-lem (sc ∷ p [ x , x₁ ]s) x* x** q =
-- -- -- --     T₁.rec isProp⊥
-- -- -- --      (⊎.rec (isFull'⇒isFull-lem sc x* x** (fst q)) λ w → snd q ∣ x** , w ∣₁) 

-- -- -- --   isFull'⇒isFull : ∀ sc → ⟨ isFull' sc L.⇒ isFull sc  ⟩ 
-- -- -- --   isFull'⇒isFull [] x x₁ (y , _) = T₁.rec isProp⊥ (λ x₂ → snd x₂) (x _ y)
-- -- -- --   isFull'⇒isFull (sc ∷ p [ x₃ , x₄ ]s) F' x* q* =
-- -- -- --     T₁.rec isProp⊥
-- -- -- --          (uncurry λ x** →
-- -- -- --            T₁.rec isProp⊥
-- -- -- --              (⊎.rec (isFull'⇒isFull-lem sc x* x** (fst (snd q*)))
-- -- -- --                 λ r** → snd (snd q*) ∣ x** , r** ∣₁))
-- -- -- --          (F' x* (fst q*))  

-- -- -- --   ¬∀≮≯→∃ : ∀ xs p → ⟨ L.¬  fst (∀≮≯ xs p) ⟩
-- -- -- --                   → ⟨ L.∃[ y ] (sc∃ (λ z → y ≤ₚ z L.⊓ (y ≤ₚ p)) xs) ⟩
-- -- -- --   ¬∀≮≯→∃ [] p x = ⊥-elim (x _)
-- -- -- --   ¬∀≮≯→∃ (xs ∷ p₁ [ x₁ , x₂ ]s) p x with p₁ ⊓? p
-- -- -- --   ... | inl x₃ = ∣ fst x₃ , ∣ inr (fst (snd x₃)) ∣₁ ∣₁
-- -- -- --   ... | inr x₃ =
-- -- -- --      let zz = ¬∀≮≯→∃ xs p λ x₄ → x (x₄ , x₃)
-- -- -- --      in T₁.map (λ x₄ → fst x₄ , ∣ inl (snd x₄) ∣₁) zz


-- -- -- --   isFull⇒isFull' : ∀ sc → ⟨ isFull sc L.⇒ isFull' sc  ⟩ 
-- -- -- --   isFull⇒isFull' [] F x q = ∣ x , (F x (q , _)) ∣₁
-- -- -- --   isFull⇒isFull' (sc ∷ p [ x₁ , x₂ ]s) F x q with  (p ⊓? x)
-- -- -- --   ... | inl x₃ = ∣ fst x₃ , ∣ inr (fst (snd x₃)) ∣₁ ∣₁
-- -- -- --   ... | inr x₃ with snd (∀≮≯ sc x)
-- -- -- --   ... | yes p₁ = ⊥-elim (F x (q , (p₁ , x₃)))
-- -- -- --   ... | no ¬p =
-- -- -- --           let zz = ¬∀≮≯→∃ sc x ¬p
-- -- -- --           in T₁.map (λ x₄ → fst x₄ , ∣ inl (snd x₄) ∣₁) zz
      
  
-- -- -- --   isFull'⇔isFull : ∀ sc → ⟨ isFull sc L.⇔ isFull' sc  ⟩
-- -- -- --   isFull'⇔isFull sc = (isFull⇒isFull' sc) , (isFull'⇒isFull sc)
-- -- -- --   -- isFull'⇔isFull [] = (λ x x₁ x₂ → x x₁ ( x₂ , tt)) , λ x x₁ x₂ → x x₁ (fst x₂)
-- -- -- --   -- isFull'⇔isFull (sc ∷ p [ x , x₁ ]s) =
-- -- -- --   --  let (z , z') = isFull'⇔isFull sc
-- -- -- --   --  in (λ x₂ x₃ x₄ →
-- -- -- --   --       let z* = z λ x₅ x₆ → x₂ x₅ (fst x₆ , snd x₆ , {!!})
-- -- -- --   --       in {!!}) ,
-- -- -- --   --      (λ x₂ x₃ x₄ → snd (snd x₄) {!!})
       
-- -- -- --   _⊈⊉_ : StrAntiChain → StrAntiChain → hProp ℓ-zero
-- -- -- --   x ⊈⊉ y = sc∀ (λ y' → fst (∀≮≯ x y')) y


  

-- -- -- --   _++AC_ : (X : StrAntiChain) → (Y : StrAntiChain) → ⟨ X ⊈⊉ Y ⟩ → StrAntiChain

-- -- -- --   ++∀≮≯ : ∀ X Y q x → ⟨ fst (∀≮≯ X x) ⟩
-- -- -- --                     → ⟨ fst (∀≮≯ Y x) ⟩
-- -- -- --                     → ⟨ fst (∀≮≯ (((X ++AC Y) q)) x) ⟩ 

-- -- -- --   (X ++AC []) x = X
-- -- -- --   (X ++AC (Y ∷ p [ x₁ , x₂ ]s)) x =
-- -- -- --     ((X ++AC Y) (fst x)) ∷ p [ x₁ ,
-- -- -- --      fromWitness (++∀≮≯ X Y (fst x) p (snd x) (toWitness x₂)) ]s

-- -- -- --   ++∀≮≯ X [] q x x₁ x₂ = x₁
-- -- -- --   ++∀≮≯ X (Y ∷ p [ x₃ , x₄ ]s) q x x₁ x₂ =
-- -- -- --     (++∀≮≯ X Y (fst q) x x₁ (fst x₂)) , snd x₂

-- -- -- --   sc∃++ : (Pred : ⟨ P ⟩ → hProp ℓ-zero) →
-- -- -- --            ∀ X Y q 
-- -- -- --              → ⟨ sc∃ Pred X L.⊔  sc∃ Pred Y ⟩ 
-- -- -- --              → ⟨ sc∃ Pred (_++AC_ X Y q)⟩  
-- -- -- --   sc∃++ Pred X [] q = T₁.rec (snd (sc∃ Pred X)) (⊎.rec (idfun _) λ ())
-- -- -- --   sc∃++ Pred X Y'@(Y ∷ p [ x₁ , x₂ ]s) q =
-- -- -- --      T₁.map (⊎.map (sc∃++ Pred X Y (fst q)) (idfun _))
-- -- -- --      ∘ L.pathTo⇒ (L.⊔-assoc (sc∃ Pred X) (sc∃ Pred Y) (Pred p)) 

-- -- -- --  -- sc∀→SAC⊓ : (Pred Pred' : ⟨ P ⟩ → hProp ℓ-zero)
-- -- -- --  --           → (x : StrAntiChain Pred) 
-- -- -- --  --           → ⟨ sc∀ _ Pred' x ⟩ 
-- -- -- --  --           → StrAntiChain λ x' → Pred x' L.⊓ Pred' x'
-- -- -- --  -- sc∀→SAC⊓ = {!∀≮≯-≤!}


-- -- -- --  -- SAC→sc∀ : (Pred Pred' : ⟨ P ⟩ → hProp ℓ-zero)
-- -- -- --  --           → (∀ x → ⟨ Pred x ⟩ → ⟨ Pred' x ⟩ )
-- -- -- --  --           → (x : StrAntiChain Pred)                       
-- -- -- --  --           → ⟨ sc∀ Pred Pred' x ⟩
-- -- -- --  -- SAC→sc∀ = {!!}


-- -- -- --   isInSAC : ⟨ P ⟩ → StrAntiChain → hProp ℓ-zero
-- -- -- --   isInSAC p = sc∃ (p L.≡ₚ_)

-- -- -- --   ∈SAC : ⟨ P ⟩ → StrAntiChain → DecProp ℓ-zero
-- -- -- --   ∈SAC p = sc∃Dec (p ≤ᵈ_ )

-- -- -- --   ¬-∈SAC-∅ : ∀ p xs → ⟨ L.¬ (  fst (isEmptySAC xs)  L.⊓  fst (∈SAC p xs)  ) ⟩   
-- -- -- --   ¬-∈SAC-∅ p [] ()
-- -- -- --   ¬-∈SAC-∅ p (xs ∷ p₁ [ x₁ , x₂ ]s) ()
  
-- -- -- --   min∉SAC→∀≮≯ : ∀ p xs → ⟨ minimal p ⟩
-- -- -- --          → ⟨ L.¬ fst (∈SAC p xs) ⟩
-- -- -- --          → ⟨ fst (∀≮≯ xs p) ⟩
-- -- -- --   min∉SAC→∀≮≯ p [] x x₁ = tt
-- -- -- --   min∉SAC→∀≮≯ p (xs ∷ p₁ [ x₂ , x₃ ]s) x x₁ =
-- -- -- --     (min∉SAC→∀≮≯ p xs x (x₁ ∘ ∣_∣₁ ∘ inl)) ,
-- -- -- --      x₁ ∘ T₁.map (uncurry λ p' q →
-- -- -- --        inr (PosetStr.is-trans (snd P) p p' p₁ (x p' (snd q)) (fst q) )  )
    

-- -- -- --  ─Ty : Type₀ 
-- -- -- --  ─Ty = ∀ x y → Full λ z → z ≤ₚ x L.⊓ (z ≮≯ₚ y)

-- -- -- --  -- module _ (_─_ : ─Ty)
-- -- -- --  --          (A : ⟨ P ⟩ → hProp ℓ-zero)
-- -- -- --  --          (f : ∀ x y → ⟨ x ≤ₚ y ⟩ → ⟨ A y ⟩ → ⟨ A x ⟩ ) where

-- -- -- --  --  _─*_ : ∀ x y → ⟨ A x ⟩ → Full λ z → A x L.⊓ z ≤ₚ x L.⊓ (z ≮≯ₚ y)
-- -- -- --  --  _─*_ x y q = {!!}
-- -- -- --  --   where
-- -- -- --  --    w : ∀ xs → ⟨ isFull (λ z → z ≤ₚ x L.⊓ (z ≮≯ₚ y)) xs ⟩
-- -- -- --  --        → Full λ z → A x L.⊓ z ≤ₚ x L.⊓ (z ≮≯ₚ y)
-- -- -- --  --    w [] p = [] , λ y → p y ∘ λ a → snd (fst a) , _
-- -- -- --  --    w (xs ∷ p₁ [ x , x₁ ]s) p =
-- -- -- --  --     let (v , v') = w xs λ y → p y ∘ map-snd λ x₃ → x₃ , {!!}
-- -- -- --  --     in (v ∷ p₁ [ (f _ _ {!x!} {!!}) , {!!} , {!!} ]s ) , {!!}
 
-- -- -- --  -- ─Ty¬∅ : ∀ x y sc →
-- -- -- --  --          ⟨ (isFull (λ z → z ≤ₚ x L.⊓ (z ≮≯ₚ y)) sc) ⟩
-- -- -- --  --          → ∀ v →
-- -- -- --  --          ⟨ v ≮≯ₚ y ⟩ → ⟨ v ≤ₚ x ⟩
-- -- -- --  --          → ⟨ sc∃ _ {!!} sc ⟩ 
-- -- -- --  -- ─Ty¬∅ = {!!}
-- -- -- --   -- AC─ : (StrAntiChain λ _ → Unit , isPropUnit) → 
-- -- -- --   --        Σ _ λ sc → ⟨ sc∀ (λ _ → Unit , isPropUnit) (λ p' → p' ≮≯ₚ p) sc ⟩    
-- -- -- --   -- AC─ [] = [] , tt
-- -- -- --   -- AC─ (xs ∷ p' [ x₁ , x₂ ]s) =
-- -- -- --   --  let (xx , yy) = AC─ xs
-- -- -- --   --      (xx' , yy') = p ─ p'  
-- -- -- --   --  in _++AC_ (λ _ → Unit , isPropUnit) xx {!xx'!} {!!} , {!!}  
 
-- -- -- --  MaxSAC : Type₀ 
-- -- -- --  MaxSAC = Full λ _ → (Unit , isPropUnit)


-- -- -- --  mapSAC : ∀ {A B} → (∀ x → ⟨ A x ⟩ → ⟨ B x ⟩)
-- -- -- --               →  StrAntiChain A → StrAntiChain B

-- -- -- --  map∀≮≯  : ∀ {A B} → (f : ∀ x → ⟨ A x ⟩ → ⟨ B x ⟩)
-- -- -- --               → ∀ xs p
-- -- -- --               → ⟨ fst (∀≮≯ A xs p) ⟩
-- -- -- --               → ⟨ fst (∀≮≯ B (mapSAC f xs) p) ⟩ 

-- -- -- --  map∀≮≯'  : ∀ {A B} → (f : ∀ x → ⟨ A x ⟩ → ⟨ B x ⟩)
-- -- -- --               → ∀ xs p
-- -- -- --               → ⟨ fst (∀≮≯ B (mapSAC f xs) p) ⟩
-- -- -- --               → ⟨ fst (∀≮≯ A xs p) ⟩ 

-- -- -- --  mapSAC _ [] = []
-- -- -- --  mapSAC f (x₁ ∷ p [ x₂ , x₃ ]s) =
-- -- -- --   (mapSAC f x₁) ∷ p [ f _ x₂ ,
-- -- -- --     fromWitness (map∀≮≯ f x₁ p (toWitness x₃)) ]s

-- -- -- --  map∀≮≯ f [] p x = tt
-- -- -- --  map∀≮≯ f (xs ∷ p₁ [ x₁ , x₂ ]s) p x =
-- -- -- --   (map∀≮≯ f xs p (fst x)) , snd x

-- -- -- --  map∀≮≯' f [] p x = tt
-- -- -- --  map∀≮≯' f (xs ∷ p₁ [ x₁ , x₂ ]s) p x =
-- -- -- --    (map∀≮≯' f xs p (fst x)) , snd x

-- -- -- --  sc∃mapSAC : ∀ {A B} Pred f xs → ⟨ sc∃ A Pred xs  ⟩
-- -- -- --                              → ⟨ sc∃ B Pred (mapSAC f xs )  ⟩
-- -- -- --  sc∃mapSAC Pred f (xs ∷ p [ x₁ , x₂ ]s) =
-- -- -- --    T₁.map (⊎.map (sc∃mapSAC Pred f xs) (idfun _))

-- -- -- --  sc∃mapSAC⁻ : ∀ {A B} Pred f xs → ⟨ sc∃ B Pred (mapSAC f xs )  ⟩
-- -- -- --                                 → ⟨ sc∃ A Pred xs  ⟩
                             
-- -- -- --  sc∃mapSAC⁻ Pred f (xs ∷ p [ x₁ , x₂ ]s) = 
-- -- -- --    T₁.map (⊎.map (sc∃mapSAC⁻ Pred f xs) (idfun _))


-- -- -- --  module AC─ (_─_ : ─Ty) (p : ⟨ P ⟩) where


-- -- -- --   AC─hlp : ∀ xs
-- -- -- --                → (p' : ⟨ P ⟩) → ∀ ys
-- -- -- --                → ⟨ fst (∀≮≯ _ xs p') ⟩  → ⟨ ((_≮≯ₚ p) ⊈⊉ xs) (mapSAC (λ _ → snd) ys) ⟩
-- -- -- --   AC─hlp xs p' [] _ = tt
-- -- -- --   AC─hlp xs p' (ys ∷ p [ x , x₁ ]s) xx =
-- -- -- --      (AC─hlp xs p' ys xx) , ∀≮≯-≤ _ xs p' p xx (fst x) 


-- -- -- --   AC─ : (StrAntiChain λ _ → Unit , isPropUnit) → (StrAntiChain (_≮≯ₚ p))

-- -- -- --   AC─∀≮≯ : ∀ xs p' → ⟨ fst (∀≮≯ _ xs p')  ⟩  → ⟨ fst (∀≮≯ (λ v → v ≮≯ₚ p) (AC─ xs) p') ⟩


-- -- -- --   AC─ [] = []
-- -- -- --   AC─ (xs ∷ p' [ x₁ , x₂ ]s) =
-- -- -- --       let (xx' , yy') = p' ─ p
-- -- -- --       in  _++AC_ _ (AC─ xs)
-- -- -- --                 (mapSAC (λ _ → snd) xx')
-- -- -- --                 (AC─hlp (AC─ xs) p' xx' (AC─∀≮≯ xs p' (toWitness x₂)) )

-- -- -- --   AC─∀≮≯ [] p' _ = tt
-- -- -- --   AC─∀≮≯ (xs ∷ p' [ x₁ , x₂ ]s) p* q =
-- -- -- --     let (xx' , yy') = p' ─ p
-- -- -- --     in ++∀≮≯ (_≮≯ₚ p) (AC─ xs) ((mapSAC (λ _ → snd) xx'))
-- -- -- --          _ p* (AC─∀≮≯ xs p* (fst q))
-- -- -- --           (map∀≮≯ (λ _ → snd) xx' p*
-- -- -- --            (hh xx' ))
-- -- -- --     where
-- -- -- --     hh : (xs : StrAntiChain (λ z → (z ≤ₚ p') L.⊓ (z ≮≯ₚ p))) →
-- -- -- --             ⟨ fst (∀≮≯ _ xs p*) ⟩ 
-- -- -- --     hh [] = tt
-- -- -- --     hh (xs ∷ p [ x , x₁ ]s) =
-- -- -- --      hh xs , ≤-≮≯ _ _ _ (snd q) (fst x)

-- -- -- --   AC─full' : ∀ xs → ⟨ isFull' _ xs ⟩
-- -- -- --                  → ⟨ isFull' _ (AC─ xs) ⟩


-- -- -- --   AC─full'-lem : ∀ xs x x≮≯ₚp
-- -- -- --     → (x₁ : ⟨ P ⟩)
-- -- -- --       → (
-- -- -- --          ⟨ sc∃ (λ v → Unit , isPropUnit) (λ z → (x₁ ≤ₚ z) L.⊓ (x₁ ≤ₚ x)) xs
-- -- -- --          ⟩) →
-- -- -- --       ∥ Σ ⟨ P ⟩
-- -- -- --       (λ x₁ → ⟨ sc∃ (_≮≯ₚ p) (λ z → (x₁ ≤ₚ z) L.⊓ (x₁ ≤ₚ x)) (AC─ xs) ⟩) ∥₁
-- -- -- --   AC─full'-lem (xs ∷ p' [ x₂ , x₃ ]s) x x≮≯ₚp x₁ = 
-- -- -- --      let (xx' , yy') = p' ─ p
-- -- -- --          F' : fst (isFull' (λ z → (z ≤ₚ p') L.⊓ (z ≮≯ₚ p)) (fst (p' ─ p)))
-- -- -- --          F' = isFull⇒isFull' _ (fst (p' ─ p)) (snd (p' ─ p))
-- -- -- --      in T₁.rec squash₁
-- -- -- --          (⊎.rec (λ q* →
-- -- -- --               let qq = AC─full'-lem xs x x≮≯ₚp x₁ q*
-- -- -- --               in T₁.map
-- -- -- --                   (λ x₄ →
-- -- -- --                      fst x₄ ,
-- -- -- --                       sc∃++ (_≮≯ₚ p) _
-- -- -- --                      (AC─ xs)
-- -- -- --                      (mapSAC (λ _ → snd) xx')
-- -- -- --                      _ ∣ inl (snd x₄) ∣₁ )
-- -- -- --                       qq)
-- -- -- --             λ q* →
-- -- -- --                let qq = F' x₁ (fst q* , ≤-≮≯ _ _ _ x≮≯ₚp (snd q*))
-- -- -- --                in T₁.map (λ x₄ → fst x₄ ,
-- -- -- --                    sc∃++ (_≮≯ₚ p) _
-- -- -- --                      (AC─ xs)
-- -- -- --                      (mapSAC (λ _ → snd) xx')
-- -- -- --                      _
-- -- -- --                      ∣ inr (sc∃mapSAC {B = (_≮≯ₚ p)} (λ z → (fst x₄ ≤ₚ z) L.⊓ (fst x₄ ≤ₚ x))
-- -- -- --                                 (λ _ → snd) (fst (p' ─ p))
-- -- -- --                                  (sc∃⇒ _
-- -- -- --                               (λ _ → map-snd
-- -- -- --                                 λ x* →
-- -- -- --                                  PosetStr.is-trans (snd P) _ _ _ x* (snd q*))
-- -- -- --                                ((fst (p' ─ p))) (snd x₄))) ∣₁) qq)
                


-- -- -- --   AC─full' xs F x x≮≯ₚp = 
-- -- -- --     T₁.rec squash₁ (uncurry (AC─full'-lem xs x x≮≯ₚp)) (F x _)

-- -- -- --   AC─full : ∀ xs → ⟨ isFull _ xs ⟩
-- -- -- --                  → ⟨ isFull _ (AC─ xs) ⟩
-- -- -- --   AC─full xs = isFull'⇒isFull _ (AC─ xs) ∘  AC─full' xs ∘ isFull⇒isFull' _ xs

-- -- -- --   AC─' : (StrAntiChain λ _ → Unit , isPropUnit) → (StrAntiChain λ _ → Unit , isPropUnit)
-- -- -- --   AC─' = mapSAC (λ x _ → tt)  ∘ AC─

  
-- -- -- --   stillIn : ∀ sac p* → ⟨ minimal p* ⟩  → ⟨ p ≮≯ₚ p* ⟩ →
-- -- -- --                   ⟨ fst (∈SAC _ p* sac) ⟩
-- -- -- --                 → ⟨ fst (∈SAC _ p* (AC─' sac)) ⟩
-- -- -- --   stillIn (xs ∷ p' [ x₁ , x₂ ]s) p* x* x₁* x₂* =
-- -- -- --    let (xx' , yy') = p' ─ p
-- -- -- --        achlp = (AC─hlp (AC─ xs) p' xx' (AC─∀≮≯ xs p' (toWitness x₂)) )
-- -- -- --        yyys = (mapSAC (λ _ → snd) xx')
-- -- -- --        xxxs = _++AC_ _ (AC─ xs)
-- -- -- --                 yyys
-- -- -- --                 achlp

-- -- -- --    in sc∃mapSAC _ (λ x _ → tt)
-- -- -- --     xxxs (sc∃++ _ _ (AC─ xs) yyys achlp
-- -- -- --           (T₁.map 
-- -- -- --             (⊎.map ((sc∃mapSAC⁻ _ (λ x _ → tt) (AC─ xs)) ∘ (stillIn xs p* x* x₁*))
-- -- -- --                λ y →
-- -- -- --                  sc∃mapSAC _ (λ _ → snd) xx'
-- -- -- --                    (decRec (idfun _)
-- -- -- --                      (⊥-rec ∘ yy' p* ∘
-- -- -- --                        λ a → (y , ≮≯-sym _ _ x₁*) ,
-- -- -- --                          min∉SAC→∀≮≯ _ p* xx' x* a )
-- -- -- --                      (snd (∈SAC _ p* xx'))))
-- -- -- --               x₂*))
  
-- -- -- --  -- module AC─* (_─_ : ─Ty) (A : ⟨ P ⟩ → hProp ℓ-zero) (p : ⟨ P ⟩) where


-- -- -- --  --  AC─hlp : ∀ xs
-- -- -- --  --               → (p' : ⟨ P ⟩) → ∀ ys
-- -- -- --  --               → ⟨ fst (∀≮≯ _ xs p') ⟩  → ⟨ ((_≮≯ₚ p) ⊈⊉ xs) (mapSAC (λ _ → snd) ys) ⟩
-- -- -- --  --  AC─hlp xs p' [] _ = tt
-- -- -- --  --  AC─hlp xs p' (ys ∷ p [ x , x₁ ]s) xx =
-- -- -- --  --     (AC─hlp xs p' ys xx) , ∀≮≯-≤ _ xs p' p xx (fst x) 


-- -- -- --  --  AC─ : (StrAntiChain A) → (StrAntiChain (λ x → (A x) L.⊓ x ≮≯ₚ p))

-- -- -- --  --  AC─∀≮≯ : ∀ xs p' → ⟨ fst (∀≮≯ _ xs p')  ⟩  → ⟨ fst (∀≮≯ _ (AC─ xs) p') ⟩


-- -- -- --  --  AC─ [] = []
-- -- -- --  --  AC─ (xs ∷ p' [ x₁ , x₂ ]s) = 
-- -- -- --  --      let (xx' , yy') = p' ─ p
-- -- -- --  --      in  _++AC_ _ (AC─ xs)
-- -- -- --  --                (mapSAC (λ _ → snd) xx')
-- -- -- --  --                (AC─hlp (AC─ xs) p' xx' (AC─∀≮≯ xs p' (toWitness x₂)) )

-- -- -- --  --  AC─∀≮≯ [] p' _ = tt
-- -- -- --  --  AC─∀≮≯ (xs ∷ p' [ x₁ , x₂ ]s) p* q = 
-- -- -- --  --    let (xx' , yy') = p' ─ p
-- -- -- --  --    in ++∀≮≯ (_≮≯ₚ p) (AC─ xs) ((mapSAC (λ _ → snd) xx'))
-- -- -- --  --         _ p* (AC─∀≮≯ xs p* (fst q))
-- -- -- --  --          (map∀≮≯ (λ _ → snd) xx' p*
-- -- -- --  --           (hh xx' ))
-- -- -- --  --    where
-- -- -- --  --    hh : (xs : StrAntiChain (λ z → (z ≤ₚ p') L.⊓ (z ≮≯ₚ p))) →
-- -- -- --  --            ⟨ fst (∀≮≯ _ xs p*) ⟩ 
-- -- -- --  --    hh [] = tt
-- -- -- --  --    hh (xs ∷ p [ x , x₁ ]s) =
-- -- -- --  --     hh xs , ≤-≮≯ _ _ _ (snd q) (fst x)

-- -- -- --  --  AC─full' : ∀ xs → ⟨ isFull' _ xs ⟩
-- -- -- --  --                 → ⟨ isFull' _ (AC─ xs) ⟩


-- -- -- --  --  AC─full'-lem : ∀ xs x x≮≯ₚp
-- -- -- --  --    → (x₁ : ⟨ P ⟩)
-- -- -- --  --      → (
-- -- -- --  --         ⟨ sc∃ A (λ z → (x₁ ≤ₚ z) L.⊓ (x₁ ≤ₚ x)) xs
-- -- -- --  --         ⟩) → ∥
-- -- -- --  --                Σ ⟨ P ⟩
-- -- -- --  --                (λ x₂ →
-- -- -- --  --                   ⟨
-- -- -- --  --                   sc∃ (λ x₃ → A x₃ L.⊓ (x₃ ≮≯ₚ p)) (λ z → (x₂ ≤ₚ z) L.⊓ (x₂ ≤ₚ x))
-- -- -- --  --                   (AC─ xs)
-- -- -- --  --                   ⟩)
-- -- -- --  --                ∥₁

-- -- -- --  --  -- AC─full'-lem = {!!}
-- -- -- --  --  AC─full'-lem (xs ∷ p' [ x₂ , x₃ ]s) x x≮≯ₚp x₁ = {!!}
-- -- -- --  --     -- let (xx' , yy') = p' ─ p
-- -- -- --  --     --     F' : fst (isFull' (λ z → (z ≤ₚ p') L.⊓ (z ≮≯ₚ p)) (fst (p' ─ p)))
-- -- -- --  --     --     F' = isFull⇒isFull' _ (fst (p' ─ p)) (snd (p' ─ p))
-- -- -- --  --     -- in T₁.rec squash₁
-- -- -- --  --     --     (⊎.rec (λ q* →
-- -- -- --  --     --          let qq = AC─full'-lem xs x x≮≯ₚp x₁ q*
-- -- -- --  --     --          in T₁.map
-- -- -- --  --     --              (λ x₄ →
-- -- -- --  --     --                 fst x₄ ,
-- -- -- --  --     --                  sc∃++ (_≮≯ₚ p) _
-- -- -- --  --     --                 (AC─ xs)
-- -- -- --  --     --                 (mapSAC (λ _ → snd) xx')
-- -- -- --  --     --                 _ ∣ inl (snd x₄) ∣₁ )
-- -- -- --  --     --                  qq)
-- -- -- --  --     --        λ q* →
-- -- -- --  --     --           let qq = F' x₁ (fst q* , ≤-≮≯ _ _ _ x≮≯ₚp (snd q*))
-- -- -- --  --     --           in T₁.map (λ x₄ → fst x₄ ,
-- -- -- --  --     --               sc∃++ (_≮≯ₚ p) _
-- -- -- --  --     --                 (AC─ xs)
-- -- -- --  --     --                 (mapSAC (λ _ → snd) xx')
-- -- -- --  --     --                 _
-- -- -- --  --     --                 ∣ inr (sc∃mapSAC {B = (_≮≯ₚ p)} (λ z → (fst x₄ ≤ₚ z) L.⊓ (fst x₄ ≤ₚ x))
-- -- -- --  --     --                            (λ _ → snd) (fst (p' ─ p))
-- -- -- --  --     --                             (sc∃⇒ _
-- -- -- --  --     --                          (λ _ → map-snd
-- -- -- --  --     --                            λ x* →
-- -- -- --  --     --                             PosetStr.is-trans (snd P) _ _ _ x* (snd q*))
-- -- -- --  --     --                           ((fst (p' ─ p))) (snd x₄))) ∣₁) qq)
                


-- -- -- --  --  AC─full' xs F x x≮≯ₚp = 
-- -- -- --  --    T₁.rec squash₁ (uncurry (AC─full'-lem xs x x≮≯ₚp)) (F x _)

-- -- -- --  --  AC─full : ∀ xs → ⟨ isFull _ xs ⟩
-- -- -- --  --                 → ⟨ isFull _ (AC─ xs) ⟩
-- -- -- --  --  AC─full xs = isFull'⇒isFull _ (AC─ xs) ∘  AC─full' xs ∘ isFull⇒isFull' _ xs


-- -- -- -- module _ {POA POB : Poset ℓ-zero ℓ-zero}
-- -- -- --     {DPA : DecPoset POA}
-- -- -- --     {DPB : DecPoset POB}
-- -- -- --     {P : ⟨ POA ⟩ → hProp ℓ-zero}
-- -- -- --     {Q : ⟨ POB ⟩ → hProp ℓ-zero}
-- -- -- --     (f : ⟨ POA ⟩ → ⟨ POB ⟩)
-- -- -- --     (g : ∀ x → ⟨ P x ⟩ → ⟨ Q (f x) ⟩)
    
-- -- -- --     where

-- -- -- --  module DA = DecPoset DPA
-- -- -- --  module DB = DecPoset DPB

-- -- -- --  SAC-poset-map : (pres≮≯ : ∀ x y → ⟨ x DA.≮≯ₚ y  L.⇒ ((f x) DB.≮≯ₚ (f y)) ⟩ ) → 
-- -- -- --       DA.StrAntiChain P → DB.StrAntiChain Q

-- -- -- --  SAC-poset-map∀≮≯ : ∀ pres≮≯ xs p 
-- -- -- --               → ⟨ fst (DA.∀≮≯ P xs p) ⟩
-- -- -- --               → ⟨ fst (DB.∀≮≯ Q (SAC-poset-map pres≮≯ xs) (f p)) ⟩

-- -- -- --  SAC-poset-map pres≮≯ DecPoset.[] = DecPoset.[]
-- -- -- --  SAC-poset-map pres≮≯ (x DecPoset.∷ p [ x₁ , x₂ ]s) =
-- -- -- --     (SAC-poset-map pres≮≯ x) DecPoset.∷ (f p)
-- -- -- --       [ g _ x₁ , fromWitness (SAC-poset-map∀≮≯ pres≮≯ x p (toWitness x₂))  ]s

-- -- -- --  SAC-poset-map∀≮≯ pres≮≯ DecPoset.[] p x = tt
-- -- -- --  SAC-poset-map∀≮≯ pres≮≯ (xs DecPoset.∷ p₁ [ x₁ , x₂ ]s) p x =
-- -- -- --    SAC-poset-map∀≮≯ pres≮≯ xs p (fst x) ,  (pres≮≯ _ _) (snd x)

-- -- -- --  SAC-poset-map∀≮≯⁻ : ∀ pres≮≯
-- -- -- --     (pres≮≯' : ∀ x y → ⟨ ((f x) DB.≮≯ₚ (f y))  L.⇒ x DA.≮≯ₚ y ⟩)
-- -- -- --               →  ∀ xs p 
-- -- -- --               → ⟨ fst (DB.∀≮≯ Q (SAC-poset-map pres≮≯ xs) (f p)) ⟩
-- -- -- --               → ⟨ fst (DA.∀≮≯ P xs p) ⟩

-- -- -- --  SAC-poset-map∀≮≯⁻ pres≮≯ pres≮≯' DecPoset.[] p x = tt
-- -- -- --  SAC-poset-map∀≮≯⁻ pres≮≯ pres≮≯' (xs DecPoset.∷ p₁ [ x₁ , x₂ ]s) p x =
-- -- -- --    SAC-poset-map∀≮≯⁻ pres≮≯ pres≮≯' xs p (fst x) ,
-- -- -- --      pres≮≯' _ _ (snd x)


-- -- -- --  sc∃-SAC-poset-map : ∀ A B pres≮≯ 
-- -- -- --     → (∀ x → ⟨ A x ⟩ → ⟨ P x ⟩ → ⟨ Q (f x) ⟩ → ⟨ B (f x) ⟩)
-- -- -- --     → ∀ xs
-- -- -- --     → ⟨ DA.sc∃ P A xs ⟩
-- -- -- --     → ⟨ DB.sc∃ Q B (SAC-poset-map pres≮≯ xs) ⟩ 
-- -- -- --  sc∃-SAC-poset-map A B pres≮≯ f (xs DecPoset.∷ p [ x₂ , x₃ ]s) =
-- -- -- --   T₁.map
-- -- -- --     (⊎.map (sc∃-SAC-poset-map A B pres≮≯ f xs) λ a → f p a x₂ (g p x₂))



-- -- -- -- --  -- [_─_]⊂⊃[_] : ⟨ P ⟩ → ⟨ P ⟩ → StrAntiChain → hProp ℓ-zero
-- -- -- -- --  -- [ x ─ y ]⊂⊃[ sac ] =
-- -- -- -- --  --    {!!}
-- -- -- -- --  --   -- L.∀[ z ] (((z ≤ₚ x) L.⊔ (z ≤ₚ y))
-- -- -- -- --  --   --         L.⇔ (fst (z ∈sac sac)))
 
-- -- -- -- --  -- _─_ : (x y : ⟨ P ⟩) → Σ StrAntiChain
-- -- -- -- --  --                        λ sac → ⟨ [ x ─ y ]⊂⊃[ sac ] ⟩ 
-- -- -- -- --  -- _─_ = {!!}

-- -- -- -- --  ∀inSAC : (Atom → hProp ℓ-zero) → StrAntiChain → hProp ℓ-zero 
-- -- -- -- --  ∀inSAC P [] = (Unit , isPropUnit) 
-- -- -- -- --  ∀inSAC P (sac ∷ p [ _ ]s) = (∀inSAC P sac) L.⊓ (L.∀[ x ] (fromAtom x ≤ₚ p L.⇒ P x  ))

-- -- -- -- --  ∀inSAC-tail : ∀ P sac → ⟨ ∀inSAC P sac L.⇒ ∀inSAC P (sacTail sac) ⟩
-- -- -- -- --  ∀inSAC-tail P [] x = tt
-- -- -- -- --  ∀inSAC-tail P (sac ∷ p [ x₁ ]s) = fst

-- -- -- --  -- AC++ : (sc sc' : StrAntiChain) → ⟨ ∀inSAC (L.¬_ ∘ fst ∘ (_∈sac sc) ) sc' ⟩ → StrAntiChain
-- -- -- --  -- AC++ sc [] x = sc
-- -- -- --  -- AC++ sc (sc' ∷ y [ x₁ ]s) x =
-- -- -- --  --   (AC++ sc sc' (fst x)) ∷ y [ fromWitness {!snd x!} ]s
-- -- -- --  -- -- AC++ [] sc' _ = sc'
-- -- -- --  -- -- AC++ (xs ∷ x [ p ]s) sc' q =
-- -- -- --  -- --   AC++ xs (sc' ∷ x [ fromWitness {!toWitness p!} ]s) ({!q!} , {!!})
-- -- -- --  -- -- AC++ (sc ∷ p [ x₁ ]s) (sc' ∷ p₁ [ x₂ ]s) x = {!!}


-- -- -- -- --  DecScan : Type (ℓ-suc ℓ-zero)
-- -- -- -- --  DecScan =
-- -- -- -- --    (p : Atom → DecProp ℓ-zero)
-- -- -- -- --    (mbDecP : ∀ x → Maybe ( (
-- -- -- -- --          (∀ a → ⟨ (fromAtom a ≤ₚ x) L.⇒ fst (p a)  ⟩)
-- -- -- -- --        ⊎ (∀ a → ⟨ (fromAtom a ≤ₚ x) L.⇒ L.¬ (fst (p a)) ⟩) )))
-- -- -- -- --       → Σ StrAntiChain
-- -- -- -- --          λ sac → ∀ a → ⟨  fst (a ∈sac sac) L.⇔ fst (p a) ⟩ 

-- -- -- -- --  ∀DecScan : ∀  (p : Atom → DecProp ℓ-zero) sac → (∀ a → ⟨  fst (a ∈sac sac) L.⇒ fst (p a) ⟩)
-- -- -- -- --               → ⟨ ∀inSAC (fst ∘ p) sac ⟩ 
-- -- -- -- --  ∀DecScan P [] _ = tt
-- -- -- -- --  ∀DecScan P (xs ∷ x [ p ]s) q =
-- -- -- -- --     ∀DecScan P xs ((_∘ ∣_∣₁ ∘ inr) ∘ q) , ((_∘ ∣_∣₁ ∘ inl)) ∘ q
      
 
-- -- -- -- module _ (Pat : Type)
-- -- -- --        (PO : PosetStr ℓ-zero Pat)
-- -- -- --        (DP :  DecPoset (_ , PO))
        
-- -- -- --        where

-- -- -- --  open PosetStr
-- -- -- --  open IsPoset
-- -- -- --  open DecPoset


-- -- -- --  _≤ℙ_ : ℙ Pat → ℙ Pat → DecProp ℓ-zero
-- -- -- --  x ≤ℙ ₋₋ = ((Unit , isPropUnit) , yes _)
-- -- -- --  ₋₋ ≤ℙ ⌞_ x₁ = ((⊥ , isProp⊥) , no λ ())
-- -- -- --  ⌞_ x ≤ℙ ⌞_ x₁ = (_≤ᵈ_ DP) x x₁
 
-- -- -- --  Posetℙ : PosetStr ℓ-zero (ℙ Pat)
-- -- -- --  Posetℙ = w
-- -- -- --   where
  
-- -- -- --   w : PosetStr ℓ-zero (ℙ Pat)
-- -- -- --   PosetStr._≤_ w = λ x y → fst (fst (x ≤ℙ y))
-- -- -- --   is-set (isPoset w) = ℙ.isOfHLevelMaybe 0 (is-set PO)
-- -- -- --   is-prop-valued (isPoset w) = λ x y → snd (fst (x ≤ℙ y)) 
-- -- -- --   is-refl (isPoset w) ₋₋ = tt
-- -- -- --   is-refl (isPoset w) (⌞_ x) = is-refl (isPoset PO) x
-- -- -- --   is-trans (isPoset w) a b ₋₋ x x₁ = tt
-- -- -- --   is-trans (isPoset w) (⌞_ a) (⌞_ b) (⌞_ c) x x₁ =
-- -- -- --      is-trans (isPoset PO) a b c x x₁
-- -- -- --   is-antisym (isPoset w) ₋₋ ₋₋ x x₁ = refl
-- -- -- --   is-antisym (isPoset w) (⌞_ a) (⌞_ b) x x₁ =
-- -- -- --     cong (⌞_) (is-antisym (isPoset PO) a b x x₁)

-- -- -- --  DecPosetℙ : DecPoset (_ , Posetℙ)
-- -- -- --  patOrdDec DecPosetℙ = λ x y → snd (x ≤ℙ y) 
-- -- -- --  (DecPosetℙ ⊓? ₋₋) ₋₋ = inl (₋₋ , _)
-- -- -- --  (DecPosetℙ ⊓? ₋₋) (⌞_ x) = inl (⌞ x , (_ , is-refl (isPoset PO) x) , z)
-- -- -- --   where
-- -- -- --    z : (x₁ : ℙ Pat) →
-- -- -- --          Σ Unit (λ _ → fst (fst (x₁ ≤ℙ (⌞ x)))) → fst (fst (x₁ ≤ℙ (⌞ x)))
-- -- -- --    z (⌞_ x₁) = snd

-- -- -- --  (DecPosetℙ ⊓? ⌞_ x) ₋₋ = inl (⌞ x , (is-refl (isPoset PO) x , _) , z)
-- -- -- --   where
-- -- -- --    z : (x₁ : ℙ Pat) → _
-- -- -- --    z (⌞_ x₁) = fst
-- -- -- --  (DecPosetℙ ⊓? ⌞_ x) (⌞_ x₁) =
-- -- -- --     ⊎.map z (_∘ T₁.map z') (_⊓?_ DP x x₁) 
-- -- -- --    where
-- -- -- --     z : _
-- -- -- --     fst (z (y , _)) = ⌞ y
-- -- -- --     fst (snd (z (y , q))) = fst q
-- -- -- --     snd (snd (z (y , q))) (⌞_ x) x₁ = snd q x x₁

-- -- -- --     z' : _
-- -- -- --     z' (⌞_ x , q) = x , q

-- -- -- --  Predℙ : (Pat → hProp ℓ-zero) → (ℙ Pat → hProp ℓ-zero) 
-- -- -- --  Predℙ = ℙ.rec (⊥ , isProp⊥) 

-- -- -- --  StrAntiChainℙ : ∀ {P} →  StrAntiChain DP P → StrAntiChain DecPosetℙ (Predℙ P)

-- -- -- --  ∀≮≯ℙ : ∀ {P} x p → (fst (fst (∀≮≯ DP P x p)))
-- -- -- --        → fst (fst (∀≮≯ DecPosetℙ (Predℙ P) (StrAntiChainℙ x) (⌞ p)) )

-- -- -- --  ∀≮≯ℙ' : ∀ {P} x p 
-- -- -- --        → fst (fst (∀≮≯ DecPosetℙ (Predℙ P) (StrAntiChainℙ x) (⌞ p)) )
-- -- -- --        → (fst (fst (∀≮≯ DP P x p)))
 

-- -- -- --  StrAntiChainℙ [] = []
-- -- -- --  StrAntiChainℙ (x ∷ p [ xx , x₁ ]s) = StrAntiChainℙ x ∷ ⌞ p [ xx , fromWitness (∀≮≯ℙ x p (toWitness x₁)) ]s

-- -- -- --  ∀≮≯ℙ [] p x₁ = tt
-- -- -- --  ∀≮≯ℙ (x ∷ p₁ [ _ , x₂ ]s) p q =
-- -- -- --   let z = ∀≮≯ℙ x p (fst q)
-- -- -- --   in z , snd q ∘ T₁.map w 
-- -- -- --    where
-- -- -- --    w : Σ (ℙ Pat)
-- -- -- --          (λ x₁ →
-- -- -- --             Σ (fst (fst (x₁ ≤ℙ (⌞ p₁)))) (λ _ → fst (fst (x₁ ≤ℙ (⌞ p))))) →
-- -- -- --          Σ Pat
-- -- -- --          (λ x₁ → Σ ((PO PosetStr.≤ x₁) p₁) (λ _ → (PO PosetStr.≤ x₁) p))
-- -- -- --    w (⌞_ x₁ , x) = x₁ , x

-- -- -- --  ∀≮≯ℙ' [] p x₁ = tt
-- -- -- --  ∀≮≯ℙ' (x ∷ p₁ [ x₂ , x₃ ]s) p q =
-- -- -- --   let z = ∀≮≯ℙ' x p (fst q)
-- -- -- --   in z , snd q ∘ T₁.map w
-- -- -- --    where
-- -- -- --     w : _
-- -- -- --     w x = ⌞ fst x , snd x

-- -- -- --  module _ (_─_ : DecPoset.─Ty DP )
-- -- -- --        (maxSAC : DecPoset.MaxSAC DP )
-- -- -- --          where

-- -- -- --   ─ℙ : ─Ty DecPosetℙ
-- -- -- --   fst (─ℙ _ ₋₋) = []
-- -- -- --   snd (─ℙ _ ₋₋) (zz) ((fst₁ , snd₂) , snd₁) =
-- -- -- --     snd₂ ∣ zz , IsPoset.is-refl (isPoset Posetℙ) zz  , tt ∣₁ 



-- -- -- --   ─ℙ ₋₋ (⌞ x₁) =
-- -- -- --     mapSAC DecPosetℙ zz
-- -- -- --        xs'
-- -- -- --          , zzzz
-- -- -- --      where
-- -- -- --       open AC─ DP _─_ x₁
-- -- -- --       xs' = (StrAntiChainℙ (AC─ (fst maxSAC) ))

-- -- -- --       zz : _
-- -- -- --       zz (₋₋) ()
-- -- -- --       zz (⌞_ x) x₁' = _ , x₁' ∘ T₁.map zzz
-- -- -- --        where
-- -- -- --        zzz : _
-- -- -- --        zzz (⌞_ x , snd₁) = x , snd₁

-- -- -- --       w = AC─full (fst maxSAC) (snd maxSAC)


-- -- -- --       zzzz : _
-- -- -- --       zzzz ₋₋ x₁* = snd (fst x₁*) ∣ (⌞ x₁) , tt , (is-refl (isPoset PO) x₁) ∣₁ 
-- -- -- --       zzzz (⌞_ x) x₁* = w x ((snd (fst x₁*) ∘ T₁.map (λ a → ⌞ (fst a) , snd a)) ,
-- -- -- --                             qqvv
-- -- -- --                             )
-- -- -- --        where
-- -- -- --         zzzz* = map∀≮≯' DecPosetℙ zz xs' (⌞ x) (snd x₁*)

-- -- -- --         qqvv = ∀≮≯ℙ' ((AC─ (fst maxSAC) )) x zzzz*

-- -- -- --   ─ℙ (⌞ x) (⌞ x₁) =

-- -- -- --     SAC-poset-map {P = P'} {Q = Q'} ⌞_ zw
-- -- -- --       (λ x y → _∘ T₁.map (zz x y) ) (fst zz') , zz'' (fst zz') (snd zz')
-- -- -- --    where
-- -- -- --     P' : _
-- -- -- --     P' = _

-- -- -- --     Q' : _
-- -- -- --     Q' = _

-- -- -- --     zw : _
-- -- -- --     zw x x₁ = fst x₁ , snd x₁ ∘ T₁.map zww
-- -- -- --      where
-- -- -- --       zww : _
-- -- -- --       zww (⌞_ x , snd₁) = x , snd₁

-- -- -- --     zz : ∀ x y → _
-- -- -- --     zz x y (⌞_ x₁ , snd₁) = x₁ , snd₁

-- -- -- --     zz' : _
-- -- -- --     zz' = x ─ x₁  


-- -- -- --     zz'' : (xs : StrAntiChain DP (λ z → (DP ≤ₚ z) x L.⊓ (DP ≮≯ₚ z) x₁))
-- -- -- --       → ⟨ isFull _ _ xs ⟩
-- -- -- --       → ⟨ isFull DecPosetℙ Q'
-- -- -- --           (SAC-poset-map {P = P'} {Q = Q'} ⌞_ zw
-- -- -- --       (λ x y → _∘ T₁.map (zz x y) ) xs) ⟩
-- -- -- --     zz'' xs q ₋₋ ()
-- -- -- --     zz'' xs q (⌞_ x*) = q x* ∘ zz'''
-- -- -- --      where
-- -- -- --       zz''' : _
-- -- -- --       fst (zz''' (pp , qq)) =
-- -- -- --         fst pp , (snd pp ∘ T₁.map λ a → ⌞ (fst a) , snd a)
-- -- -- --       snd (zz''' (pp , qq)) =
-- -- -- --         SAC-poset-map∀≮≯⁻ ⌞_ zw ((λ x y → _∘ T₁.map (zz x y) ))
-- -- -- --          (λ x₂ y x₃ → x₃ ∘ T₁.map λ a → ⌞ (fst a) , snd a) xs x* qq

-- -- -- --   ℙSAC : DecPoset.MaxSAC DecPosetℙ
-- -- -- --   fst ℙSAC = [] ∷ ₋₋ [ tt , tt ]s
-- -- -- --   snd ℙSAC ₋₋ x₁ = snd (snd x₁) ∣ ₋₋ , tt , tt ∣₁
-- -- -- --   snd ℙSAC (⌞_ x) x₁ = snd (snd x₁) ∣ (⌞ x) , (tt , (is-refl (isPoset PO) x)) ∣₁
 
-- -- -- --  module _ (Pat' : Type)
-- -- -- --         (PO' : PosetStr ℓ-zero Pat')
-- -- -- --         (DP' :  DecPoset (_ , PO'))

-- -- -- --         where

  

-- -- -- --   _≤×_ : Pat × Pat' → Pat × Pat' → DecProp ℓ-zero
-- -- -- --   (x , x') ≤× (y , y') = DecProp⊓ (_≤ᵈ_ DP x y) (_≤ᵈ_ DP' x' y') 

-- -- -- --   open PosetStr
-- -- -- --   open IsPoset
-- -- -- --   open DecPoset
  

-- -- -- --   ProdPoset : PosetStr ℓ-zero (Pat × Pat')
-- -- -- --   PosetStr._≤_ ProdPoset = λ x y → (fst (fst (x ≤× y)))
-- -- -- --   is-set (isPoset ProdPoset) = isSet× (is-set (isPoset PO)) ((is-set (isPoset PO')))
-- -- -- --   is-prop-valued (isPoset ProdPoset) = λ x y → (snd (fst (x ≤× y)))
-- -- -- --   is-refl (isPoset ProdPoset) (x , x') =
-- -- -- --     is-refl (isPoset PO) x , is-refl (isPoset PO') x'
-- -- -- --   is-trans (isPoset ProdPoset) x y z (p , p') (q , q') =
-- -- -- --     is-trans (isPoset PO) _ _ _ p q ,
-- -- -- --      is-trans (isPoset PO') _ _ _ p' q'
-- -- -- --   is-antisym (isPoset ProdPoset) _ _ (p , p') (q , q') =
-- -- -- --     cong₂ _,_
-- -- -- --      (is-antisym (isPoset PO) _ _ p q)
-- -- -- --      (is-antisym (isPoset PO') _ _ p' q')


-- -- -- --   DecPoset× : DecPoset (_ , ProdPoset)
-- -- -- --   patOrdDec DecPoset× (x , x') (y , y') =
-- -- -- --     Dec× (patOrdDec DP x y) (patOrdDec DP' x' y')

-- -- -- --   _⊓?_ DecPoset× (x , x') (y , y') with _⊓?_ DP x y | _⊓?_ DP' x' y'
-- -- -- --   ... | inr x₁ | _ =
-- -- -- --     inr (x₁ ∘ T₁.map
-- -- -- --       λ x₁ → (fst (fst x₁)) , (fst (fst (snd x₁))) , fst (snd (snd x₁)) ) 
-- -- -- --   ... | inl _ | inr x₁ =
-- -- -- --     inr (x₁ ∘ T₁.map
-- -- -- --       λ x₁ → (snd (fst x₁)) , (snd (fst (snd x₁))) , snd (snd (snd x₁)) ) 
-- -- -- --   ... | inl (z , (z< , q)) | inl (z' , (z'< , q')) =
-- -- -- --      inl ((z , z')
-- -- -- --          , (((fst z< , fst z'<) , (snd z< , snd z'<)) ,
-- -- -- --            uncurry λ v v' → uncurry (uncurry
-- -- -- --              λ v<x v'<x' → uncurry 
-- -- -- --              λ v<y v'<y' →
-- -- -- --               let h  = q v
-- -- -- --                   h' = q' v'
-- -- -- --               in h (v<x , v<y) , h' (v'<x' , v'<y') )))

-- -- -- --         -- (_─_ : DecPoset.─Ty DP' )
-- -- -- --         -- (maxSAC : DecPoset.MaxSAC DP' ) 

-- -- -- -- record HasPat (A : Type) : Type₁ where
-- -- -- --  field
-- -- -- --   Pat : Type
-- -- -- --   patData : Pat → Type
  
-- -- -- --   -- patPred : Pat → A → DecProp ℓ-zero
-- -- -- --   patOrd : PosetStr ℓ-zero Pat
-- -- -- --   patDecPoset : DecPoset (_ , patOrd)
-- -- -- --   pat─ : DecPoset.─Ty patDecPoset
-- -- -- --   patSAC : DecPoset.MaxSAC patDecPoset
-- -- -- --   toPat : A → Pat
-- -- -- --   toPatMin : ∀ a → ⟨ DecPoset.minimal patDecPoset (toPat a) ⟩

-- -- -- --  field
-- -- -- --   patDataEquiv : ∀ p →
-- -- -- --     Σ A (λ a → ⟨ DecPoset._≤ₚ_ patDecPoset (toPat a)  p ⟩   ) ≃ patData p
    
-- -- -- --  open DecPoset (DecPosetℙ _ _ patDecPoset) 

 
-- -- -- --  ℙat : Type
-- -- -- --  ℙat = ℙ Pat



-- -- -- -- --  -- patChainCompltₚ' : PatChain → hProp ℓ-zero 
-- -- -- -- --  -- patChainCompltₚ' pc = ∀


-- -- -- -- --  patChainCompltₚLawHlp : ∀ pc → _
-- -- -- -- --  patChainCompltₚLawHlp [] x = just (inl λ _ _ → tt)
-- -- -- -- --  patChainCompltₚLawHlp pc@(xs ∷ x [ q ]p) y with snd (patChainTail pc y)
-- -- -- -- --  ... | yes p = nothing
-- -- -- -- --  ... | no ¬p = just (inr λ a v vv → ¬p ({!!} , {!!}) )
 
-- -- -- -- --  -- patChainCompltₚLawHlp pc x with snd (patChainTail pc x)


-- -- -- -- --  patChainCompltₚLaw : ∀ pc →
-- -- -- -- --    ⟨ patChainCompltₚ pc L.⇔
-- -- -- -- --      fst (isEmptySAC (fst
-- -- -- -- --        ((patDecScan (λ a → patChainTail pc (fromAtom a)) (patChainCompltₚLawHlp pc))))) ⟩ 
-- -- -- -- --  fst (patChainCompltₚLaw []) = {!!}
-- -- -- -- --  snd (patChainCompltₚLaw []) = {!!}
-- -- -- -- --  patChainCompltₚLaw (pc ∷ p [ x ]p) = {!!}

-- -- -- -- patData' : ∀ {A} → {{hpA : HasPat A}}
-- -- -- --               →  HasPat.ℙat hpA  → Type₀
-- -- -- -- patData' {A} ₋₋ = A
-- -- -- -- patData' ⦃ hpA = hpA ⦄ (⌞ x) = HasPat.patData hpA x

-- -- -- -- patData'Equiv : ∀ {A} → {{hpA : HasPat A}}
-- -- -- --               → 
-- -- -- --               ∀ p →
-- -- -- --               Σ A (λ a → ⟨ DecPoset._≤ₚ_ (DecPosetℙ _ _ (HasPat.patDecPoset hpA)) (⌞ (HasPat.toPat hpA a))  p ⟩   ) ≃ patData' p
-- -- -- -- patData'Equiv ₋₋ = isoToEquiv rUnit×Iso
-- -- -- -- patData'Equiv ⦃ hpA = hpA ⦄ (⌞_ x₁) = HasPat.patDataEquiv hpA x₁
