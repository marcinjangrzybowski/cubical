{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.NormalForm where

-- open import Cubical.HITs.FreeGroup.Base renaming (assoc to ·assoc)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

-- open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
-- open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Functions.Involution

open import Cubical.Functions.Embedding
import Cubical.Functions.Logic as L

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/₂_ ; [_] to [_]/)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base


private
  variable
    ℓ : Level

module _ {A : Type ℓ} where

 ++=[] : ∀ (xs ys : List A) → xs ++ ys ≡ [] → ys ≡ [] 
 ++=[] [] ys x = x
 ++=[] (x₁ ∷ xs) ys x = ⊥.rec (¬cons≡nil x)


module NormalForm {A : Type ℓ} where


 IsRedex : Bool × A → Bool × A → Type ℓ
 IsRedex (b , x) (b' , x') = (b ≡ not b') × (x ≡ x')

 WillReduce : Bool → A → (xs : List (Bool × A)) → Type ℓ
 WillReduce _ _ [] = ⊥* 
 WillReduce b x (h ∷ _) = IsRedex (b , x) h

 HeadIsRedex : List (Bool × A) → Type ℓ
 HeadIsRedex [] = ⊥*
 HeadIsRedex ((b , a) ∷ xs) = WillReduce b a xs

 IsNormalised : List (Bool × A) → Type ℓ
 IsNormalised [] = Unit*
 IsNormalised ((b , x) ∷ xs) = (¬ WillReduce b x xs)  × IsNormalised xs

 WillReduce∷ʳ : ∀ x x' xs → WillReduce (fst x) (snd x) xs →
                 WillReduce (fst x) (snd x) (xs ∷ʳ x')
 WillReduce∷ʳ x x' (x₂ ∷ xs) x₁ = x₁

 WillReduce++ʳ : ∀ {x xs ys} → WillReduce (fst x) (snd x) xs →
                 WillReduce (fst x) (snd x) (xs ++ ys)
 WillReduce++ʳ {xs = _ ∷ _} u = u


 IsNormalised∷ᵣ : ∀ x xs → IsNormalised (xs ∷ʳ x) → IsNormalised xs 
 IsNormalised∷ᵣ x [] x₁ = tt*
 IsNormalised∷ᵣ x (x₂ ∷ xs) x₁ =
   fst x₁ ∘ WillReduce∷ʳ _ _ _  , IsNormalised∷ᵣ x xs (snd x₁)

 IsNormalised++ : ∀ xs ys → IsNormalised (xs ++ ys) →
      IsNormalised xs × IsNormalised ys
 IsNormalised++ [] ys x = _ , x
 IsNormalised++ (x₁ ∷ xs) ys (u , v) = 
  let (u' , v')  = IsNormalised++ xs ys v
  in (u ∘  WillReduce++ʳ , u') , v'
  
 infixr 5 _∷_ 
 
 data Red* {ℓX} (X : Type ℓX) : Type ℓX where
  [] : Red* X
  _∷_ : X ⊎ Red* X → Red* X → Red* X

 infixr 5 _cj∷_ _cj⁺∷_ _cj⁻∷_ _·∷_ 

 pattern _cj∷_ a xs = (inl a) ∷ xs  
 pattern _cj⁺∷_ a xs = (inl (true  , a)) ∷ xs  
 pattern _cj⁻∷_ a xs = (inl (false  , a)) ∷ xs  
 pattern _·∷_ xs ys = (inr xs) ∷ ys  

 mapRed : ∀ {ℓX} {X} {ℓX'} {X'} → (X → X') → Red* {ℓX} X → Red* {ℓX'} X'
 mapRedHlp : ∀ {ℓX} {X} {ℓX'} {X'} → (X → X') →
                     (X ⊎ Red* {ℓX} X)
                    → (X' ⊎ Red* {ℓX'} X')
 mapRedHlp f (inl x) = inl (f x)
 mapRedHlp f (inr x) = inr (mapRed f x)
 mapRed f [] = []
 mapRed f (x ∷ y) = mapRedHlp f x ∷ mapRed f y

 Red = Red* (Bool × A)
 Shp = Red* Unit
 
 IdxHlp : ∀ {ℓX} {X} → X ⊎ Red* {ℓX} X → Type

 Idx : ∀ {ℓX} {X} → Red* {ℓX} X → Type

 IdxHlp (inl x) = Unit
 IdxHlp (inr x) = Idx x

 Idx [] = ⊥
 Idx (x ∷ xs) = IdxHlp x ⊎ Idx xs

 discreteIdx : ∀ {ℓX} {X} → (r : Red* {ℓX} X) →
                 Discrete (Idx r)
 discreteIdxHlp : ∀ {ℓX} {X} → (r : _) →
                 Discrete (IdxHlp {ℓX} {X} r)
 discreteIdxHlp (inl x) _ _ = yes refl
 discreteIdxHlp (inr x) = discreteIdx x
 discreteIdx (x ∷ r) = discrete⊎ (discreteIdxHlp x) (discreteIdx r)

 shp : Red → Shp 
 shp = mapRed λ _ → _
 
 lookupIdx : ∀ r → Idx r → Bool × A
 lookupIdxHlp : (r' : (Bool × A) ⊎ Red) → IdxHlp r' → Bool × A 
 lookupIdxHlp (inl x₁) x = x₁
 lookupIdxHlp (inr x₁) x = lookupIdx x₁ x
 lookupIdx (x₁ ∷ r) (inl x) = lookupIdxHlp x₁ x
 lookupIdx (x₁ ∷ r) (inr x) = lookupIdx r x

 tabulateIdx : ∀ {ℓX} {X} s → (Idx {ℓX} {X} s → (Bool × A)) → Red
 tabulateIdxHlp : ∀ {ℓX} {X} s → ((IdxHlp {ℓX} {X} s) → Bool × A)
                      → (Bool × A) ⊎ Red* (Bool × A)
 tabulateIdxHlp (inl _) x = inl (x tt)
 tabulateIdxHlp (inr x₁) x = inr (tabulateIdx x₁ x)

 
 tabulateIdx [] x = []
 tabulateIdx (x₁ ∷ s) x =
   tabulateIdxHlp x₁ (x ∘ inl) ∷ tabulateIdx s (x ∘ inr)

 not₁ : (Bool × A) → (Bool × A)
 not₁ = map-fst not


 evRed : Red → List (Bool × A)
 evRed [] = []
 evRed (x cj∷ xs) = x ∷ (evRed xs ∷ʳ not₁ x)
 evRed (x ·∷ xs) = evRed x ++ evRed xs

 redLen : ∀ {ℓX} {X} → Red* {ℓX} X → ℕ
 redLenHlp : ∀ {ℓX} {X} → X ⊎ Red* {ℓX} X → ℕ
 redLenHlp (inl x) = 1
 redLenHlp (inr x) = redLen x
 redLen [] = 0
 redLen (x ∷ xs) = redLenHlp x + redLen xs

 isEmptyRed : ∀ {ℓX} {X} → Red* {ℓX} X → Type
 isEmptyRed [] = Unit
 isEmptyRed (x cj∷ x₁) = ⊥
 isEmptyRed (x ·∷ x₁) = isEmptyRed x × isEmptyRed x₁ 

 isLeafIdx : ∀ {ℓX} {X} s → Idx {ℓX} {X} s → Type
 isLeafIdxHlp : ∀ {ℓX} {X} s → Red* {ℓX} X → IdxHlp {ℓX} {X} s → Type
 isLeafIdxHlp (inl x₁) xs x = isEmptyRed xs
 isLeafIdxHlp (inr x₁) xs x = isLeafIdx x₁ x
 isLeafIdx (x ∷ s) (inl x₁) = isLeafIdxHlp x s x₁
 isLeafIdx (x ∷ s) (inr x₁) = isLeafIdx s x₁

 Idx×𝟚 : Red → Type
 Idx×𝟚 r = Idx r × Bool
 
 lookupIdx' : ∀ r → Idx r → Bool → (Bool × A)
 lookupIdx' r idx b =
   map-fst (b ⊕_) (lookupIdx r idx)


 [idx] : ∀ {ℓX} {X} r → List (Idx {ℓX} {X} r × Bool)
 [idx] [] = []
 [idx] (a cj∷ r) =
   (inl _ , false) ∷ (Li.map (map-fst inr) ([idx] r) ∷ʳ (inl _ , true))
 [idx] (r' ·∷ r) =
   Li.map (map-fst inl) ([idx] r')
    ++ Li.map (map-fst inr) ([idx] r) 

 idx→k : ∀ {ℓX} {X} r → Idx {ℓX} {X} r → Bool → ℕ 
 idx→k (x₂ ∷ r) (inr x) b = (redLenHlp x₂ ℕ.· 2) + idx→k r x b
 idx→k (x₁ cj∷ r) (inl x) false = 0
 idx→k (x₁ cj∷ r) (inl x) true = suc (redLen r ℕ.· 2)
 idx→k (x₁ ·∷ r) (inl x) b = idx→k x₁ x b

 idx→k<len·2 : ∀ {ℓX} {X} r →
   (ix : Idx {ℓX} {X} r) → ∀ b
   → idx→k r ix b < redLen r ℕ.· 2
 idx→k<len·2 (x ∷ r) (inr x₁) b = {!!}
 idx→k<len·2 (x cj∷ r) (inl x₁) false = tt
 idx→k<len·2 (x cj∷ r) (inl x₁) true = ≤-refl (redLen r ℕ.· 2)
 idx→k<len·2 (x ·∷ r) (inl x₁) b =
  ≤-trans {suc (idx→k x x₁ b)}
   {redLen x ℕ.· 2} {(redLen x + redLen r) ℕ.· 2} (idx→k<len·2 x x₁ b)
     (subst (redLen x ℕ.· 2 ≤_)
       (·-distribʳ (redLen x) (redLen r) 2)
        (k≤k+n (redLen x ℕ.· 2)))

 Fin·2 : ∀ n → Type
 Fin·2 n = Σ _ λ k → (k < n ℕ.· 2)

 IsoFinS·2 : ∀ n → Iso (Fin·2 (suc n)) (Unit ⊎ (Unit ⊎ (Fin·2 n)) )
 Iso.fun (IsoFinS·2 n) (zero , k<) = inl _
 Iso.fun (IsoFinS·2 n) (suc zero , k<) = inr (inl _)
 Iso.fun (IsoFinS·2 n) (suc (suc k) , k<) = inr (inr (k , k<))
 Iso.inv (IsoFinS·2 n) (inl x) = 0 , _
 Iso.inv (IsoFinS·2 n) (inr (inl x)) = 1 , _
 Iso.inv (IsoFinS·2 n) (inr (inr (k , k<))) = suc (suc k) , k< 
 Iso.rightInv (IsoFinS·2 n) (inl x) = refl
 Iso.rightInv (IsoFinS·2 n) (inr (inl x)) = refl
 Iso.rightInv (IsoFinS·2 n) (inr (inr x)) =
  cong (inr {A = Unit} ∘ inr) (Σ≡Prop
    (λ k → Cubical.Data.Nat.Order.Recursive.isProp≤ {suc k}
      {n ℕ.· 2}) refl)
 Iso.leftInv (IsoFinS·2 n) (zero , k<) = refl
 Iso.leftInv (IsoFinS·2 n) (suc zero , k<) = refl
 Iso.leftInv (IsoFinS·2 n) (suc (suc k) , k<) =
   (Σ≡Prop
    (λ k → Cubical.Data.Nat.Order.Recursive.isProp≤ {k}
      {suc (n ℕ.· 2)}) refl)
 
 IsoFin⊎ : ∀ n m → Iso ((Fin·2 n) ⊎ (Fin·2 m)) (Fin·2 (n + m)) 
 IsoFin⊎ zero m = compIso ⊎.⊎-swap-Iso
   (compIso (⊎Iso idIso (compIso Σ-swap-Iso (ΣEmptyIso _))) ⊎-⊥-Iso)
 IsoFin⊎ (suc n) m =
   compIso (⊎Iso (IsoFinS·2 n) (idIso))
     (compIso (compIso
        (compIso ⊎-assoc-Iso
          (⊎Iso idIso ⊎-assoc-Iso)) (⊎Iso idIso (⊎Iso idIso (IsoFin⊎ n m))))
       (invIso (IsoFinS·2  (n + m))))

 IsoIdxFin·2 : ∀ r → Iso (Idx×𝟚 r) (Fin·2 (redLen r)) 
 IsoIdxFin·2Hlp : ∀ (r : _ ⊎ Red) → Iso (IdxHlp r × Bool) (Fin·2 (redLenHlp r))
 IsoIdxFin·2Hlp (inl x) = {!!}
 IsoIdxFin·2Hlp (inr x) = IsoIdxFin·2 x
 
 IsoIdxFin·2 [] = compIso (compIso (ΣEmptyIso _) (invIso (ΣEmptyIso _)))
                   Σ-swap-Iso 
 IsoIdxFin·2 (x cj∷ r) = {!!}
  --  compIso (compIso lemIso (⊎Iso (idIso {A = Unit})
  --    (⊎Iso (IsoIdxFin·2 r) (idIso {A = Unit})))) {!!}
  -- where
  --  lemIso : Iso ((Unit ⊎ Idx r) × Bool) (Unit ⊎ ((Idx r ×  Bool) ⊎ Unit))
  --  Iso.fun lemIso (inl _ , false) = inl _
  --  Iso.fun lemIso (inl _ , true) = inr (inr _)
  --  Iso.fun lemIso (inr x , b) = inr (inl (x , b))
  --  Iso.inv lemIso (inl _) = inl _ , false
  --  Iso.inv lemIso (inr (inl (x , b))) = inr x , b
  --  Iso.inv lemIso (inr (inr _)) = inl _ , true
  --  Iso.rightInv lemIso (inl _) = refl
  --  Iso.rightInv lemIso (inr (inl (_ , false))) = refl
  --  Iso.rightInv lemIso (inr (inl (_ , true))) = refl
  --  Iso.rightInv lemIso (inr (inr _)) = refl
  --  Iso.leftInv lemIso (inl x , false) = refl
  --  Iso.leftInv lemIso (inr x , false) = refl
  --  Iso.leftInv lemIso (inl x , true) = refl
  --  Iso.leftInv lemIso (inr x , true) = refl
   
 IsoIdxFin·2 (x ·∷ r) =
   compIso (compIso Σ⊎Iso
     (⊎Iso (IsoIdxFin·2 x) (IsoIdxFin·2 r))) (IsoFin⊎ (redLen x) (redLen r))
    
 -- k→idx : ∀ {ℓX} {X} r →
 --   ∀ k → (k < redLen r ℕ.· 2) → Σ (Idx {ℓX} {X} r × Bool)
 --      (λ (ix , b) → idx→k r ix b ≡ k) 
 -- k→idx (x₁ cj∷ r) zero x = (inl _ , false) , refl
 -- k→idx (x₁ cj∷ r) (suc k) x = {!!}
 -- k→idx (x₁ ·∷ r) k x = {!!}
 
 [_]_≺_ : ∀ {ℓX} {X} r → Idx {ℓX} {X} r → Idx r → ((Σ Type Dec) × (Σ Type Dec))
 [_]_≺_ (a cj∷ r) (inl x) (inl x₁) = (Unit , yes tt) , (⊥ , no λ ())
 [_]_≺_ (a cj∷ r) (inl x) (inr x₁) = (⊥ , no λ ()) , (⊥ , no λ ())
 [_]_≺_ (a cj∷ r) (inr x) (inl x₁) = (Unit , yes tt) , (Unit , yes tt)
 [_]_≺_ (a cj∷ r) (inr x) (inr x₁) = [ r ] x ≺ x₁
 [_]_≺_ (r ·∷ r') (inl x) (inl x₁) = [ r ] x ≺ x₁
 [_]_≺_ (r ·∷ r') (inl x) (inr x₁) = (⊥ , no λ ()) , (⊥ , no λ ())
 [_]_≺_ (r ·∷ r') (inr x) (inl x₁) = (⊥ , no λ ()) , (⊥ , no λ ())
 [_]_≺_ (r ·∷ r') (inr x) (inr x₁) = [ r' ] x ≺ x₁


 MarkedRed = Red* (Bool × (Bool × A))

 toMarkedFresh : Red → MarkedRed
 toMarkedFresh = mapRed (false ,_) 

 _⊰_ : {r : Red} → Idx×𝟚 r → Idx×𝟚 r → Type  
 _⊰_ {r} x y = 
   fst (Iso.fun (IsoIdxFin·2 r) x)
    < fst (Iso.fun (IsoIdxFin·2 r) y)


 -- Mark' : ∀ {ℓ} {A : Type ℓ}
          
 --          (B? : ∀ a → Bool ) → List A
 --          → Bool → ℕ → Bool
 -- Mark' B? [] b0 _ = b0
 -- Mark' B? (x ∷ xs) b0 zero = b0
 -- Mark' B? (x ∷ xs) b0 (suc k) =
 --  Mark' B? (xs) (B? x ⊕ b0) k
  

 ∫⊕ : (ℕ → Bool) → ℕ → Bool 
 ∫⊕ f zero = false
 ∫⊕ f (suc k) = f k ⊕ ∫⊕ f k

 ∫⊕F' : ∀ {n} → ((Σ _ λ k → (k < n)) → Bool) → ∀ k → (k < n) → Bool 
 ∫⊕F' {suc n} f (zero) k< = false
 ∫⊕F' {suc n} f (suc k) k< =
   f (k , <-weaken {n = n} k<) ⊕ ∫⊕F' {suc n} f k (<-weaken {n = n} k<)


 ∫⊕F : ∀ {n} → ((Σ _ λ k → (k < n)) → Bool) → (Σ _ λ k → (k < n)) → Bool 
 ∫⊕F {n} f = uncurry (∫⊕F' {n} f) 


 ∫fromIx' : ∀ (r : Red) → (Idx r → Bool) → Bool → Idx×𝟚 r → Bool
 ∫fromIx' (x₁ cj∷ r) f b' = uncurry $
   let f? = f (inl _)
   in ⊎.rec (λ _ bSide → if bSide then b' else (f? ⊕ b'))
        (curry (∫fromIx' r (f ∘ inr) (f? ⊕ b')))
 ∫fromIx' (x₁ ·∷ r) f b' =
   uncurry $ ⊎.rec ((curry (∫fromIx' x₁ (f ∘ inl) b' ))) (curry (∫fromIx' r (f ∘ inr) b' )) 


 ∫fromIx : ∀ (r : Red) → (Idx r → Bool) → Idx×𝟚 r → Bool
 ∫fromIx r f = ∫fromIx' r f false 
 -- f : ℕ → Bool
 -- f 0 = false
 -- f 1 = false
 -- f 2 = true
 -- f 3 = false
 -- f 4 = false
 -- f 5 = true
 -- f _ = false

 range : ℕ → List ℕ
 range zero = []
 range (suc k) = zero ∷ Li.map suc (range k)
 
 -- fx = Li.map {B = Bool × Bool} (λ k → f k , ∫⊕ f k) (range 8)

 
 -- fx' = (false , false) ∷
 --         (false , false) ∷
 --         (true , false) ∷
 --         (false , true) ∷
 --         (false , true) ∷
 --         (true , true) ∷ (false , false) ∷ (false , false) ∷ []
 
 record ChainCtx : Type ℓ where
  field
   aR bR : Red
   l : List (Bool × A)
   0<lenL : 0 < length l 
   aR++l=bR : evRed aR ++ l ≡ evRed bR
   IsoIxBIxA⊎F : Iso (Idx×𝟚 bR) (Idx×𝟚 aR ⊎ Fin·2 (redLen bR ℕ.∸ redLen aR))
   
  ixB∈aR : Idx bR × Bool → Type
  ixB∈aR x = isInl (Iso.fun IsoIxBIxA⊎F x)

  ixB∉aR : Idx bR × Bool → Type
  ixB∉aR x = isInr (Iso.fun IsoIxBIxA⊎F x)
  
  overEdgeBidx : Idx bR → Type
  overEdgeBidx idx =
    ixB∈aR (idx , false)
     × ixB∉aR (idx , true)

  _b↔a_ : Idx×𝟚 bR → Idx×𝟚 aR → Type
  _b↔a_ bIx aIx = Iso.fun IsoIxBIxA⊎F bIx ≡ inl aIx

  

  data Chain : Type

  headCh : Chain → Idx×𝟚 bR

  _↖↙_ : Idx×𝟚 bR → Idx×𝟚 bR → Type 
  (ixB , b) ↖↙ ixB'  =
   Σ (ixB∈aR ixB') λ p → 
    ((ixB , not b) ≡
      Iso.inv IsoIxBIxA⊎F (inl (map-snd not (fromIsInl _ p))))

  record ChainStep (xs : Chain) : Type where
   pattern
   constructor cs[_,_]
   field
    ixB : _
    link : ixB ↖↙ (headCh xs)

  open ChainStep
 
  data Chain where
   [_,_] : ∀ ixB → overEdgeBidx ixB → Chain
   _∷_ : ∀ xs → ChainStep xs → Chain

  headCh [ ixB , x ] = ixB , false
  headCh (xs ∷ cs[ ixB , x₁ ]) = ixB

  chainStep? : ∀ xs → Dec (ChainStep xs)
  chainStep? xs = w (_ , refl)
   where
   w : ((x , _) : singl (Iso.fun IsoIxBIxA⊎F (headCh xs)))
          → Dec (ChainStep xs)
   w (inl x , p) = yes cs[
          map-snd not
           (Iso.inv IsoIxBIxA⊎F (inl (map-snd not
             (fromIsInl (Iso.fun IsoIxBIxA⊎F (headCh xs))
              (subst isInl (sym p) _)))))
          , ((subst isInl (sym p) _) , ΣPathP (refl , notnot _)) ]
   w (inr x , p) = no ((subst isInl p ∘ fst) ∘ link)

  IsCompleted : Chain → Type
  IsCompleted xs = ¬ (ChainStep xs)


  -- inCh? : Idx×𝟚 bR → Bool
  -- inCh? = {!!}

  markF : ℕ → Bool
  markF k = {!!}
  
  mark : Idx×𝟚 bR → Bool
  mark ix =
   let k = {!!}
   in ∫⊕F {!!} k
  
--   ixB∈aR→ixA : ∀ idxB → ixB∈aR idxB → Idx aR × Bool
--   ixB∈aR→ixA = {!!}
 
--   infixr 5 _b∷_[_,_] _a∷_[_,_]


--   data ChainA : Type
--   data ChainB : Type 

--   _B∉chA_ : Idx×𝟚 bR → ChainA → Type
--   _B∉chB_ : Idx×𝟚 bR → ChainB → Type
--   _A∉chB_ : Idx×𝟚 aR → ChainB → Type
--   _A∉chA_ : Idx×𝟚 aR → ChainA → Type


--   _a←b_ : Idx×𝟚 aR → Idx×𝟚 bR → Type
--   _b←a_ : Idx×𝟚 bR → Idx×𝟚 aR → Type

--   headA : ChainA → Idx×𝟚 aR
--   headB : ChainB → Idx×𝟚 bR

--   data ChainB where 
--    [_,_] : ∀ ixB → overEdgeBidx ixB → ChainB
--    _b∷_[_,_] : ∀ ixB → (chA : ChainA)
--      → ixB b←a (headA chA) → ixB B∉chA chA  → ChainB
   
--   data ChainA  where 
--    _a∷_[_,_] : ∀ ixA → (chB : ChainB)
--      → ixA a←b (headB chB) → ixA A∉chB chB  → ChainA


--   headA (ixA a∷ chB [ _ , _ ]) = ixA

--   headB [ ixB , x ] = ixB , false
--   headB (ixB b∷ chA [ _ , _ ]) = ixB

--   (ixA , bA) a←b ixB = ixB b↔a (ixA , not bA)
--   (ixB , bB) b←a ixA = (ixB , not bB) b↔a ixA
  
  
  
--   x B∉chA (ixA a∷ chB [ _ , _ ]) = x B∉chB chB
--   x B∉chB [ ixB , x₁ ] = ¬ (fst x ≡ ixB)
--   x B∉chB (ixB b∷ chA [ _ , _ ]) =
--     (¬ (fst x ≡ fst ixB)) × (x B∉chA chA) 
--   x A∉chA (ixA a∷ chB [ _ , _ ]) =
--     (¬ (fst x ≡ fst ixA)) × (x A∉chB chB) 
--   x A∉chB [ ixB  , _ ] = Unit
--   x A∉chB (ixB b∷ chA [ _ , _ ]) = x A∉chA chA

--   Completed : ChainB → Type  
--   Completed chB = overEdgeBidx (fst  (headB chB)) × (snd (headB chB) ≡ true)

--   stepA∉ : ∀ chA → map-snd not (Iso.inv IsoIxBIxA⊎F (inl (headA chA))) B∉chA chA
--   stepA∉ (ixA a∷ [ ixB , (inlIxbF , inrIxbR )  ] [ x , x₁ ]) p =
--     let z : snd (Iso.inv IsoIxBIxA⊎F (inl ixA)) ≡ true
--         z = ¬false→true _
--            λ p' →
--              let q : Iso.inv IsoIxBIxA⊎F (inl ixA) ≡ (ixB , false)
--                  q = ΣPathP (p , p')
--                  q' = cong (Iso.fun IsoIxBIxA⊎F) q
--              in not≢const _
--                   (sym
--                    (cong snd (isEmbedding→Inj
--                     ⊎.isEmbedding-inl _ _
--                     (sym (Iso.rightInv IsoIxBIxA⊎F (inl ixA)) ∙∙ q' ∙∙ x))))
--         zz :  (ixB , true) ≡ Iso.inv IsoIxBIxA⊎F (inl ixA)
--         zz = ΣPathP (sym p , (sym z))
--     in subst {y = inl ixA} isInr
--         (cong (Iso.fun IsoIxBIxA⊎F) zz ∙
--           Iso.rightInv IsoIxBIxA⊎F (inl ixA)) inrIxbR
        
--   stepA∉ (ixA a∷ ixB b∷ chA [ x₂ , x₃ ] [ x , x₁ ]) = {!!}
  
--   stepA : (chA : ChainA) →
--     Σ _ λ ixB → ixB b←a (headA chA) × ixB B∉chA chA
--   fst (stepA chA) = map-snd not (Iso.inv IsoIxBIxA⊎F (inl (headA chA)))
--   fst (snd (stepA chA)) =
--     cong (Iso.fun IsoIxBIxA⊎F) (ΣPathP (refl , notnot _))
--      ∙ Iso.rightInv IsoIxBIxA⊎F (inl (headA chA))
--   snd (snd (stepA chA)) = stepA∉ chA
  
-- --  -- ChainCtx a b l = {!!}

-- --  Hlp : ∀ (a b : Red) (l : List (Bool × A)) →  0 < length l →  evRed a ++ l ≡ evRed b →
-- --             ¬ (IsNormalised l)   
-- --  Hlp = {!!}

-- --  -- [_,_,_]subRed_ : _ → Red →  _ → Red → Type ℓ
-- --  -- [ ls , xs , rs ]subRed ys = 
-- --  --    ls ++ evRed xs ++ rs ≡ evRed ys


-- --  -- AtomRdxAt : (r : Red) → Idx r → Bool → Type
-- --  -- AtomRdxAt r idx b = {!!}


-- --  -- subRedsEndL : ∀ ls xs ys rs → [ ls , xs , rs ]subRed ys →
-- --  --                 Σ Red λ r → evRed r ≡ ls ++ rs
-- --  -- subRedsEndL = {!!}




-- -- -- -- -- infixr 5 _∷↔_ 

-- -- -- --  -- Red : (R : Type ℓ) → Type ℓ
-- -- -- --  -- Red R = ((Bool × A) × Maybe (Bool × R))

-- -- -- --  data Red : Type ℓ
-- -- -- --  data Red[] : Type ℓ

-- -- -- --  data Red where
-- -- -- --   red· : Red[] → Red
-- -- -- --   ·A : (Bool × A) → Red

-- -- -- --  data Red[] where
-- -- -- --    ↔ : Red[]
-- -- -- --    _∷↔_ : Red → Red[] → Red[]

-- -- -- --  -- red[]→List : Red[] → List Red
-- -- -- --  -- red[]→List (↔ x) = [ x ]
-- -- -- --  -- red[]→List (x ∷↔ xs) = x ∷ red[]→List xs

-- -- -- --  evRed : Red → List (Bool × A) → List (Bool × A)
-- -- -- --  evRed[] : Red[] → List (Bool × A)

-- -- -- --  red[]Length/2 : Red[] → ℕ

-- -- -- --  redLength/2 : Red → ℕ
-- -- -- --  redLength/2 (red· x) = red[]Length/2 x
-- -- -- --  redLength/2 (·A x) = 1


-- -- -- --  red[]Length/2 ↔ = zero
-- -- -- --  red[]Length/2 (x ∷↔ x₁) = redLength/2 x + red[]Length/2 x₁

-- -- -- --  evRed (red· x) xs = evRed[] x ++ xs
-- -- -- --  -- evRed (·red x) xs = xs ++ evRed[] x 
-- -- -- --  evRed (·A (b , a)) xs = (b , a) ∷ (xs ∷ʳ (not b , a))
-- -- -- --  evRed[] (↔) = []
-- -- -- --  evRed[] (x ∷↔ xs) = evRed x (evRed[] xs)

-- -- -- --  evRedLen : ∀ r → length (evRed[] r) ≡ red[]Length/2 r ℕ.· 2
-- -- -- --  evRedLen ↔ = refl
-- -- -- --  evRedLen (red· x ∷↔ r) =
-- -- -- --    let x' = evRedLen x
-- -- -- --        r' = evRedLen r
-- -- -- --    in length++ (evRed[] x) (evRed[] r) ∙∙ cong₂ _+_ x' r'
-- -- -- --      ∙∙ ·-distribʳ (red[]Length/2 x) (red[]Length/2 r)  2
-- -- -- --  evRedLen (·A x ∷↔ r) =
-- -- -- --    cong suc (length++ (evRed[] r) _ ∙ +-comm _ 1)
-- -- -- --     ∙ cong (2 +_) (evRedLen r)    

-- -- -- --  [_,_,_]subRed_ : _ → Red[] →  _ → Red[] → Type ℓ
-- -- -- --  [ ls , xs , rs ]subRed ys = 
-- -- -- --     ls ++ evRed[] xs ++ rs ≡ evRed[] ys

-- -- -- --  atomRedexAt : List (Bool × A) → ℕ → Type ℓ
-- -- -- --  atomRedexAt xs k = HeadIsRedex (drop k xs) 

-- -- -- --  atomRedexAt<length : ∀ xs k → atomRedexAt xs k → suc k < length xs
-- -- -- --  atomRedexAt<length (x₁ ∷ x₂ ∷ xs) zero x = tt
-- -- -- --  atomRedexAt<length (x₁ ∷ xs) (suc k) x = atomRedexAt<length xs k x
  
-- -- -- --  atomRedex : List (Bool × A) → Type ℓ
-- -- -- --  atomRedex xs =
-- -- -- --    Σ _ (atomRedexAt xs)

-- -- -- --  ++atomRedexAt : ∀ k xs ys
-- -- -- --    → atomRedexAt ys k
-- -- -- --    → atomRedexAt (xs ++ ys) (length xs + k)
-- -- -- --  ++atomRedexAt k [] ys x = x
-- -- -- --  ++atomRedexAt k (x₁ ∷ xs) ys x = ++atomRedexAt k xs ys x
 
-- -- -- --  ++atomRedex : ∀ xs ys → atomRedex ys → atomRedex (xs ++ ys)
-- -- -- --  ++atomRedex xs ys (k , u) = length xs + k , ++atomRedexAt k xs ys u 

-- -- -- --  atomRedexAt++ : ∀ k xs ys → atomRedexAt xs k → atomRedexAt (xs ++ ys) k
-- -- -- --  atomRedexAt++ zero [] ys ()
-- -- -- --  atomRedexAt++ (suc k) [] ys ()
-- -- -- --  atomRedexAt++ (suc k) (x₁ ∷ xs) ys u = atomRedexAt++ k xs ys u
-- -- -- --  atomRedexAt++ zero (x₁ ∷ x₂ ∷ xs) ys x = x
 
-- -- -- --  atomRedex++ : ∀ xs ys → atomRedex xs → atomRedex (xs ++ ys)
-- -- -- --  atomRedex++ xs ys (k , u) = k , atomRedexAt++ k xs ys u

-- -- -- --  atomRedexRed[]Ev : ∀ r → atomRedex (evRed[] r) ⊎ (evRed[] r ≡ []) 
-- -- -- --  atomRedexRed[]Ev ↔ = inr refl
-- -- -- --  atomRedexRed[]Ev (red· x ∷↔ r) =
-- -- -- --    ⊎.rec (λ u → inl (atomRedex++ _ _ u))
-- -- -- --          (λ p → ⊎.rec
-- -- -- --            (λ u → inl (++atomRedex _ _ u))
-- -- -- --            (λ p' → inr (cong₂ _++_ p p'))
-- -- -- --            (atomRedexRed[]Ev r) )
-- -- -- --      (atomRedexRed[]Ev x) 
-- -- -- --  atomRedexRed[]Ev (·A x ∷↔ r) =
-- -- -- --       ⊎.rec ((λ u → inl (++atomRedex [ x ] _ (atomRedex++ _ _ u))))
-- -- -- --             (λ p → inl (subst (λ xs →
-- -- -- --              atomRedex (x ∷ xs ++ (not (fst x) , snd x) ∷ []))
-- -- -- --              (sym p) ((0) , (sym (notnot (fst x))) , refl)))
-- -- -- --      (atomRedexRed[]Ev r) 

-- -- -- --  -- pairIn : ∀ (Bool × A) (Bool × A) → List (Bool × A) → {!!} 
-- -- -- --  -- pairIn = {!!}
-- -- -- --  -- subRedsAtomRedex : ∀ ls xs ys rs → [ ls , xs , rs ]subRed ys 
-- -- -- --  --                 → atomRedex (evRed[] xs)
-- -- -- --  --                 → atomRedex (evRed[] ys) 
-- -- -- --  -- subRedsAtomRedex ls xs ys rs p u =
-- -- -- --  --    subst atomRedex p ((++atomRedex ls _ (atomRedex++ _ rs u)))

-- -- -- --  subRedsAtomRedexAt : ∀ ls xs ys rs k → [ ls , xs , rs ]subRed ys 
-- -- -- --                  → atomRedexAt (evRed[] xs) k
-- -- -- --                  → atomRedexAt (evRed[] ys) (length ls + k) 
-- -- -- --  subRedsAtomRedexAt ls xs ys rs k u v =
-- -- -- --    let z = ++atomRedexAt k ls (evRed[] xs ++ rs)
-- -- -- --             (atomRedexAt++ k (evRed[] xs) rs v)
-- -- -- --    in subst (flip atomRedexAt (length ls + k))
-- -- -- --         u z


-- -- -- --  removePairAt : ℕ → List (Bool × A) → List (Bool × A)
-- -- -- --  removePairAt k xs = (take k xs) ++ (drop (2 + k) xs)

-- -- -- --  ++removePairAt : ∀ k xs ys →
-- -- -- --    removePairAt (length xs + k) (xs ++ ys) ≡
-- -- -- --      xs ++ removePairAt k ys 
-- -- -- --  ++removePairAt k [] ys = refl
-- -- -- --  ++removePairAt k (x ∷ xs) ys =
-- -- -- --   cong (x ∷_) (++removePairAt k xs ys)

-- -- -- --  removePairAt++ : ∀ k xs ys → suc k < length xs → 
-- -- -- --    removePairAt k (xs ++ ys) ≡
-- -- -- --      removePairAt k xs ++ ys 
-- -- -- --  removePairAt++ zero (_ ∷ _ ∷ _) _ _ = refl
-- -- -- --  removePairAt++ (suc k) (x ∷ xs) ys v =
-- -- -- --    cong (x ∷_) (removePairAt++ k xs ys v)
 

-- -- -- --  removePairAt-len : ∀ xs k → suc k < length xs → 
-- -- -- --    2 + length (removePairAt k xs) ≡ length xs 
-- -- -- --  removePairAt-len (x₁ ∷ xs) (suc k) x =
-- -- -- --    cong suc (removePairAt-len xs k x)
-- -- -- --  removePairAt-len (x₁ ∷ x₂ ∷ xs) zero x = refl

-- -- -- --  redexSpan : List (Σ Bool (λ _ → A)) → Bool × A → Bool × A → Type ℓ
-- -- -- --  redexSpan xs x x' =
-- -- -- --     Σ (_ × _ × _)
-- -- -- --        λ (ls , cs , rs) → ls ++ [ x ] ++ cs ++ [ x' ] ++ rs ≡ xs

-- -- -- --  redexSpan' : _ → _ → _
-- -- -- --  redexSpan' xs x =
-- -- -- --        redexSpan xs x (map-fst not x)
-- -- -- --      ⊎ redexSpan xs (map-fst not x) x


-- -- -- --  lookup : (xs : List (Bool × A)) → ∀ k → k < length xs → (Bool × A)
-- -- -- --  lookup (x ∷ _) zero _ = x
-- -- -- --  lookup (_ ∷ xs) (suc k) = lookup xs k

-- -- -- --  _∈_ : (Bool × A) → List (Bool × A) → Type ℓ 
-- -- -- --  x ∈ xs = Σ (Σ _ _) λ (k , k<) → lookup xs k k< ≡ x

-- -- -- --  -- ∈red→span' : ∀ x r  → x ∈ evRed[] r → redexSpan' (evRed[] r) x

-- -- -- --  -- ∈red→span'-uc : ∀ x r k k< → lookup (evRed[] r) k k< ≡ x
-- -- -- --  --   → redexSpan' (evRed[] r) x
-- -- -- --  -- ∈red→span'-uc = {!!}
 
-- -- -- --  -- ∈red→span'-uc x (red· x₁ ∷↔ r) zero k< p = {!!}
-- -- -- --  -- ∈red→span'-uc x (·A x₁ ∷↔ r) zero k< p =
-- -- -- --  --   inl (([] , (evRed[] r , [])) ,
-- -- -- --  --     cong evRed[] λ i → (·A (p (~ i)) ∷↔ r))
-- -- -- --  -- ∈red→span'-uc x (red· x₁ ∷↔ r) (suc k) k< p = {!!}
-- -- -- --  -- ∈red→span'-uc x (·A x₁ ∷↔ r) (suc k) k< p = {!!}

-- -- -- --  RedIdx : Red → Type
-- -- -- --  Red[]Idx : Red[] → Type
 
-- -- -- --  RedIdx (red· x) = Red[]Idx x
-- -- -- --  RedIdx (·A x) = Bool
 
-- -- -- --  Red[]Idx ↔ = ⊥
-- -- -- --  Red[]Idx (x ∷↔ r) = RedIdx x ⊎ Red[]Idx r

-- -- -- --  lookupRed[] : ∀ r → Red[]Idx r → Bool × A
-- -- -- --  lookupRed : ∀ r → RedIdx r → Bool × A
 
-- -- -- --  lookupRed (red· x₁) x = lookupRed[] x₁ x
-- -- -- --  lookupRed (·A (b , a)) x = x ⊕ b , a
 
-- -- -- --  lookupRed[] (r ∷↔ _) (inl x) = lookupRed r x
-- -- -- --  lookupRed[] (_ ∷↔ r) (inr x) = lookupRed[] r x


-- -- -- --  adjRed[]Idx : ∀ r → Red[]Idx r → Red[]Idx r
 
-- -- -- --  adjRedIdx : ∀ r → RedIdx r → RedIdx r
-- -- -- --  adjRedIdx (red· x₁) x = adjRed[]Idx x₁ x
-- -- -- --  adjRedIdx (·A x₁) = not

-- -- -- --  adjRed[]Idx (x₁ ∷↔ r) =
-- -- -- --    ⊎.map (adjRedIdx x₁) (adjRed[]Idx r)
 
-- -- -- --  RedIdx/2 : Red → Type
-- -- -- --  Red[]Idx/2 : Red[] → Type

-- -- -- --  RedIdx/2 (red· x) = Red[]Idx/2 x
-- -- -- --  RedIdx/2 (·A x) = Unit
-- -- -- --  Red[]Idx/2 ↔ = ⊥
-- -- -- --  Red[]Idx/2 (x ∷↔ y) = RedIdx/2 x ⊎ Red[]Idx/2 y



-- -- -- --  Idx[]→Fin : ∀ r → (Red[]Idx r) → (Σ ℕ (_< red[]Length/2 r ℕ.· 2))
-- -- -- --  Idx[]→Fin (x₁ ∷↔ r) x = {!!}

-- -- -- --  IsoIdx[]Fin : ∀ r → Iso (Red[]Idx r) (Σ ℕ (_< red[]Length/2 r ℕ.· 2)) 
-- -- -- --  IsoIdx[]Fin ↔ = {!!}
-- -- -- --  IsoIdx[]Fin (red· x ∷↔ r) = compIso (⊎Iso (IsoIdx[]Fin x) (IsoIdx[]Fin r))
-- -- -- --     {!!} 
-- -- -- --  IsoIdx[]Fin (·A x ∷↔ r) = {!!}
-- -- -- --   -- compIso (⊎Iso {!!} (IsoIdx[]Fin r)) {!!} 



-- -- -- --  Iso[Bool×RedIdx/2]RedIdx : ∀ r → Iso (Bool × Red[]Idx/2 r) (Red[]Idx r)
-- -- -- --  Iso[Bool×RedIdx/2]RedIdx r = w
-- -- -- --   where

-- -- -- --   w→ : (Red[]Idx/2 r × Bool) → (Red[]Idx r)
-- -- -- --   w→ = {!!}
  
-- -- -- --   w : Iso _ _
-- -- -- --   Iso.fun w = {!!}
-- -- -- --   Iso.inv w = {!!}
-- -- -- --   Iso.rightInv w = {!!}
-- -- -- --   Iso.leftInv w = {!!}
  

-- -- -- --  -- AtomRedexSpansCases : ∀ r k → atomRedexAt (evRed[] r) k →
-- -- -- --  --            {!? ⊎ ?!}
-- -- -- --  -- AtomRedexSpansCases = {!!}
 
-- -- -- --  removeAtomRedex : ∀ r k → atomRedexAt (evRed[] r) k →
-- -- -- --                       Σ _ λ r' → 
-- -- -- --                        evRed[] r' ≡ (removePairAt k (evRed[] r)) 
-- -- -- --  removeAtomRedex = {!!}



-- -- -- --  subRedsEndL : ∀ ls xs ys rs → [ ls , xs , rs ]subRed ys →
-- -- -- --                  Σ Red[] λ r → evRed[] r ≡ ls ++ rs
-- -- -- --  subRedsEndL ls xs ys rs x =
-- -- -- --    h (red[]Length/2 xs) ls xs ys rs (evRedLen xs) x (atomRedexRed[]Ev xs)
-- -- -- --   where
-- -- -- --   h : ∀ n ls xs ys rs
-- -- -- --         → length (evRed[] xs) ≡ n ℕ.· 2
-- -- -- --         → [ ls , xs , rs ]subRed ys
-- -- -- --         → atomRedex (evRed[] xs) ⊎ (evRed[] xs ≡ [])
-- -- -- --         → Σ Red[] λ r → evRed[] r ≡ ls ++ rs
-- -- -- --   h zero ls xs ys rs x x₁ _ = ys ,
-- -- -- --     sym x₁ ∙  cong (ls ++_) (cong (_++ rs) (lengthZero (evRed[] xs) x))
-- -- -- --   h (suc n) ls xs ys rs x x₁ (inl (k , rat)) =
-- -- -- --    let (xs' , pXs') = removeAtomRedex xs k rat
-- -- -- --        (ys' , pYs') = removeAtomRedex ys _
-- -- -- --            (subRedsAtomRedexAt ls xs ys rs k x₁ rat)
-- -- -- --        k< = atomRedexAt<length (evRed[] xs) k rat
-- -- -- --        l= = removePairAt-len (evRed[] xs) k k< ∙ x
-- -- -- --    in h n ls xs' ys' rs (cong length pXs' ∙ injSuc (injSuc l=))
-- -- -- --       ((cong (λ zs → ls ++ zs ++ rs) pXs'
-- -- -- --          ∙∙ cong (ls ++_)
-- -- -- --           (sym (removePairAt++ k  (evRed[] xs) rs
-- -- -- --             k<))
-- -- -- --           ∙∙
-- -- -- --          sym (++removePairAt k ls (evRed[] xs ++ rs)))
-- -- -- --         ∙∙ cong (removePairAt (length ls + k)) x₁ ∙∙
-- -- -- --         sym pYs')
-- -- -- --       (atomRedexRed[]Ev xs')
-- -- -- --   h (suc n) ls xs ys rs x x₁ (inr x₂) = 
-- -- -- --     ⊥.rec (znots (cong length (sym x₂) ∙ x)) 
    


-- -- -- --  IsNormalisedEvRed[]→≡[] : ∀ x → (IsNormalised (evRed[] x)) → evRed[] x ≡ []
-- -- -- --  IsNormalisedEvRed[]→≡[] ↔ x₁ = refl
-- -- -- --  IsNormalisedEvRed[]→≡[] (red· x ∷↔ y) u =
-- -- -- --    let (x* , y*) = IsNormalised++ (evRed[] x) (evRed[] y) u
-- -- -- --        x' = IsNormalisedEvRed[]→≡[] x x*
-- -- -- --        y' = IsNormalisedEvRed[]→≡[] y y*
-- -- -- --    in cong₂ _++_ x' y'
-- -- -- --  IsNormalisedEvRed[]→≡[] (·A x ∷↔ x₂) (u , v) =
-- -- -- --   let z = IsNormalisedEvRed[]→≡[] x₂ (IsNormalised∷ᵣ _ _ v)
-- -- -- --   in ⊥.rec ( u (subst (WillReduce (fst x) (snd x))
-- -- -- --         (cong (_++ [ (not (fst x) , snd x) ]) (sym z))
-- -- -- --          ((sym (notnot _)) , refl)))
 
-- -- -- --  -- -- RED = (Bool × A) × List Red

-- -- -- --  -- -- evRED : RED → List (Bool × A)
-- -- -- --  -- -- evRED (x , y) = evRed (·A x) (flatten (Li.map (flip evRed []) y))

-- -- -- --  infix 3 _↓_ _↓∷_

-- -- -- --  _↓∷_ : (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  _↓∷_ x xs =
-- -- -- --    Σ (_ × _)  λ (redL , xsR) → ((evRed[] redL) ++ (x ∷ xsR) ≡ xs)

-- -- -- --  ↓[] : List (Bool × A) → Type ℓ
-- -- -- --  ↓[] xs = Σ _ λ r → evRed[] r ≡ xs

-- -- -- --  -- _↓_∷_ : {!!}
-- -- -- --  -- _↓_∷_ = {!!}
 
-- -- -- --  _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  xs ↓ [] = ↓[] xs
-- -- -- --  xs ↓ (x ∷ ys) =
-- -- -- --    Σ (x ↓∷ xs) λ ((_ , xsR) , _) → xsR ↓ ys 

-- -- -- --  ¬[]↓∷ : ∀ x xs  → [] ↓ x ∷ xs → ⊥ 
-- -- -- --  ¬[]↓∷ x xs (((l , r) , p) , _) =
-- -- -- --     ¬cons≡nil (++=[] (evRed[] l) (x ∷ r) p) 
 
-- -- -- --  ↓[][] : ↓[] []
-- -- -- --  fst ↓[][] = ↔
-- -- -- --  snd ↓[][] = refl

-- -- -- --  ↓refl : ∀ x → x ↓ x
-- -- -- --  ↓refl [] = ↓[][]
-- -- -- --  ↓refl (x ∷ xs) =
-- -- -- --    ((↔ , _) , refl) , ↓refl xs


-- -- -- --  ↓[]++↓ : ∀ xs ys → evRed[] xs ++ ys ↓ ys 
-- -- -- --  ↓[]++↓ xs [] = xs , sym (++-unit-r _)
-- -- -- --  ↓[]++↓ xs (x ∷ ys) =
-- -- -- --    ((xs , ys) , refl) , ↓refl ys

-- -- -- --  ↓++↓[] : ∀ xs ys → xs ++ evRed[] ys ↓ xs 
-- -- -- --  ↓++↓[] [] ys = ys , refl
-- -- -- --  ↓++↓[] (x ∷ xs) ys =
-- -- -- --   ((↔ , _) , refl) , ↓++↓[] xs ys 


-- -- -- --  open BinaryRelation

 
-- -- -- --  []↓ : ∀ xs → [] ↓ xs → xs ≡ []
-- -- -- --  []↓ [] q = refl
-- -- -- --  []↓ (x ∷ xs) (((lL , lR) , p) , q) =
-- -- -- --           let w = ++=[] _ (x ∷ lR) p
-- -- -- --            in ⊥.rec (¬cons≡nil w)

-- -- -- --  ↓++ : ∀ xs ysL ysR → xs ↓ ysL ++ ysR →
-- -- -- --           Σ (_ × _) λ (xsL ,  xsR) →
-- -- -- --              (xsL ++ xsR ≡ xs) × (xsL ↓ ysL) × (xsR ↓ ysR) 
-- -- -- --  ↓++ xs [] ysR x = ([] , xs) , refl ,
-- -- -- --    ↓[][] , x
-- -- -- --  ↓++ xs (y ∷ ysL) ysR (((wL , wR) , w) , x) =
-- -- -- --   let ((xsL' , xsR') , (p , (q , r))) = ↓++ _ ysL ysR x
-- -- -- --   in (evRed[] wL ++ y ∷ xsL' , xsR') ,
-- -- -- --         ++-assoc (evRed[] wL) _ _ ∙∙
-- -- -- --           cong ((evRed[] wL ++_) ∘ (y ∷_))
-- -- -- --             p ∙∙ w
-- -- -- --         , (((((wL) , xsL') , refl) , q) , r)


-- -- -- --  ↓trans[] : ∀ xs r → xs ↓ (evRed[] r) → ↓[] xs
-- -- -- --  ↓trans[] xs ↔ q = q
-- -- -- --  ↓trans[] xs (red· x ∷↔ r) q =
-- -- -- --     let ((x' , r') , (x'++r'≡xs , x'↓x , r'↓r)) =
-- -- -- --           ↓++ xs (evRed[] x) (evRed[] r) q
-- -- -- --         (x'' , x='') = ↓trans[] x' x x'↓x
-- -- -- --         (r'' , r='') = ↓trans[] r' r r'↓r
-- -- -- --     in (red· x'' ∷↔ r'') ,
-- -- -- --        cong₂ _++_ x='' r='' ∙ x'++r'≡xs
-- -- -- --  ↓trans[] xs (·A x ∷↔ r) q = 
-- -- -- --   let ¬x = not (fst x) , snd x
-- -- -- --       (([x] , r*++¬[x]*) , (v , v' , v'')) =
-- -- -- --         ↓++ xs [ x ] (evRed[] r ++ [ ¬x ]) q
-- -- -- --       ((r* , ¬[x]*) , (u , u' , u'')) = ↓++ r*++¬[x]* (evRed[] r) [ ¬x ] v''
-- -- -- --       (((rL , _) , f'') , (rR , f')) = u'' 
-- -- -- --       (r' , p') = ↓trans[] r* r u'
-- -- -- --       eq1 : evRed[] rL ++ ¬x ∷ evRed[] rR ≡ ¬[x]*
-- -- -- --       eq1 = cong (λ s → evRed[] rL ++ ¬x ∷ s) (f') ∙ f''
-- -- -- --       e : [x] ++ r*++¬[x]* ↓ []      
-- -- -- --       e = (red· (fst (fst (fst v'))) ∷↔
-- -- -- --              red· (·A x ∷↔ (red· r' ∷↔ rL)) ∷↔
-- -- -- --                rR) ,
-- -- -- --                   ((cong (evRed[] (fst (fst (fst q))) ++_)
-- -- -- --                     (cong (x ∷_) (
-- -- -- --                       cong (_++ evRed[] rR)
-- -- -- --                         (++-assoc _ (evRed[] rL) [ ¬x ] ∙
-- -- -- --                            cong (_++ (evRed[] rL ++ [ ¬x ])) p')
-- -- -- --                             ∙ ++-assoc ([] ++ r*)
-- -- -- --                              (evRed[] rL ++ [ ¬x ]) (evRed[] rR)))  ∙ sym (++-assoc
-- -- -- --                      (evRed[] (fst (fst (fst q)))) ([ x ] ++ r*)
-- -- -- --                   ((evRed[] rL ++ [ ¬x ]) ++ (evRed[] rR))))
-- -- -- --                     ∙
-- -- -- --                       cong₂ (_++_)
-- -- -- --                         (sym (++-assoc (evRed[] (fst (fst (fst q)))) [ x ] r*))
-- -- -- --                         (++-assoc (evRed[] rL) [ ¬x ] _))

-- -- -- --                       ∙∙

-- -- -- --                     cong₂ _++_ refl eq1 ∙∙
-- -- -- --                      (++-assoc (evRed[] (fst (fst (fst q))) ++ [ x ])
-- -- -- --                        r* _ ∙
-- -- -- --                       cong ((evRed[] (fst (fst (fst q))) ++ x ∷ []) ++_) u)  
-- -- -- --   in subst ↓[] v e
 

-- -- -- --  ↓trans : isTrans _↓_
-- -- -- --  ↓trans xs ys [] u (r , p) = 
-- -- -- --   ↓trans[] xs r (subst (xs ↓_) (sym p) u)
  
-- -- -- --  ↓trans xs ys (x ∷ zs) u (((ysL , ysR) , p) , q) =
-- -- -- --    let ((xsL , xsR) , xsL++xsR≡xs , ysL↓[] , xsR↓x∷ysR) =
-- -- -- --            ↓++ xs
-- -- -- --               (evRed[] ysL)
-- -- -- --               (x ∷ ysR)
-- -- -- --                 (subst (xs ↓_) (sym p) u)
-- -- -- --        (((ysL' , ysR') , p') , q') = xsR↓x∷ysR
-- -- -- --        (xsL' , xsL'≡) = ↓trans[] xsL ysL ysL↓[]
-- -- -- --        qq' = ↓trans ysR' ysR zs q' q
       
-- -- -- --    in ((red· xsL' ∷↔ ysL' , ysR') ,
-- -- -- --            ++-assoc (evRed[] xsL') (evRed[] ysL') (x ∷ ysR') ∙
-- -- -- --             cong₂ {x = evRed[] xsL'} _++_ xsL'≡ p' ∙ xsL++xsR≡xs
-- -- -- --            )
-- -- -- --         , qq'

-- -- -- --  _↓++↓_ : ∀ {xsL xsR ysL ysR} →
-- -- -- --     xsL ↓ ysL → xsR ↓ ysR →
-- -- -- --       xsL ++ xsR ↓ ysL ++ ysR
-- -- -- --  _↓++↓_ {xsL = []} {ysL = []} _ v = v
-- -- -- --  _↓++↓_ {xsL = []} {xsR} {(x ∷ ysL)} {ysR} u v = ⊥.rec (¬[]↓∷ _ _ u)
-- -- -- --  _↓++↓_ {xsL = (x ∷ xsL)} {xsR} {[]} {ysR} (r , p) v =
-- -- -- --    let w = ↓[]++↓ r xsR
-- -- -- --        w' = subst (λ w' → w' ++ xsR ↓ xsR) p w
-- -- -- --    in ↓trans _ _ _ w' v
-- -- -- --  _↓++↓_ {xsL = (x ∷ xsL)} {xsR} {(y ∷ ysL)} {ysR} (((uL , uR) , u) , u') v' =
-- -- -- --   let q = u' ↓++↓ v'
-- -- -- --   in ((uL , uR ++ xsR) ,
-- -- -- --     sym (++-assoc (evRed[] uL) (y ∷ uR) xsR)
-- -- -- --       ∙  cong (_++ xsR) u) , q

-- -- -- --  -- rev↓rev : ∀ xs ys → xs ↓ ys → rev xs ↓ rev ys
-- -- -- --  -- rev↓rev = {!!}
-- -- -- --  -- rev↓rev [] [] x = x
-- -- -- --  -- rev↓rev [] (x₁ ∷ ys) x = ⊥.rec (¬[]↓∷ _ _ x)
-- -- -- --  -- rev↓rev (x₁ ∷ xs) [] x = {!!}
-- -- -- --  -- rev↓rev (x₁ ∷ xs) (x₂ ∷ ys) x =
-- -- -- --  --  let z = ↓++↓ _ _ _ _ (rev↓rev xs ys {!!}) {!!} 
-- -- -- --  --  in {!!}
  
-- -- -- --  _↙_↘_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  xs ↙ zs ↘ ys = (zs ↓ xs) × (zs ↓ ys)

-- -- -- --  infix 3 _↙↘_


-- -- -- --  _↙↘_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  xs ↙↘ ys = Σ _ (xs ↙_↘ ys)

-- -- -- --  ↙↘sym : ∀ x y → x ↙↘ y → y ↙↘ x
-- -- -- --  ↙↘sym x y = map-snd λ (x , y) → y , x



-- -- -- --  ↙↘refl : ∀ x → x ↙↘ x
-- -- -- --  ↙↘refl = λ x → x , ↓refl x , ↓refl x

-- -- -- --  ↘[]↙→↙↘ : ∀ x y → ↓[] x → ↓[] y → x ↙↘ y
-- -- -- --  ↘[]↙→↙↘ x y (x' , px) (y' , py) =
-- -- -- --    (x ++ y)
-- -- -- --      , subst (λ y → x ++ y ↓ x) py (↓++↓[] x y')
-- -- -- --      , subst (λ x → x ++ y ↓ y) px (↓[]++↓ x' y)
 
-- -- -- --  ↘↙→↙↘ : ∀ x y z → x ↓ z → y ↓ z → x ↙↘ y
-- -- -- --  ↘↙→↙↘ x y [] = ↘[]↙→↙↘ x y
-- -- -- --  ↘↙→↙↘ xs ys (z ∷ zs)
-- -- -- --    (((xsL , xsR) , pX) , qX)
-- -- -- --    (((ysL , ysR) , pY) , qY) =
-- -- -- --   let (w , w↓xsL , w↓ysL)  = ↘[]↙→↙↘ _ _ (xsL , refl) (ysL , refl)
-- -- -- --       (ws , ws↓xsR , ws↓ysR ) = ↘↙→↙↘ _ _ _ qX qY
      
-- -- -- --   in w ++ z ∷ ws
-- -- -- --       , subst (w ++ z ∷ ws ↓_) pX
-- -- -- --          (w↓xsL ↓++↓ 
-- -- -- --            (_↓++↓_ {[ z ]} {_} {[ z ]} (↓refl [ z ]) (ws↓xsR))) 
-- -- -- --       , subst (w ++ z ∷ ws ↓_) pY
-- -- -- --          ((w↓ysL ↓++↓ 
-- -- -- --            (_↓++↓_ {[ z ]} {_} {[ z ]} (↓refl [ z ]) (ws↓ysR))))
 
-- -- -- --  ↙↘trans : ∀ x y z → x ↙↘ y → y ↙↘ z → x ↙↘ z
-- -- -- --  ↙↘trans x y z (x' , p , q) (z' , r , s) =
-- -- -- --   let (y' , p' , q') = ↘↙→↙↘ x' z' y q r
-- -- -- --   in y' , (↓trans y' x' x p' p  , ↓trans y' z' z q' s)


-- -- -- --  isEquivRel↙↘ : isEquivRel _↙↘_ 
-- -- -- --  isEquivRel.reflexive isEquivRel↙↘ = ↙↘refl
-- -- -- --  isEquivRel.symmetric isEquivRel↙↘ = ↙↘sym
-- -- -- --  isEquivRel.transitive isEquivRel↙↘ = ↙↘trans


-- -- -- --  _↙↘++↙↘_ : ∀ {xsL xsR ysL ysR} →
-- -- -- --     xsL ↙↘ ysL → xsR ↙↘ ysR →
-- -- -- --       xsL ++ xsR ↙↘ ysL ++ ysR
-- -- -- --  (_ , xl , yl) ↙↘++↙↘ (_ , xr , yr) = _ , (xl ↓++↓ xr) , (yl ↓++↓ yr)

-- -- -- --  List/↙↘ : Type ℓ
-- -- -- --  List/↙↘ = _ /₂ _↙↘_


-- -- -- --  List/↙↘· : List/↙↘ → List/↙↘ → List/↙↘
-- -- -- --  List/↙↘· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
-- -- -- --     (λ _ _ c → eq/ _ _ ∘ _↙↘++↙↘ (↙↘refl c))
-- -- -- --     (λ a _ _ → eq/ _ _ ∘ (↙↘refl a) ↙↘++↙↘_ )


-- -- -- --  rev-fst-not : List (Bool × A) → List (Bool × A)
-- -- -- --  rev-fst-not = rev ∘ Li.map (map-fst not)

-- -- -- --  invol-rev-fst-not : isInvolution rev-fst-not
-- -- -- --  invol-rev-fst-not xs =
-- -- -- --   sym (rev-map-comm (map-fst not) (rev-fst-not xs)) ∙
-- -- -- --     cong (Li.map (map-fst not))
-- -- -- --       (rev-rev (Li.map (map-fst not) xs))
-- -- -- --      ∙ map-∘ (map-fst not) (map-fst not) xs ∙
-- -- -- --      (λ i → Li.map (map-fst (λ x → notnot x i) ) xs) ∙ map-id xs
    

-- -- -- --  rev-fst-not-↓ : ∀ xs ys → xs ↓ ys → rev-fst-not xs ↓ rev-fst-not ys
-- -- -- --  rev-fst-not-↓ xs ys =
-- -- -- --    {!!}


-- -- -- --  XS++rev-fst-notXS↓[] : ∀ xs → xs ++ rev-fst-not xs ↓ []
-- -- -- --  XS++rev-fst-notXS↓[] [] = ↔ , refl
-- -- -- --  XS++rev-fst-notXS↓[] (x ∷ xs) =
-- -- -- --   let (r , p) = XS++rev-fst-notXS↓[] xs
-- -- -- --   in (·A x ∷↔ r ) , 
-- -- -- --        cong (λ xs → x  ∷ (xs ∷ʳ (not (fst x) , snd x))) p
-- -- -- --        ∙ cong (x ∷_) (++-assoc xs (rev-fst-not xs) _ ∙
-- -- -- --          cong (xs ++_) ((
-- -- -- --               (sym (cong rev (map++ (map-fst not) [ x ] xs)))) ∙
-- -- -- --                          sym (rev-++ (Li.map (map-fst not) [ x ])
-- -- -- --                               (Li.map (map-fst not) xs))))

-- -- -- --  rev-fst-notXS++XS↓[] : ∀ xs → rev-fst-not xs ++ xs ↓ []
-- -- -- --  rev-fst-notXS++XS↓[] xs =
-- -- -- --    subst (λ xs' → rev-fst-not xs ++ xs' ↓ [])
-- -- -- --       (invol-rev-fst-not xs)
-- -- -- --      (XS++rev-fst-notXS↓[] (rev-fst-not xs))

-- -- -- --  ↓→↙↘ : ∀ {xs ys} → xs ↓ ys → xs ↙↘ ys
-- -- -- --  ↓→↙↘ x = _ , ↓refl _ , x
 
-- -- -- --  rev-fst-not-↙↘ : ∀ xs ys →  xs ↙↘ ys → rev-fst-not xs ↙↘ rev-fst-not ys
-- -- -- --  rev-fst-not-↙↘ xs ys (zs , ↓xs , ↓ys) =
-- -- -- --    _ , rev-fst-not-↓ _ _ ↓xs , rev-fst-not-↓ _ _ ↓ys

-- -- -- --  List/↙↘Group : GroupStr List/↙↘
-- -- -- --  GroupStr.1g List/↙↘Group = SQ.[ [] ]
-- -- -- --  GroupStr._·_ List/↙↘Group = List/↙↘·

-- -- -- --  GroupStr.inv List/↙↘Group =
-- -- -- --    SQ.rec squash/ (SQ.[_] ∘ rev-fst-not)
-- -- -- --     λ _ _ → eq/ _ _ ∘ rev-fst-not-↙↘ _ _
-- -- -- --  GroupStr.isGroup List/↙↘Group = makeIsGroup
-- -- -- --    squash/ (SQ.elimProp3
-- -- -- --      (λ _ _ _ → squash/ _ _)
-- -- -- --       λ xs ys zs → cong SQ.[_] (sym (++-assoc xs ys zs)))
-- -- -- --    (SQ.elimProp
-- -- -- --      (λ _ → squash/ _ _)
-- -- -- --      λ xs → cong SQ.[_] (++-unit-r xs))
-- -- -- --    (SQ.elimProp
-- -- -- --      (λ _ → squash/ _ _)
-- -- -- --      λ _ → refl)
-- -- -- --    (SQ.elimProp
-- -- -- --      (λ _ → squash/ _ _)
-- -- -- --      λ xs → eq/ _ _ (↓→↙↘ {ys = []} (XS++rev-fst-notXS↓[] xs)))
-- -- -- --    (SQ.elimProp
-- -- -- --      (λ _ → squash/ _ _)
-- -- -- --      λ xs → eq/ _ _ (↓→↙↘ {ys = []} (rev-fst-notXS++XS↓[] xs)))



-- -- -- --  -- -- -- ↙↘[]lem : ∀ r xs → IsNormalised xs → evRed[] r ↓ xs → xs ≡ [] 
-- -- -- --  -- -- -- ↙↘[]lem = {!!}


 

-- -- -- --  -- -- ↙↘-norm-uniq : ∀ xs ys zs
-- -- -- --  -- --    → IsNormalised xs
-- -- -- --  -- --    → IsNormalised ys 
-- -- -- --  -- --    → xs ↙ zs ↘ ys
-- -- -- --  -- --    → xs ≡ ys  
-- -- -- --  -- -- ↙↘-norm-uniq [] ys zs nX nY (rX , rY) =
-- -- -- --  -- --   sym (↙↘[]lem (fst rX) ys nY (subst (_↓ ys) (sym (snd rX)) rY)) 
-- -- -- --  -- -- ↙↘-norm-uniq xs@(_ ∷ _) [] zs nX nY (rX , rY) =
-- -- -- --  -- --     ⊥.rec
-- -- -- --  -- --      (¬cons≡nil (↙↘[]lem (fst rY) xs nX (subst (_↓ xs) (sym (snd rY)) rX))) 
-- -- -- --  -- -- ↙↘-norm-uniq (x ∷ xs) (y ∷ ys) zs nX nY
-- -- -- --  -- --    ((((rX , zLX) , pX) , qX) ,
-- -- -- --  -- --     (((rY , zLY) , pY) , qY)) =
-- -- -- --  -- --   decRec
-- -- -- --  -- --     (λ lenRX≡lenRY →
-- -- -- --  -- --       let z = congP (λ i → drop (((evRedLen rX ∙∙
-- -- -- --  -- --             (cong (ℕ._· 2) lenRX≡lenRY) ∙∙ sym (evRedLen rY)) i))) (pX ∙ (sym pY))
-- -- -- --  -- --           z' = (sym (drop++ (evRed[] rX) _) ∙∙ z ∙∙ drop++ (evRed[] rY) _)
-- -- -- --  -- --       in cong₂ _∷_
-- -- -- --  -- --            (cons-inj₁ z')
-- -- -- --  -- --            (↙↘-norm-uniq xs ys zLX
-- -- -- --  -- --               (snd nX) (snd nY)
-- -- -- --  -- --               (qX , subst (_↓ ys) (sym (cons-inj₂ z')) qY)) )
-- -- -- --  -- --     (⊥.rec ∘ ⊎.rec {!!} {!!} ∘ ≢-split
-- -- -- --  -- --       )
-- -- -- --  -- --    (ℕ.discreteℕ (red[]Length/2 rX)
-- -- -- --  -- --                  (red[]Length/2 rY))

-- -- -- --  -- --   where
-- -- -- --  -- --    h : red[]Length/2 rX < red[]Length/2 rY → ⊥
-- -- -- --  -- --    h = {!!}
   

-- -- -- --  -- -- -- _↘_↙_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- xs ↘ zs ↙ ys = (xs ↓ zs) × (ys ↓ zs)

-- -- -- --  -- -- -- _↘↙_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- xs ↘↙ ys = Σ _ (xs ↘_↙ ys)

-- -- -- --  -- -- -- ↘↙sym : ∀ x y → x ↘↙ y → y ↘↙ x
-- -- -- --  -- -- -- ↘↙sym x y = map-snd λ (x , y) → y , x



-- -- -- --  -- -- -- ↘↙refl : ∀ x → x ↘↙ x
-- -- -- --  -- -- -- ↘↙refl = λ x → x , ↓refl x , ↓refl x

-- -- -- --  -- -- -- ↘[]↙→↘↙ : ∀ x y → ↓[] x → ↓[] y → x ↘↙ y
-- -- -- --  -- -- -- ↘[]↙→↘↙ _ _ u v = [] , u , v 

-- -- -- --  -- -- -- ↙↘→↘↙ : ∀ x y z → z ↓ x → z ↓ y → x ↘ z ↙ y
-- -- -- --  -- -- -- ↙↘→↘↙ = {!!}
 
-- -- -- --  -- -- -- -- ↘↙→↙↘ : ∀ x y z → x ↓ z → y ↓ z → x ↙↘ y
-- -- -- --  -- -- -- -- ↘↙→↙↘ x y [] = ↘[]↙→↙↘ x y
-- -- -- --  -- -- -- -- ↘↙→↙↘ xs ys (z ∷ zs)
-- -- -- --  -- -- -- --   (((xsL , xsR) , pX) , qX)
-- -- -- --  -- -- -- --   (((ysL , ysR) , pY) , qY) =
-- -- -- --  -- -- -- --  let (w , w↓xsL , w↓ysL)  = ↘[]↙→↙↘ _ _ (xsL , refl) (ysL , refl)
-- -- -- --  -- -- -- --      (ws , ws↓xsR , ws↓ysR ) = ↘↙→↙↘ _ _ _ qX qY
      
-- -- -- --  -- -- -- --  in w ++ z ∷ ws
-- -- -- --  -- -- -- --      , subst (w ++ z ∷ ws ↓_) pX
-- -- -- --  -- -- -- --         (↓++↓ _ _ _ _ w↓xsL
-- -- -- --  -- -- -- --           (↓++↓ [ z ] _ [ z ] _ (↓refl [ z ]) (ws↓xsR))) 
-- -- -- --  -- -- -- --      , subst (w ++ z ∷ ws ↓_) pY
-- -- -- --  -- -- -- --         ((↓++↓ _ _ _ _ w↓ysL
-- -- -- --  -- -- -- --           (↓++↓ [ z ] _ [ z ] _ (↓refl [ z ]) (ws↓ysR))))
 
-- -- -- --  -- -- -- -- ↙↘trans : ∀ x y z → x ↙↘ y → y ↙↘ z → x ↙↘ z
-- -- -- --  -- -- -- -- ↙↘trans x y z (x' , p , q) (z' , r , s) =
-- -- -- --  -- -- -- --  let (y' , p' , q') = ↘↙→↙↘ x' z' y q r
-- -- -- --  -- -- -- --  in y' , (↓trans y' x' x p' p  , ↓trans y' z' z q' s)


-- -- -- --  -- -- -- -- isEquivRel↙↘ : isEquivRel _↙↘_ 
-- -- -- --  -- -- -- -- isEquivRel.reflexive isEquivRel↙↘ = ↙↘refl
-- -- -- --  -- -- -- -- isEquivRel.symmetric isEquivRel↙↘ = ↙↘sym
-- -- -- --  -- -- -- -- isEquivRel.transitive isEquivRel↙↘ = ↙↘trans




-- -- -- --  -- -- -- -- List/↓ : Type ℓ
-- -- -- --  -- -- -- -- List/↓ = _ /₂ _↓_


-- -- -- --  -- -- -- -- List/↓· : List/↓ → List/↓ → List/↓
-- -- -- --  -- -- -- -- List/↓· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
-- -- -- --  -- -- -- --    (λ a b c → eq/ _ _ ∘ flip (↓++↓ _ _ _ _) (↓refl c))
-- -- -- --  -- -- -- --    (λ a b c → eq/ _ _ ∘ ↓++↓ _ _ _ _ (↓refl a))


-- -- -- --  -- -- -- -- List/↓Group : GroupStr List/↓
-- -- -- --  -- -- -- -- GroupStr.1g List/↓Group = SQ.[ [] ]
-- -- -- --  -- -- -- -- GroupStr._·_ List/↓Group = List/↓·

-- -- -- --  -- -- -- -- GroupStr.inv List/↓Group =
-- -- -- --  -- -- -- --   SQ.rec squash/ (SQ.[_] ∘ rev)
-- -- -- --  -- -- -- --    {!!}
-- -- -- --  -- -- -- -- GroupStr.isGroup List/↓Group = {!!}



-- -- -- --  -- -- -- -- module FG (freeGroupGroup : Group ℓ)
-- -- -- --  -- -- -- --           (η : A → ⟨ freeGroupGroup ⟩) where 

-- -- -- --  -- -- -- --  FreeGroup = ⟨ freeGroupGroup ⟩

-- -- -- --  -- -- -- --  open GroupStr (snd freeGroupGroup)

-- -- -- --  -- -- -- --  open GroupTheory freeGroupGroup

-- -- -- --  -- -- -- --  η* : Bool × A → FreeGroup
-- -- -- --  -- -- -- --  η* (b , a) = (if b then idfun _ else inv) (η a)

-- -- -- --  -- -- -- --  fromList' : FreeGroup → List (Bool × A) → FreeGroup
-- -- -- --  -- -- -- --  fromList' = foldr (_·_ ∘ η*) 

-- -- -- --  -- -- -- --  fromList : List (Bool × A) → FreeGroup
-- -- -- --  -- -- -- --  fromList = fromList' 1g

-- -- -- --  -- -- -- --  fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
-- -- -- --  -- -- -- --                            fromList xs · fromList ys
-- -- -- --  -- -- -- --  fromList· [] _ = sym (·IdL _)
-- -- -- --  -- -- -- --  fromList· (_ ∷ xs) _ =
-- -- -- --  -- -- -- --   cong (_ ·_) (fromList· xs _) ∙
-- -- -- --  -- -- -- --    ·Assoc _ _ _

-- -- -- --  -- -- -- --  redex-ε-η* : ∀ x x' → IsRedex x x' → η* x · η* x' ≡ 1g
-- -- -- --  -- -- -- --  redex-ε-η* (false , _) (false , _) (p , _) = ⊥.rec (false≢true p)
-- -- -- --  -- -- -- --  redex-ε-η* (false , x) (true , _) (_ , q) = 
-- -- -- --  -- -- -- --    cong (inv (η x) ·_) (cong (η) (sym q)) ∙ ·InvL (η x) 
-- -- -- --  -- -- -- --  redex-ε-η* (true , x) (false , _) (_ , q) =
-- -- -- --  -- -- -- --    cong (η x ·_) (cong (inv ∘ η) (sym q)) ∙ ·InvR (η x)
-- -- -- --  -- -- -- --  redex-ε-η* (true , _) (true , _) (p , _) = ⊥.rec (true≢false p)







-- -- -- --  -- -- -- -- -- -- -- -- -- ↓trans : isTrans _↓_
-- -- -- --  -- -- -- -- -- -- -- -- -- ↓trans xs [] zs u v = subst (xs ↓_) (sym ([]↓ zs v)) u
-- -- -- --  -- -- -- -- -- -- -- -- -- ↓trans xs (x ∷ ys) zs u v = {!!}
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- infix 3 [_]_↓'_ [_]_∷↓'_ [_]_↓∷'_ _↓∷Fst_


-- -- -- --  -- -- -- -- -- -- -- -- -- -- _↓∷Fst_ : List (Bool × A) → List (Bool × A) → Type ℓ 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- xs ↓∷Fst ys = Σ (_ × _)  λ (redL , xsR) → ((evRED redL) ++ xsR ≡ xs)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷Snd : (xs ys : List (Bool × A)) → xs ↓∷Fst ys → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷Snd = {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷Fst  = Σ (_ × _)  λ (redL , xsR) → ((evRED redL) ++ xsR ≡ xs)
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- [_]_↓∷'_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- [_]_↓'_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- [_]_∷↓'_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ

-- -- -- --  -- -- -- -- -- -- -- -- -- -- [ [] ] xs ↓∷' ys = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- [ x ∷ tx ] xs ↓∷' ys =
-- -- -- --  -- -- -- -- -- -- -- -- -- --   Σ (xs ↓∷Fst ys)
-- -- -- --  -- -- -- -- -- -- -- -- -- --      λ q → [ tx ] snd (fst q) ↓' ys 
 

 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- [ _ ] [] ∷↓' [] = Unit*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- [ _ ] [] ∷↓' _ ∷ _ = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- [ _ ] _ ∷ _ ∷↓' [] = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- [ [] ] x₁ ∷ xs ∷↓' y ∷ ys = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- [ _ ∷ tx ] x ∷ xs ∷↓' y ∷ ys =
-- -- -- --  -- -- -- -- -- -- -- -- -- --    (x ≡ y) × ([ tx ] xs ↓' ys)
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- [ tx ] xs ↓' ys =
-- -- -- --  -- -- -- -- -- -- -- -- -- --   ([ tx ] xs ↓∷' ys) ⊎.⊎
-- -- -- --  -- -- -- -- -- -- -- -- -- --     ([ tx ] xs ∷↓' ys)  

-- -- -- --  -- -- -- -- -- -- -- -- -- -- ↓∷'→len≥2 : ∀ ts xs ys → [ ts ] xs ↓∷' ys → 2 ≤ length xs  
-- -- -- --  -- -- -- -- -- -- -- -- -- -- ↓∷'→len≥2 (_ ∷ _) xs ys (((redL , xsR) , p) , _) =
-- -- -- --  -- -- -- -- -- -- -- -- -- --   let p' =  cong suc (cong (_+ length xsR)
-- -- -- --  -- -- -- -- -- -- -- -- -- --              (sym (+-suc _ _) ∙ sym (length++ (flatten (Li.map (λ x₁ → evRed x₁ []) (snd redL)))
-- -- -- --  -- -- -- -- -- -- -- -- -- --                [ (not (fst (fst redL)) , snd (fst redL)) ])) ∙ sym (length++
-- -- -- --  -- -- -- -- -- -- -- -- -- --             ((flatten (Li.map (λ x₁ → evRed x₁ []) (snd redL)) ++
-- -- -- --  -- -- -- -- -- -- -- -- -- --                (not (fst (fst redL)) , snd (fst redL)) ∷ [])
-- -- -- --  -- -- -- -- -- -- -- -- -- --                ) xsR)) ∙ cong length p
-- -- -- --  -- -- -- -- -- -- -- -- -- --   in subst (2 ≤_) p' tt   
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- open BinaryRelation

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [[]]↓'→⊥ : ∀ xs ys → [ [] ] xs ↓' ys → xs ≡ ys
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [[]]↓'→⊥ [] [] (inr x) = {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [[]]↓'→⊥ (x₁ ∷ xs) [] (inr ())
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [[]]↓'→⊥ (x₁ ∷ xs) (x₂ ∷ ys) (inr ())

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- isTrans-↓∷' : ∀ tx → isTrans [ tx ]_↓∷'_
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- isTrans-∷↓' : ∀ tx → isTrans [ tx ]_∷↓'_
-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' : ∀ tx tx' → ∀ a b c →
-- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx ] a ↓' b) →
-- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx' ] b ↓' c) →
-- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx ] a ↓' c)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- isTrans-↓∷' (x ∷ tx) xs ys zs p q = {!!}


-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷'-lem : ∀ tx → ∀ a x bL bR →
-- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx ] (x ∷ a) ∷↓' (evRED (x , bL)) ++ bR) →
-- -- -- --  -- -- -- -- -- -- -- -- -- --                       Σ (List Red × List (Bool × A))
-- -- -- --  -- -- -- -- -- -- -- -- -- --                        λ (aL , aR) →
-- -- -- --  -- -- -- -- -- -- -- -- -- --                          {!!} × ([ tx ] aR ↓' bR )
-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷'-lem = {!!}
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷' : ∀ tx tx' → ∀ a x bL bR c →
-- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx ] (x ∷ a) ∷↓' (evRED (x , bL)) ++ bR) →
-- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx' ] (evRED (x , bL)) ++ bR ↓∷' c) →
-- -- -- --  -- -- -- -- -- -- -- -- -- --                       ([ tx ] (x ∷ a) ↓∷' c)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷' tx tx' a x bL bR c = {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- tx tx' (x ∷ a) (fst₁ , []) bR [] p q = {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷' tx tx' (x ∷ a) (fst₁ , []) bR (x₁ ∷ c) p q = {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- isTrans-∷↓'-↓∷' tx tx' (x₁ ∷ a) (fst₁ , x ∷ snd₁) bR c p q = {!c!}

-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' tx [] a b c (inr x) (inl ())
-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' tx tx'@(_ ∷ _) a [] c (inr x) (inl x'@(((bL , bR) , p) , q)) =
-- -- -- --  -- -- -- -- -- -- -- -- -- --   ⊥.rec (¬cons≡nil p)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' tx@(_ ∷ _) tx'@(_ ∷ _) (ha ∷ a) (x ∷ b) c (inr u) (inl x'@((((_ , bL) , bR) , p) , q)) =
-- -- -- --  -- -- -- -- -- -- -- -- -- --  let pp = sym p ∙ cong (λ h → evRED (h , bL) ++ bR)
-- -- -- --  -- -- -- -- -- -- -- -- -- --             (cons-inj₁ p ∙ sym (fst u))
-- -- -- --  -- -- -- -- -- -- -- -- -- --  in inl (isTrans-∷↓'-↓∷' tx tx' a ha bL bR c
-- -- -- --  -- -- -- -- -- -- -- -- -- --     (subst ([ tx ] (ha ∷ a) ∷↓'_) pp u)
-- -- -- --  -- -- -- -- -- -- -- -- -- --     (subst ( [ tx' ]_↓∷' c) pp x')
-- -- -- --  -- -- -- -- -- -- -- -- -- --    )

-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' tx tx' [] [] [] (inr x) (inr _) = inr _
-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' (_ ∷ tx) [] (x₂ ∷ xs) (x₃ ∷ ys) (x₄ ∷ zs) (inr (p , q)) (inr ())
-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' (_ ∷ tx) (_ ∷ tx') (x₂ ∷ xs) (x₃ ∷ ys) (x₄ ∷ zs) (inr (p , q)) (inr (p' , q'))  = inr (p ∙ p' , isTrans-↓' tx tx' xs ys zs q q')
-- -- -- --  -- -- -- -- -- -- -- -- -- -- isTrans-↓' (_ ∷ tx) tx' xs ys zs (inl ((((rL , rs) , w) , q))) v =
-- -- -- --  -- -- -- -- -- -- -- -- -- --  let u = isTrans-↓' tx tx' rs ys zs q v
-- -- -- --  -- -- -- -- -- -- -- -- -- --  in inl (((rL , rs) , w) , u)


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- infix 3 _↓_ _∷↓_ _↓∷_

-- -- -- --  -- -- -- -- -- -- -- -- -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- xs ↓ ys = [ xs ] xs ↓' ys

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- _↓∷_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- _∷↓_ : List (Bool × A) → List (Bool × A) → Type ℓ

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷H : ∀ n → (l : List (Bool × A)) → length l ≤ n  → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓H : ∀ n → (l : List (Bool × A)) → length l ≤ n  → List (Bool × A) → Type ℓ

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷H zero _ _ _ = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓∷H (suc n) xs l≤sn xs'  =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- --      Σ (_ × _)  λ (redL , xsR) →
-- -- -- --  -- -- -- -- -- -- -- -- -- -- --     (((evRED redL) ++ xsR ≡ xs) ×
-- -- -- --  -- -- -- -- -- -- -- -- -- -- --       (↓∷H n {!!} {!!} {!!} ⊎ ↓H n xsR {!!} xs') )

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- ↓H n l x x₁ =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- --   {!!}


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- xs ↓∷ xs' = ↓∷H (length xs) xs (≤-refl (length xs)) xs'
-- -- -- --  -- -- -- -- -- -- -- -- -- -- --   -- Σ (_ × _)  λ (redL , xsR) →
-- -- -- --  -- -- -- -- -- -- -- -- -- -- --   --   (((evRED redL) ++ xsR ≡ xs) × {!? ↓ ?!} )
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [] ∷↓ [] = Unit*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- [] ∷↓ _ ∷ _ = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- _ ∷ _ ∷↓ [] = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- x ∷ xs ∷↓ x' ∷ xs' = (x ≡ x') × (xs ↓ xs')
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- xs ↓ xs' = (xs ↓∷ xs') ⊎ (xs ∷↓ xs')

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- module FG (freeGroupGroup : Group ℓ)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --           (η : A → ⟨ freeGroupGroup ⟩) where 

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  FreeGroup = ⟨ freeGroupGroup ⟩

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  open GroupStr (snd freeGroupGroup)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  open GroupTheory freeGroupGroup

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  η* : Bool × A → FreeGroup
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  η* (b , a) = (if b then idfun _ else inv) (η a)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList' : FreeGroup → List (Bool × A) → FreeGroup
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList' = foldr (_·_ ∘ η*) 

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList : List (Bool × A) → FreeGroup
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList = fromList' 1g

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --                            fromList xs · fromList ys
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList· [] _ = sym (·IdL _)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  fromList· (_ ∷ xs) _ =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --   cong (_ ·_) (fromList· xs _) ∙
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --    ·Assoc _ _ _

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* : ∀ x x' → IsRedex x x' → η* x · η* x' ≡ 1g
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (false , _) (false , _) (p , _) = ⊥.rec (false≢true p)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (false , x) (true , _) (_ , q) = 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --    cong (inv (η x) ·_) (cong (η) (sym q)) ∙ ·InvL (η x) 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (true , x) (false , _) (_ , q) =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --    cong (η x ·_) (cong (inv ∘ η) (sym q)) ∙ ·InvR (η x)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (true , _) (true , _) (p , _) = ⊥.rec (true≢false p)


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- infix 3 _↓_ _∷↓_ _↓∷_

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- _↓∷_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- _∷↓_ : List (Bool × A) → List (Bool × A) → Type ℓ

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- [] ↓∷ xs' = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ []) ↓∷ xs' = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ x' ∷ xs) ↓∷ xs' = IsRedex x x' × (xs ↓ xs')

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- [] ∷↓ [] = Unit*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- [] ∷↓ _ ∷ _ = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- _ ∷ _ ∷↓ [] = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- x ∷ xs ∷↓ x' ∷ xs' = (x ≡ x') × (xs ↓ xs')

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- xs ↓ xs' = (xs ↓∷ xs') ⊎ (xs ∷↓ xs')


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓refl : ∀ x → x ∷↓ x
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓refl : ∀ x → x ↓ x

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓refl [] = tt*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓refl (_ ∷ xs) = refl , ↓refl xs
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓refl x = ⊎.inr (∷↓refl x)


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓trans : ∀ x y z → x ∷↓ y → y ∷↓ z → x ∷↓ z
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓trans = {!!}
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans-∷↓-↓∷ :  ∀ x y z → x ∷↓ y → y ↓∷ z → x ↓ z

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans : ∀ x y z → x ↓ y → y ↓ z → x ↓ z
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans x y z (inr p) (inl q) = {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ []) (x' ∷ x₂ ∷ ys) zs (inr (fst₁ , inl ())) (inl x₁)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ []) (x' ∷ x₂ ∷ ys) zs (inr (fst₁ , inr ())) (inl x₁)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ x₃ ∷ x₄ ∷ xs) (x' ∷ x₂ ∷ ys) zs (inr (p , inl x₁)) (inl (q , r)) =    {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ x₃ ∷ xs) (x' ∷ x₂ ∷ ys) zs (inr (p , inr (p' , p''))) (inl (q , r)) =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --   inl (subst2 IsRedex {!!} {!!} q
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --     , (↓trans _ _ _ p'' r))
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans [] [] _ (inr _) (inr x) = inr x
    
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ xs) (x' ∷ ys) [] (inr p) (inr ())
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ xs) (x' ∷ ys) (z' ∷ zs) (inr (p , q)) (inr (p' , q')) =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --   inr (p ∙ p' , ↓trans _ _ _ q q' )
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans (x ∷ x₂ ∷ x₃) _ _ (inl (p , q)) r =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --    inl (p , ↓trans _ _ _ q r)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans-∷↓-↓∷ (x ∷ []) (x₃ ∷ x₄ ∷ y) z (fst₁ , inl ()) x₂
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans-∷↓-↓∷ (x ∷ []) (x₃ ∷ x₄ ∷ y) z (fst₁ , inr ()) x₂
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans-∷↓-↓∷ (x ∷ y ∷ xs) (x' ∷ y' ∷ ys) z (p , inr (p' , q')) (r , s) =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --    inl (subst2 IsRedex (sym p) (sym p') r ,
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --        ↓trans _ _ _ q' s)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- ↓trans-∷↓-↓∷ (x ∷ y ∷ u ∷ xs) (x' ∷ y' ∷ ys) z (p , inl (r' , s')) (r , s) =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --   inl (subst2 IsRedex (sym p) {!!} r ,
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- --     {!!} )
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓→≤length : ∀ xs ys → xs ↓ ys → length ys ≤ length xs
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷→<length : ∀ xs ys → xs ↓∷ ys → length ys < length xs
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓→≤length : ∀ xs ys → xs ∷↓ ys → length ys ≤ length xs

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓→≤length [] [] x = tt
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓→≤length (x₁ ∷ xs) (x₂ ∷ ys) x = ↓→≤length xs ys (snd x)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷→<length (x₁ ∷ x₂ ∷ xs) ys x =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --   <-weaken {length ys} (↓→≤length xs ys (snd x))
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓→≤length xs ys = ⊎.rec
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --   (<-weaken {length ys} ∘ ↓∷→<length xs ys)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --   (∷↓→≤length xs ys)


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷asym : ∀ xs ys → xs ↓∷ ys → ys ↓∷ xs → ⊥
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷asym xs ys p p' =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --  <-asym {length ys} (↓∷→<length xs ys p) (↓∷→<length ys xs p')

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓antisym : ∀ x y → x ∷↓ y → y ∷↓ x → x ≡ y
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓antisym : ∀ x y → x ↓ y → y ↓ x → x ≡ y


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓antisym [] [] p q = refl
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷↓antisym (_ ∷ xs) (_ ∷ ys) (p , q) (p' , q') = 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --   cong₂ _∷_ p (↓antisym xs ys q q')


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓antisym xs ys (inl x) (inl x₁) = ⊥.rec (↓∷asym _ _ x x₁)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓antisym xs ys (inl x) (inr x₁) = {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓antisym xs ys (inr x) (inl x₁) = {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓antisym xs ys (inr x) (inr x₁) = ∷↓antisym xs ys x x₁

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↙_↘_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- xs ↙ zs ↘ ys = (zs ↓ xs) × (zs ↓ ys)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↙↘_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- xs ↙↘ ys = Σ _ (xs ↙_↘ ys)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘sym : ∀ x y → x ↙↘ y → y ↙↘ x
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘sym x y = map-snd λ (x , y) → y , x

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘refl : ∀ x → x ↙↘ x
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘refl = λ x → x , ↓refl x , ↓refl x

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↘↙→↙↘ : ∀ x y z → x ↓ z → y ↓ z → x ↙↘ y
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↘↙→↙↘ = {!!}
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘trans : ∀ x y z → x ↙↘ y → y ↙↘ z → x ↙↘ z
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↙↘trans x y z (x' , p , q) (z' , r , s) =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --  let (y' , p' , q') = ↘↙→↙↘ x' z' y q r
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- --  in y' , (↓trans y' x' x p' p  , ↓trans y' z' z q' s)
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open BinaryRelation _↓_

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓EquivRel : isEquivRel
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivRel.reflexive ↓EquivRel = ↓refl
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivRel.symmetric ↓EquivRel = ↓sym
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivRel.transitive ↓EquivRel = {!!}

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↓∷_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- [] ↓∷ xs' = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ []) ↓∷ xs' = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ x' ∷ xs) ↓∷ xs' = IsRedex x x' × (xs ≡ xs')
 

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- [] ↓ xs' = ⊥*
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ xs) ↓ [] = (x ∷ xs) ↓∷ []
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (x ∷ xs) ↓ (x' ∷ xs') =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ((x ∷ xs) ↓∷ (x' ∷ xs'))
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⊎ ((x ≡ x') × (xs ↓ xs'))

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- redex∷↓ : ∀ x x' xs → IsRedex x x' → x ∷ x' ∷ xs ↓ xs
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- redex∷↓ x x' [] p = p , refl
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- redex∷↓ x x' (x₁ ∷ xs) p = inl (p , refl)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷++ : ∀ {a b x x'} c → (x ∷ a) ↓∷ (x' ∷ b) → (x ∷ a ++ c) ↓∷ (x' ∷ b ++ c)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷++ {x₁ ∷ []} c (_ , q) = ⊥.rec (¬nil≡cons q)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ↓∷++ {x₁ ∷ x₂ ∷ a} c = map-snd (cong (_++ c))
 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++L↓ : ∀ a b c → a ↓ b → a ++ c ↓ b ++ c
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++L↓ (x₁ ∷ a) (x₂ ∷ b) c =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ⊎.map (↓∷++ c) (map-snd (++L↓ a b c))
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++L↓ (x ∷ x' ∷ []) [] xs (p , _) = redex∷↓ x x' xs p 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++L↓ (x₁ ∷ x₂ ∷ x₃ ∷ a) [] c (_ , q) = ⊥.rec (¬cons≡nil q)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++R↓ : ∀ a b c → b ↓ c → a ++ b ↓ a ++ c
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++R↓ [] b c p = p
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ++R↓ (x ∷ a) b c p = inr (refl , ++R↓ a b c p)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓ : Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓ = _ /₂ _↓_


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (isSetA : isSet A) where

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsPropIsNormalised : ∀ x → isProp (IsNormalised x)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsPropIsNormalised = {!!}

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝑵 : ℙ (List (Bool × A)) 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝑵 x = IsNormalised x , IsPropIsNormalised x

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  isSet[𝟚×A] : isSet _
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  isSet[𝟚×A] = isOfHLevelList 0 (isSet× 𝟚.isSetBool isSetA)


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ηInj : ∀ a a' → Path List/↓ [ [ (true , a) ] ]/ [ [ (true , a') ] ]/ →
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             a ≡ a' 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ηInj a a' = PT.rec (isSetA _ _)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!} ∘' Iso.fun (SQ.TC.IsoTcTc' _↓_ _ _) 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w : ∀ a a' → TC.tc _↓_ ((true , a) ∷ []) ((true , a') ∷ []) → a ≡ a'
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.here (inl ()))
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.here (inr ()))
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.there [] x x₁) = {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.there ((false , a'') ∷ []) x x₁) =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.there ((true , a'') ∷ []) x x₁) =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      w _ _ x ∙ w _ _ x₁
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.there (x₂ ∷ x₃ ∷ a'') x x₁) = {!!}
      
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.tcsym x) = sym (w a' a x)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w a a' (TC.tcrefl x) = cong snd (cons-inj₁ x)
    
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓· : List/↓ → List/↓ → List/↓
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++L↓ a b c))
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++R↓ a b c))

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓ : List/↓ → List/↓ → List/↓
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++L↓ a b c))
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++R↓ a b c))


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- List/↓Group : GroupStr List/↓
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.1g List/↓Group = SQ.[ [] ]
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr._·_ List/↓Group = List/↓·

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.inv List/↓Group =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SQ.rec squash/ (SQ.[_] ∘ rev)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.isGroup List/↓Group = {!!}


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module FG (freeGroupGroup : Group ℓ)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (η : A → ⟨ freeGroupGroup ⟩) where 

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  FreeGroup = ⟨ freeGroupGroup ⟩

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open GroupStr (snd freeGroupGroup)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open GroupTheory freeGroupGroup

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  η* : Bool × A → FreeGroup
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  η* (b , a) = (if b then idfun _ else inv) (η a)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList' : FreeGroup → List (Bool × A) → FreeGroup
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList' = foldr (_·_ ∘ η*) 

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList : List (Bool × A) → FreeGroup
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList = fromList' 1g

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            fromList xs · fromList ys
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList· [] _ = sym (·IdL _)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fromList· (_ ∷ xs) _ =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cong (_ ·_) (fromList· xs _) ∙
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ·Assoc _ _ _

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* : ∀ x x' → IsRedex x x' → η* x · η* x' ≡ 1g
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (false , _) (false , _) (p , _) = ⊥.rec (false≢true p)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (false , x) (true , _) (_ , q) = 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong (inv (η x) ·_) (cong (η) (sym q)) ∙ ·InvL (η x) 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (true , x) (false , _) (_ , q) =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong (η x ·_) (cong (inv ∘ η) (sym q)) ∙ ·InvR (η x)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  redex-ε-η* (true , _) (true , _) (p , _) = ⊥.rec (true≢false p)

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- 𝑵𝑭 : ⟨ freeGroupGroup ⟩ → ℙ (List (Bool × A))
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- 𝑵𝑭 a l = ((fromList l ≡ a) , is-set _ _) L.⊓
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --             𝑵 l
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- NF : ⟨ freeGroupGroup ⟩ → Type ℓ
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- NF a = ∃ (List (Bool × A))
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   λ l → (fromList l ≡ a)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     × IsNormalised l 

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module FGAlt where
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open import Cubical.HITs.FreeGroup.Alt 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open FG (freeGroupGroup A) η

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- hh : ∀ x b xs → ∀ l → {!NonEmpty (NF ((x , b) ∷ l)) → 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --          !}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- hh = {!!}

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   non∅NF : ∀ x → NonEmpty (NF x) 
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   non∅NF = ElimProp.go w
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    open ElimProp
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    w : ElimProp _
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    εB (elim₁ w) q = q ∣ [] , refl , tt* ∣₁
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∷B (elim₁ w) false a x x₁ = x₁ {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∷B (elim₁ w) true a x x₁ = {!!}
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    isPropB w = {!!}


-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (_≟_ : Discrete A) where

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsRedex? : ∀ x x' → Dec (IsRedex x x')
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsRedex? (b , x) (b' , x') =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    subst Dec (sym ΣPathP≡PathPΣ)
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (discreteΣ 𝟚._≟_ (λ _ → _≟_) (b , x) (not b' , x'))

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  WillReduce? : ∀ x xs → Dec (WillReduce (fst x) (snd x) xs)  
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  WillReduce? _ [] = no λ ()
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  WillReduce? _ (_ ∷ xs) = IsRedex? _ _

-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsNormalised? : ∀ xs → Dec (IsNormalised xs)  
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsNormalised? [] = yes _
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  IsNormalised? (x ∷ xs) =
-- -- -- --  -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Dec× (Dec¬ (WillReduce? _ _)) (IsNormalised? _) 


