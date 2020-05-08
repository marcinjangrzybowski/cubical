{-# OPTIONS --cubical  #-}
module Cubical.HITs.NCube.Internalize where


open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as Sum

open import Cubical.HITs.Interval
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.Data.NatMinusOne


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.NCube.BaseVec

!! : ℕ → ℕ
!! zero = suc zero
!! (suc x) = (suc x) * !! x

2^ : ℕ → ℕ
2^ zero = suc zero
2^ (suc x) = (2^ x) * 2


_─_ :  ℕ → ℕ → ℕ
x ─ zero = x
zero ─ suc x₁ = zero
suc x ─ suc x₁ = x ─ x₁


repeat : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → A →  Vec A n
repeat {n = zero} a = []
repeat {n = suc n} a  = a ∷ (repeat a) 

SubFace : ℕ → Type₀
SubFace = Vec (Maybe Bool)

-- sfDim : ∀ {n} → SubFace n → Fin (suc n)
-- sfDim x = {!!}

-- _<MB_ : Maybe Bool → Maybe Bool → Type₀
-- _<MB_ (just x) nothing = Unit
-- _<MB_ _ _ = ⊥

_≤MB_ : Maybe Bool → Maybe Bool → Type₀
x ≤MB nothing = Unit
nothing ≤MB just x₁ = ⊥
just x ≤MB just x₁ = x ≡ x₁

_⊆_ : ∀ {n} → SubFace n → SubFace n → Type₀ 
[] ⊆ [] = Unit
(x ∷ x₁) ⊆ (x₂ ∷ x₃) = (x ≤MB x₂) × (x₁ ⊆ x₃) 

⊆■ : ∀ {n} → ∀ x → x ⊆ (repeat {n = n} nothing)
⊆■ [] = tt
⊆■ (x ∷ x₁) = tt , ⊆■ _

⊆-refl : ∀ {n} → ∀ x → _⊆_ {n = n} x x
⊆-refl {zero} [] = tt
⊆-refl {suc n} (nothing ∷ x₁) = tt , ⊆-refl _
⊆-refl {suc n} (just x ∷ x₁) = refl , ⊆-refl _ 

data BdFacet : (n : ℕ) → Type₀ where
     lid : ∀ n → Bool → BdFacet (suc n)
     cyl : ∀ n → Maybe Bool → BdFacet (suc n) → BdFacet (suc (suc n))

¬BdFacet0 : BdFacet 0 → ⊥
¬BdFacet0 ()



cylF' : ∀ {n} → Maybe Bool → BdFacet (n) → BdFacet (suc n)
cylF' {suc n} x x₁ = cyl _ x x₁

facetCase : ∀ {n} → BdFacet (suc n) → ((Fin (suc n) × Bool)) ⊎ (Maybe Bool × BdFacet n)  
facetCase {zero} (lid .0 x) = inl (fzero , x)
facetCase {suc n} (lid .(suc n) x) = inl (fzero , x)
facetCase {suc n} (cyl .n nothing x₁) =
  let z = facetCase x₁
  in Sum.map (λ x → fsuc (fst x) , snd x) (λ x → fst x , cylF' (fst x) (snd x)) z
facetCase {suc n} (cyl .n (just x) x₁) = inr (just x , x₁)


facetLidSide : ∀ {n} → BdFacet (suc n) → Bool  
facetLidSide (lid _ x) = x
facetLidSide (cyl n x x₁) = false

facetIsLid? : ∀ {n} → BdFacet (suc n) → Bool  
facetIsLid? (lid _ x) = true
facetIsLid? (cyl n x x₁) = false

lid-injective : ∀ {n} → ∀ {x y} → BdFacet.lid n x ≡ lid n y → x ≡ y
lid-injective {x = false} {false} p = refl
lid-injective {x = false} {true} p = ⊥-rec (false≢true (cong facetLidSide p ))
lid-injective {x = true} {false} p = ⊥-rec (true≢false (cong facetLidSide p ))
lid-injective {x = true} {true} p = refl

-- BdFacet-Discrete : ∀ {n} → Discrete (BdFacet n)
-- BdFacet-Discrete (lid n x) (lid .n x₁) =
--              mapDec
--             (cong (lid _))
--             (λ x₂ x₃ → x₂ (lid-injective x₃))
--             (x ≟Bool x₁)
-- BdFacet-Discrete (lid .(suc n) x) (cyl n x₁ y) = no (⊥-rec ∘ true≢false ∘ (cong facetIsLid?))
-- BdFacet-Discrete (cyl n x x₁) (lid .(suc n) x₂) = no (⊥-rec ∘ false≢true ∘ (cong facetIsLid?))
-- BdFacet-Discrete (cyl n x x₁) (cyl .n x₂ y) = {!!}



mkFace : ∀ {n} → (Fin n × Bool) → BdFacet n
mkFace {zero} (k , snd₁) = ⊥-rec (¬Fin0 k)
mkFace {suc n} ((zero , snd₂) , snd₁) = lid _ snd₁
mkFace {suc zero} ((suc fst₁ , snd₂) , snd₁) = ⊥-rec (¬-<-zero (pred-≤-pred snd₂))
mkFace {suc (suc n)} ((suc fst₁ , snd₂) , snd₁) =
  cyl _ nothing (mkFace ((fst₁ , pred-≤-pred snd₂) , snd₁))

fctDim : ∀ {n} → BdFacet n → Fin n
fctDim {.(suc n)} (lid n x) = n , (zero , refl)
fctDim {.(suc (suc n))} (cyl n nothing x₁) = fsuc (fctDim x₁)
fctDim {.(suc (suc n))} (cyl n (just x) x₁) = fst (fctDim x₁) , ≤-suc (snd (fctDim x₁))

bdInj : ∀ {n} → BdFacet n → SubFace n
bdInj (lid n x) = just x ∷ (repeat nothing)
bdInj (cyl n nothing x₁) = nothing ∷ bdInj x₁
bdInj (cyl n (just x) x₁) = (just x) ∷ bdInj x₁


_⊆ft_ : ∀ {n} → BdFacet n → BdFacet n → Type₀ 
x ⊆ft x₁ = (bdInj x) ⊆ (bdInj x₁)

_⊂ft_ : ∀ {n} → BdFacet n → BdFacet n → Type₀ 
x ⊂ft x₁ = ((bdInj x) ⊆ (bdInj x₁)) × ((toℕ (fctDim x₁)) < (toℕ (fctDim x)))


isPartialBoundaryTest : ∀ {n} →  (BdFacet n → Bool) → Type₀
isPartialBoundaryTest f = ∀ sf₁ sf₂ → (sf₁ ⊆ft sf₂) →  f sf₁ ≡ false → f sf₂ ≡ false

PartialBoundary : ℕ → Type₀
PartialBoundary n = Σ _ (isPartialBoundaryTest {n})

substFct : ∀ {n k} → n ≡ k → (ft : BdFacet n) → BdFacet k
substFct {suc n} {zero} x ft = ⊥-rec (snotz x)
substFct {suc n} {suc k} x (lid .n x₁) = lid _ x₁
substFct {suc .(suc n)} {suc zero} x (cyl n x₁ ft) = ⊥-rec (snotz (injSuc x))
substFct {suc .(suc n)} {suc (suc k)} x (cyl n x₁ ft) = cyl _ x₁ (substFct (injSuc x) ft)


¬full-⊆-bdInj : ∀ {n} → ∀ x₂ → (repeat nothing) ⊆ bdInj {n = n} x₂ → ⊥
¬full-⊆-bdInj (cyl n nothing x₂) x = ¬full-⊆-bdInj _ (snd x)

¬lid-⊆-cyl : ∀ {n} → ∀ b → ∀ x₁ → ∀ x₂
                 → lid _ b ⊆ft BdFacet.cyl n x₁ x₂ → ⊥
¬lid-⊆-cyl b nothing x₂ x = ¬full-⊆-bdInj _ (snd x)
¬lid-⊆-cyl b (just x₁) x₂ x = ¬full-⊆-bdInj _ (snd x)

⊆ft-cases : ∀ {n} → (x y : BdFacet n) → x ⊆ft y → (x ≡ y) ⊎ (x ⊂ft y) 
⊆ft-cases = {!!}

fctProj :  ∀ {n}
           → (ft ft' : BdFacet n)
           → ft' ⊆ft ft
           → BdFacet (suc (toℕ (fctDim ft))) 
fctProj {.(suc n)} (lid n x₁) ft' x = ft'
fctProj {.(suc (suc n))} (cyl n (x₁) ft) (lid .(suc n) x₂) x = ⊥-rec (¬lid-⊆-cyl _ _ _ x) -- ⊥

fctProj {.(suc (suc n))} (cyl n nothing ft) (cyl .n nothing ft') x =
     cyl _ nothing (fctProj ft ft' (snd x))

fctProj {.(suc (suc n))} (cyl n nothing ft) (cyl .n (just x₁) ft') x =
     cyl _ (just x₁) (fctProj ft ft' (snd x))

fctProj {.(suc (suc n))} (cyl n (just x₁) ft) (cyl .n (just x₂) ft') x =
    fctProj ft ft' (snd x)
    



fctInj' : ∀ {n k} → (ft : BdFacet n) → k ≡ toℕ (fctDim ft) →  BdFacet (k) → BdFacet n

fctInj' {suc n} {suc k} (lid .n x₂) x x₁ = cylF' (just x₂) (substFct x x₁)

fctInj' {suc .(suc n)} {suc k} (cyl n (just x₂) ft) x x₁ = cyl _ (just x₂) (fctInj' ft x x₁)

fctInj' {suc .(suc n)} {suc k} (cyl n nothing ft) x x₁ with (facetCase x₁)
fctInj' {suc (suc n)} {suc k} (cyl n nothing ft) x x₁ | inl ((zero , x₂) , snd₁) =
       (cyl _ (just snd₁) ft)
fctInj' {suc (suc n)} {suc k} (cyl n nothing ft) x x₁ | inl ((suc fst₁ , x₂) , snd₁) =
       cyl _ nothing (fctInj' ft (injSuc x) (mkFace ((fst₁ , pred-≤-pred x₂) , snd₁)))
fctInj' {suc (suc n)} {suc k} (cyl n nothing ft) x x₁ | inr (fst₁ , snd₁) =
       cyl _ fst₁ (fctInj' ft ((injSuc x)) snd₁)



fctInj : ∀ {n} → (ft : BdFacet n) → BdFacet (toℕ (fctDim ft)) → BdFacet n
fctInj ft x = fctInj' ft refl x


fctInj⊂' : ∀ {n k} → (ft : BdFacet n) → ∀ ft' →  ∀ p →  (fctInj' {k = k} ft p ft') ⊆ft ft 
fctInj⊂' {suc zero} {suc k} (lid .0 x) (lid .k x₁) p = ⊥-rec (snotz p)
fctInj⊂' {suc (suc n)} {suc k} (lid .(suc n) x) (lid .k x₁) p =
                                 refl , ⊆■ (bdInj (substFct p (lid k x₁)))
fctInj⊂' {suc zero} {suc .(suc n₁)} (lid .0 x) (cyl n₁ x₁ ft') p = ⊥-rec (snotz p) 
fctInj⊂' {suc (suc n)} {suc .(suc n₁)} (lid .(suc n) x) (cyl n₁ x₁ ft') p =
                                refl , ⊆■ (bdInj (substFct p (cyl n₁ x₁ ft')))

fctInj⊂' {suc .(suc n)} {suc k} (cyl n nothing ft) ft' p with (facetCase ft')
fctInj⊂' {suc (suc n)} {suc k} (cyl n nothing ft) ft' p | inl ((zero , x) , snd₁) = ⊆-refl _
fctInj⊂' {suc (suc n)} {suc k} (cyl n nothing ft) ft' p | inl ((suc fst₁ , x) , snd₁) =
                                                               tt , fctInj⊂' _ _ (injSuc p)
fctInj⊂' {suc (suc n)} {suc k} (cyl n nothing ft) ft' p | inr (nothing , snd₁) =
   _ , (fctInj⊂' ft snd₁ (injSuc p))
fctInj⊂' {suc (suc n)} {suc k} (cyl n nothing ft) ft' p | inr (just x , snd₁) =
    _ , (fctInj⊂' ft snd₁ (injSuc p))

fctInj⊂' {suc .(suc n)} {suc k} (cyl n (just x) ft) ft' p = refl , fctInj⊂' _ _ p





fctInj⊂'F : ∀ {n k} → (ft : BdFacet n) → ∀ ft'₁ → ∀ ft'₂
            →  ∀ p → ft'₁ ⊆ft ft'₂
            →  (fctInj' {k = k} ft p ft'₁) ⊆ft (fctInj' {k = k} ft p ft'₂)
fctInj⊂'F ft ft'₁ ft'₂ p x = 

    Sum.elim (λ a → {!!})
     (λ b → {!!})
     (⊆ft-cases _ _ x)



-- fctinj⊂'f {k = suc k} (lid zero x₁) ft'₁ ft'₂ p x =  ⊥-rec (snotz p)

-- fctinj⊂'f (lid (suc n) x₁) (lid n₁ x₂) (lid .n₁ x₃) p x = refl , (fst x , ⊆-refl _)
-- fctinj⊂'f (lid (suc n) x₁) (lid .(suc n₁) x₂) (cyl n₁ x₃ ft'₂) p x = refl , {!!}
-- fctinj⊂'f (lid (suc n) x₁) (cyl n₁ x₂ ft'₁) (lid .(suc n₁) x₃) p x = {!!}
-- fctinj⊂'f (lid (suc n) x₁) (cyl n₁ x₂ ft'₁) (cyl .n₁ x₃ ft'₂) p x = {!!}


--- cyl
-- fctinj⊂'f (cyl n x₁ ft) ft'₁ ft'₂ p x = {!!}





partialBoundaryProj : ∀ {n} → PartialBoundary n
                      → (sf : BdFacet n)
                      → PartialBoundary (toℕ (fctDim sf))
fst (partialBoundaryProj x sf) x₁ = fst x (fctInj sf x₁)
snd (partialBoundaryProj x sf) sf₁ sf₂ x₁ x₂ =
  (snd x) ((fctInj sf sf₁)) (fctInj sf sf₂) (fctInj⊂'F sf sf₁ sf₂ refl x₁) x₂


isPartialBoundaryAtom : ∀ {n} → PartialBoundary n → BdFacet n → Type₀
isPartialBoundaryAtom (f , _) sf = (f sf ≡ true) × (∀ sf' → (sf ⊂ft sf') → f sf' ≡ false) 

PartialBoundaryAtom : ∀ {n} → PartialBoundary n → Type₀
PartialBoundaryAtom x = Σ _ (isPartialBoundaryAtom x)


-- isPba?Help : {!!}
-- isPba?Help = {!!}

isPba? : ∀ {n} → (pb : PartialBoundary n) → ∀ x → Dec (isPartialBoundaryAtom pb x)
isPba? pb x with (fst pb x) ≟Bool true
... | no ¬p = no λ x₁ → ¬p (fst x₁)
... | yes p with {!!}
isPba? pb x | yes p | w = {!!}

notAtomCases : ∀ {n} → (pb : PartialBoundary n) → ∀ x
                → ¬ (isPartialBoundaryAtom pb x)
                → (fst pb x ≡ false) ⊎
                  ((fst pb x ≡ true) × Σ (PartialBoundaryAtom pb) λ a → x ⊂ft fst a) 
notAtomCases = {!!}

atomInj : ∀ {n} → {pb : PartialBoundary n} → ∀ sf
           → (sfNotInPb : fst pb sf ≡ false)
           → (x : PartialBoundaryAtom (partialBoundaryProj pb sf)) 
           → Σ (PartialBoundaryAtom pb)
             (λ a → fctInj sf (fst x) ⊆ft fst a)
atomInj = {!!}


-- this is not true!!
-- atomInjDim : ∀ {n} → {pb : PartialBoundary n} → ∀ sf
--            → (sfNotAtom : fst pb sf ≡ false) → ∀ x
--            → toℕ {n} (fctDim (fst (atomInj {n} {pb} sf sfNotAtom x)))
--              ≡ toℕ {toℕ (fctDim sf)} (fctDim (fst x))
-- atomInjDim = {!!}


full : ∀ n → PartialBoundary n
fst (full n) _ = true
snd (full n) sf₁ sf₂ x x₁ = x₁


-- isFromBd : ∀ {ℓ} → (A : Type ℓ) → (n : ℕ) → (f : BdFacet n → A) →  Type ℓ 
-- isFromBd A n f = {!!}



data Skel' : (n : ℕ) → Type₀ where
   holeS : ∀ {n} → Skel' n 
   compS : ∀ {n} → ∀ {ptBnd : PartialBoundary n} →
                ((ft : PartialBoundaryAtom ptBnd) → Skel' (suc (toℕ (fctDim (fst ft)))))
                → Skel' n → Skel' n

Skel'-subst : ∀ {n k} → n ≡ k →  Skel' n  → Skel' k
Skel'-subst = {!!}

skelEnd : ∀ {n} → Skel' (suc n) → Skel' (n)


skelFace : ∀ {n} → Skel' n → (ft : BdFacet n)  → Skel' (toℕ (fctDim ft))
skelFace {n} holeS ft = holeS
skelFace {n} (compS {_} {ptBnd} x x₁) ft with isPba? ptBnd ft 
... | yes p = skelEnd (x (ft , p))
... | no ¬p with notAtomCases ptBnd ft ¬p
... | inl x₂ =
      let z = λ ft₁ →
              let (a' , xx) = atomInj {pb = ptBnd} ft x₂ ft₁
                  zz = fctProj (fst a') (fctInj' ft (λ _ → toℕ (fctDim ft)) (fst ft₁)) xx
              in skelFace (x a') (zz )
      in
      compS {ptBnd = partialBoundaryProj ptBnd ft}
      ((Skel'-subst {!!}) ∘ z)
      (skelFace x₁ ft)
... | inr x₂ = {!!}

skelEnd x = skelFace x (lid _ true)

-- ... | inl x₂ =
--   let z : Skel' (suc (fst (fctDim ft)))
--       z = x {!x₂!}
--   in skelEnd z
-- ... | inr x₂ = 
--   let pb = partialBoundaryProj ptBnd ft
--       z : (ft₁ : _) → _
--       z = λ ft₁ →
--            let qq : (fst (fctDim {!!}) , {!!}) ≡ (fst (fctDim (fst ft₁)) , {!!})
--                qq = {!!}
--            in 
--            subst (Skel' ∘ suc ∘ toℕ {n} )
--            qq
--            (x (atomInj {pb = ptBnd} ft x₂ ft₁))
  
--   in compS {fst (fctDim ft)} {pb}
--       (z)
--       (skelFace x₁ ft)


-- data Skel {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
--    holeS : A → Skel A n 
--    compS : Vec (Skel A n) (2^ n) → Skel A n → Skel A n
