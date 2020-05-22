{-# OPTIONS --cubical  #-}
module Cubical.HITs.NCube.Cub where


open import Cubical.Data.Empty renaming (rec to ⊥-rec ; elim to ⊥-elim)
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Bool renaming (_≟_ to _≟Bool_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
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

open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.Structures.Poset

open import Cubical.HITs.NCube.CompN
open import Cubical.HITs.NCube.IntervalPrim


Fin1-elim : ∀ {ℓ} → {p : Fin 1 → Type ℓ}
            → p fzero → ∀ x → p x  
Fin1-elim {p = p} x x₁ = subst p (snd isContrFin1 x₁) x


injTrim : ∀ {n} → ℕ → Fin (suc n)
injTrim zero = fzero
injTrim {zero} (suc x) = fzero
injTrim {suc n} (suc x) = fsuc (injTrim x)

decFin : ∀ {ℓ} → ∀ {n} → (p : Fin n → Type ℓ) →
             (∀ x → Dec (p x)) → Dec (∀ x → p x)
decFin {n = zero} p x = yes (⊥-rec ∘ ¬Fin0)
decFin {n = suc zero} p x with (x fzero)
... | yes p₁ = yes (Fin1-elim p₁)
... | no ¬p = no λ x₁ → ¬p (x₁ fzero)
decFin {n = suc (suc n)} p xx with decFin {n = suc n} (p ∘ fsuc) (xx ∘ fsuc)
... | yes p₁ = mapDec
               (λ x → Sum.elim
                 (λ a → subst p a x)
                 (λ b → subst p (snd b) (p₁ (fst b)) ) ∘ fsplit )
              ((λ x₁ → λ x → x₁ (x fzero))) (xx fzero)
... | no ¬p = no λ x → ¬p (x ∘ fsuc)

decRec : ∀ {ℓ ℓ'} → {A : Type ℓ} → {B : Type ℓ'}
         → (A → B) → (¬ A → B)
         → (Dec A → B)
decRec x x₁ (yes p) = x p
decRec x x₁ (no ¬p) = x₁ ¬p

decFinCase : ∀ {ℓ} → ∀ {n} → (p : Fin n → Type ℓ) →
             (∀ x → Dec (p x)) → (∀ x → p x) ⊎ Σ _ λ x → ¬ p x 
decFinCase {n = zero} p xx = inl (⊥-rec ∘ ¬Fin0)
decFinCase {n = suc zero} p xx with (xx fzero)
... | yes p₁ = inl (Fin1-elim p₁)
... | no ¬p = inr (fzero , ¬p)
decFinCase {n = suc (suc n)} p xx with decFinCase {n = suc n} (p ∘ fsuc) (xx ∘ fsuc)
... | inl x = decRec
             (λ x₁ →
                  inl (Sum.elim (λ a → subst p a x₁)
                                (λ b → subst p (snd b) (x (fst b)))
                      ∘ fsplit)
             )
             (λ x₁ → inr (fzero , x₁))
             (xx fzero)
... | inr x = inr (fsuc (fst x) , snd x)

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

n─n≡0 : ∀ n → n ─ n ≡ zero
n─n≡0 zero = refl
n─n≡0 (suc n) = n─n≡0 n

─+ : ∀ m n → ∀ k → m ≡ n ─ (toℕ {suc n} k) → m + (toℕ k) ≡ n
─+ m n (zero , snd₁) x = +-comm m zero ∙ x
─+ zero zero (suc fst₁ , snd₁) x = ⊥-rec (¬-<-zero (pred-≤-pred snd₁))
─+ (suc m) zero (suc fst₁ , snd₁) x = ⊥-rec (snotz x)
─+ zero (suc n) (suc fst₁ , snd₁) x = cong suc (─+ zero n (fst₁ , (pred-≤-pred snd₁)) x)
─+ (suc m) (suc n) (suc fst₁ , snd₁) x =
 cong suc (+-suc m fst₁) ∙ cong suc (─+ (suc m) n (fst₁ , (pred-≤-pred snd₁)) x)


suc-n─n≡1 : ∀ n → (suc n) ─ n ≡ (suc zero)
suc-n─n≡1 zero = refl
suc-n─n≡1 (suc n) = suc-n─n≡1 n

n─Fin-n : ∀ {n} → (k : Fin n) → ¬ (zero ≡ n ─ (toℕ k))
n─Fin-n {zero} = ⊥-rec ∘ ¬Fin0 
n─Fin-n {suc n} (zero , snd₁) x = ⊥-rec (znots x)
n─Fin-n {suc n} (suc fst₁ , snd₁) x = n─Fin-n {n} (fst₁ , pred-≤-pred snd₁) x

suc─ : ∀ n → ∀ m → 
          suc (n ─ suc (toℕ {n} m)) ≡ (n ─ toℕ  m)
         
suc─ zero m = ⊥-rec (¬Fin0 m)
suc─ (suc n) (zero , snd₁) = refl
suc─ (suc n) (suc fst₁ , snd₁) = suc─ n (fst₁ , pred-≤-pred snd₁)


SubFace : ℕ → Type₀
SubFace = Vec (Maybe Bool)

isFull : ∀ {n} → SubFace n → Type₀
isFull x = x ≡ repeat nothing

isFull? : ∀ {n} → ∀ x → Dec (isFull {n = n} x)
isFull? {zero} [] = yes refl
isFull? {suc n} (nothing ∷ x) = mapDec (cong (nothing ∷_)) (_∘ (cong tail)) (isFull? x)
isFull? {suc n} (just x ∷ x₁) = no (¬just≡nothing ∘ (cong head))

sfDim : ∀ {n} → SubFace n → Fin (suc n)
sfDim [] = fzero
sfDim (nothing ∷ x₁) = fsuc (sfDim x₁)
sfDim (just x ∷ x₁) = fst (sfDim x₁) , ≤-suc (snd (sfDim x₁))

sfDim-repeat : ∀ {n} → toℕ (sfDim (repeat {n = n} nothing)) ≡ n
sfDim-repeat {zero} = refl
sfDim-repeat {suc n} = cong suc sfDim-repeat


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

_⊂_ : ∀ {n} → SubFace n → SubFace n → Type₀ 
x ⊂ x₁ = (x ⊆ x₁) × ((toℕ (sfDim x)) < (toℕ (sfDim x₁)))


⊆■ : ∀ {n} → ∀ x → x ⊆ (repeat {n = n} nothing)
⊆■ [] = tt
⊆■ (x ∷ x₁) = tt , ⊆■ _


⊆-refl' : ∀ {n} → ∀ {x y} → x ≡ y → _⊆_ {n = n} x y
⊆-refl' {zero} {[]} {[]} _ = tt
⊆-refl' {suc n} {nothing ∷ x₁} {nothing ∷ y} x = tt , ⊆-refl' (cong tail x)
⊆-refl' {suc n} {nothing ∷ x₁} {just x₂ ∷ y} x = ⊥-rec (¬nothing≡just (cong head x))
⊆-refl' {suc n} {just x₁ ∷ x₂} {nothing ∷ y} x = ⊥-rec (¬just≡nothing (cong head x))
⊆-refl' {suc n} {just x₁ ∷ x₂} {just x₃ ∷ y} x = just-inj _ _ (cong head x) , ⊆-refl' (cong tail x)

⊆-refl : ∀ {n} → ∀ x → _⊆_ {n = n} x x
⊆-refl {zero} [] = tt
⊆-refl {suc n} (nothing ∷ x₁) = tt , ⊆-refl _
⊆-refl {suc n} (just x ∷ x₁) = refl , ⊆-refl _ 

⊆-trans : ∀ {n} → ∀ {x y z : SubFace n} →  x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans {x = []} {[]} {[]} a b = _
⊆-trans {x = nothing ∷ x₁} {nothing ∷ y} {nothing ∷ z} a b = tt , (⊆-trans (snd a) (snd b))
⊆-trans {x = just x ∷ x₁} {nothing ∷ y} {nothing ∷ z} a b = tt , (⊆-trans (snd a) (snd b))
⊆-trans {x = just x ∷ x₁} {just x₂ ∷ y} {nothing ∷ z} a b = tt , (⊆-trans (snd a) (snd b))
⊆-trans {x = just x ∷ x₁} {just x₂ ∷ y} {just x₃ ∷ z} a b = fst a ∙ fst b  , (⊆-trans (snd a) (snd b))

data BdFacet : (n : ℕ) → Type₀ where
     lid : ∀ n → Bool → BdFacet (suc n)
     cyl : ∀ n → Maybe Bool → BdFacet (suc n) → BdFacet (suc (suc n))

¬BdFacet0 : BdFacet 0 → ⊥
¬BdFacet0 ()



cylF' : ∀ {n} → Maybe Bool → BdFacet (n) → BdFacet (suc n)
cylF' {suc n} x x₁ = cyl _ x x₁


mkFace : ∀ {n} → (Fin n × Bool) → BdFacet n
mkFace {zero} (k , snd₁) = ⊥-rec (¬Fin0 k)
mkFace {suc n} ((zero , snd₂) , snd₁) = lid _ snd₁
mkFace {suc zero} ((suc fst₁ , snd₂) , snd₁) = ⊥-rec (¬-<-zero (pred-≤-pred snd₂))
mkFace {suc (suc n)} ((suc fst₁ , snd₂) , snd₁) =
  cyl _ nothing (mkFace ((fst₁ , pred-≤-pred snd₂) , snd₁))


facetCase : ∀ {n} → (ft : BdFacet (suc n)) →
                 (Σ (Fin (suc n) × Bool) λ x → mkFace x ≡ ft)
                 ⊎
                 (Σ (Maybe Bool × BdFacet n) λ x → cylF' (fst x) (snd x) ≡ ft)  
facetCase {zero} (lid .0 x) = inl ((fzero , x) , refl)
facetCase {suc n} (lid .(suc n) x) = inl ((fzero , x) , refl)
facetCase {suc n} (cyl .n nothing x₁) = 
  let z = facetCase x₁
  in Sum.map (λ x → ((fsuc (fst (fst x)) , snd (fst x)) ,                    
              cong (cyl n nothing ∘ mkFace)
               (λ i → toℕ-injective {fj = _ , pred-≤-pred (snd (fsuc (fst (fst x))))}
                 {fk = (fst (fst x))}
                 (λ ii → fst (fst (fst x))) i , (snd (fst x))) ∙ cong (cyl n nothing) (snd x)
               ) )
          (λ x → (nothing , cylF' (fst (fst x)) (snd (fst x))) ,
            cong (cyl n nothing) (snd x)
           ) z
facetCase {suc n} (cyl .n (just x) x₁) = inr ((just x , x₁) , refl)


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





fctDim : ∀ {n} → BdFacet n → Fin n
fctDim {.(suc n)} (lid n x) = n , (zero , refl)
fctDim {.(suc (suc n))} (cyl n nothing x₁) = fsuc (fctDim x₁)
fctDim {.(suc (suc n))} (cyl n (just x) x₁) = inject₁ (fctDim x₁)

bdInj : ∀ {n} → BdFacet n → SubFace n
bdInj (lid n x) = just x ∷ (repeat nothing)
bdInj (cyl n nothing x₁) = nothing ∷ bdInj x₁
bdInj (cyl n (just x) x₁) = (just x) ∷ bdInj x₁

fromSubFace : ∀ {n} → (sf : SubFace n) → (¬ (isFull sf)) → BdFacet n 
fromSubFace {.0} [] x = ⊥-rec (x refl)
fromSubFace {.(suc _)} (x₁ ∷ sf) x with (isFull? sf)
fromSubFace {suc _} (nothing ∷ sf) x | yes p = ⊥-rec (x (cong (nothing ∷_) p))
fromSubFace {suc _} (just x₁ ∷ sf) x | yes p = lid _ x₁
... | no ¬p = cylF' x₁ (fromSubFace _ ¬p)


fromSubFace= : ∀ {n} → (sf : SubFace n) → (¬p : ¬ (isFull sf)) → bdInj (fromSubFace sf ¬p) ≡ sf
fromSubFace= {.0} [] ¬p = ⊥-rec (¬p refl)
fromSubFace= {.(suc _)} (x ∷ sf) ¬p with (isFull? sf)
fromSubFace= {suc _} (nothing ∷ sf) ¬p | yes p = ⊥-rec (¬p (cong (nothing ∷_) p))
fromSubFace= {suc _} (just x ∷ sf) ¬p | yes p = cong (just x ∷_) (sym p)
fromSubFace= {suc zero} (x ∷ []) ¬p | no ¬p₁ = ⊥-rec (¬p₁ refl)
fromSubFace= {suc (suc n)} (nothing ∷ sf) ¬p | no ¬p₁ = cong (nothing ∷_) (fromSubFace= sf ¬p₁)
fromSubFace= {suc (suc n)} (just x ∷ sf) ¬p | no ¬p₁ = cong (just x ∷_) (fromSubFace= sf ¬p₁)

faceInj : ∀ {n} → Fin (suc n) → Bool → SubFace n → BdFacet (suc n)
faceInj f x₁ x₂ with (isFull? x₂)
... | yes p = mkFace (f , x₁)
faceInj (zero , f) x₁ x | no ¬p = cylF' (just x₁) (fromSubFace x ¬p)
faceInj (suc fst₁ , f) x₁ [] | no ¬p = ⊥-rec (¬p refl)
faceInj (suc fst₁ , f) x₁ (x ∷ x₂) | no ¬p =
  cylF' x ((fromSubFace (just x₁ ∷ x₂) λ x₃ → ¬just≡nothing (cong head x₃)))

bdInj-fromSubFace : ∀ {n} → (x : SubFace n) → ∀ ¬p → bdInj (fromSubFace x ¬p) ≡ x
bdInj-fromSubFace {zero} [] ¬p = ⊥-rec (¬p refl)
bdInj-fromSubFace {suc .0} (nothing ∷ []) ¬p = ⊥-rec (¬p refl)
bdInj-fromSubFace {suc zero} (just x ∷ []) ¬p = refl
bdInj-fromSubFace {suc (suc n)} (x ∷ x₁) ¬p with isFull? (x₁)
bdInj-fromSubFace {suc (suc n)} (nothing ∷ x₁) ¬p | yes p = ⊥-rec (¬p (cong (nothing ∷_) p))
bdInj-fromSubFace {suc (suc n)} (just x ∷ x₁) ¬p | yes p =
   cong (just x ∷_) (sym p)
bdInj-fromSubFace {suc (suc n)} (nothing ∷ x₁) ¬p | no ¬p₁ =
   cong (nothing ∷_) (bdInj-fromSubFace (x₁) ¬p₁)
bdInj-fromSubFace {suc (suc n)} (just x ∷ x₁) ¬p | no ¬p₁ =
   cong (just x ∷_) (bdInj-fromSubFace (x₁) ¬p₁)


sfDim=ftDim : ∀ {n} → (ft : BdFacet n) → toℕ (sfDim (bdInj ft)) ≡ toℕ (fctDim ft)
sfDim=ftDim (lid n x) = sfDim-repeat
sfDim=ftDim (cyl n nothing ft) = cong suc (sfDim=ftDim ft)
sfDim=ftDim (cyl n (just x) ft) = (sfDim=ftDim ft)

sfCase : ∀ {n} → (sf : SubFace n) → (toℕ (sfDim sf) ≡ n) ⊎ (Σ _ λ ft → bdInj ft ≡ sf) 
sfCase sf with (isFull? sf)
... | yes p = inl ((cong (toℕ ∘ sfDim) p) ∙ sfDim-repeat)
... | no ¬p = inr (fromSubFace sf ¬p , fromSubFace= _ _)

_⊆ft_ : ∀ {n} → BdFacet n → BdFacet n → Type₀ 
x ⊆ft x₁ = (bdInj x) ⊆ (bdInj x₁)

_⊂ft_ : ∀ {n} → BdFacet n → BdFacet n → Type₀ 
x ⊂ft x₁ = ((bdInj x) ⊆ (bdInj x₁)) × ((toℕ (fctDim x)) < (toℕ (fctDim x₁)))

⊆ft-trans : ∀ {n} → ∀ {x y z : BdFacet n} →  x ⊆ft y → y ⊆ft z → x ⊆ft z
⊆ft-trans = ⊆-trans

⊂ft-trans : ∀ {n} → ∀ {x y z : BdFacet n} →  x ⊂ft y → y ⊂ft z → x ⊂ft z
⊂ft-trans a b = (⊆ft-trans (fst a) (fst b)) , (<-trans (snd a) (snd b))

⊆→ft : ∀ {n} → ∀ {a b : BdFacet n } → bdInj a ⊆ bdInj b → a ⊆ft b 
⊆→ft x = x

⊆←ft : ∀ {n} → ∀ {a b : BdFacet n } → a ⊆ft b → bdInj a ⊆ bdInj b 
⊆←ft x = x

⊂→ft : ∀ {n} → ∀ {a b : BdFacet n } → bdInj a ⊂ bdInj b → a ⊂ft b 
⊂→ft {a = a} {b} x = (fst x) , transport (λ i → sfDim=ftDim a i < sfDim=ftDim b i) (snd x)
     


⊂←ft : ∀ {n} → ∀ {a b : BdFacet n } → a ⊂ft b → bdInj a ⊂ bdInj b 
⊂←ft {a = a} {b} x = (fst x) , (transport (λ i → sfDim=ftDim a (~ i) < sfDim=ftDim b (~ i)) (snd x))



isPartialBoundaryTest : ∀ {n} →  (BdFacet n → Bool) → Type₀
isPartialBoundaryTest f = ∀ sf₁ sf₂ → (sf₁ ⊆ft sf₂) →  f sf₁ ≡ false → f sf₂ ≡ false

PartialBoundary : ℕ → Type₀
PartialBoundary n = Σ _ (isPartialBoundaryTest {n})

PartialBoundaryₖ : ℕ → ℕ → Type₀
PartialBoundaryₖ n k =
  Σ (PartialBoundary n)
  (λ pb → ∀ x → (fst pb x) ≡ true → fst(fctDim x)  ≤ k)

substFct : ∀ {n k} → n ≡ k → (ft : BdFacet n) → BdFacet k
substFct {suc n} {zero} x ft = ⊥-rec (snotz x)
substFct {suc n} {suc k} x (lid .n x₁) = lid _ x₁
substFct {suc .(suc n)} {suc zero} x (cyl n x₁ ft) = ⊥-rec (snotz (injSuc x))
substFct {suc .(suc n)} {suc (suc k)} x (cyl n x₁ ft) = cyl _ x₁ (substFct (injSuc x) ft)


¬full-⊆-bdInj : ∀ {n} → ∀ x₂ → (repeat nothing) ⊆ bdInj {n = n} x₂ → ⊥
¬full-⊆-bdInj (cyl n nothing x₂) x = ¬full-⊆-bdInj _ (snd x)

¬lid-⊆-cyl : ∀ {n} → ∀ {b} → ∀ {x₁} → ∀ {x₂}
                 → lid _ b ⊆ft BdFacet.cyl n x₁ x₂ → ⊥
¬lid-⊆-cyl {x₁ = nothing} x = ¬full-⊆-bdInj _ (snd x)
¬lid-⊆-cyl {x₁ = just _} x = ¬full-⊆-bdInj _ (snd x)

¬lid-⊂ : ∀ {n} → ∀ {b} → ∀ {x}
                 → lid n b ⊂ft x → ⊥
¬lid-⊂ {x = lid _ x} x₁ = ¬m<m (snd x₁)
¬lid-⊂ {x = cyl n x x₁} = ¬lid-⊆-cyl ∘ fst

⊆-case : ∀ {n} → {x y : SubFace n} → x ⊆ y → (x ≡ y) ⊎ (x ⊂ y)
⊆-case {zero} {[]} {[]} _ = inl refl
⊆-case {suc n} {nothing ∷ x₁} {nothing ∷ y} (h , t) =
  Sum.map (cong (nothing ∷_)) (λ x → (tt , fst x) , (suc-≤-suc (snd x))) (⊆-case t)
⊆-case {suc n} {just x ∷ x₁} {nothing ∷ y} (h , t) =
  inr (Sum.elim (λ a → (tt , t) , zero , (cong (suc ∘ fst ∘ sfDim) a))
      (λ b → (tt , t) , (≤-suc (snd b)))
      (⊆-case t))
⊆-case {suc n} {just false ∷ x₁} {just false ∷ y} (h , t) =
  Sum.map (cong ((just false) ∷_)) (λ x → (refl , t) , (snd x)) (⊆-case t)
⊆-case {suc n} {just false ∷ x₁} {just true ∷ y} (h , t) =  ⊥-rec (false≢true h)
⊆-case {suc n} {just true ∷ x₁} {just false ∷ y} (h , t) = ⊥-rec (true≢false h)
⊆-case {suc n} {just true ∷ x₁} {just true ∷ y} (h , t) =
  Sum.map (cong ((just true) ∷_)) (λ x → (refl , t) , (snd x)) (⊆-case t)

bdInj-injective : ∀ {n} → ∀ (x y : BdFacet n) → bdInj x ≡ bdInj y → x ≡ y 
bdInj-injective {zero} () y x₁
bdInj-injective {suc n} (lid .n x) (lid .n x₂) x₁ = cong (lid n) (just-inj _ _ (cong head x₁))
bdInj-injective {suc .(suc n)} (lid .(suc n) x) (cyl n nothing y) x₁ =
  ⊥-rec (¬just≡nothing (cong head x₁))
bdInj-injective {suc .(suc n)} (lid .(suc n) x) (cyl n (just x₂) y) x₁ =
  ⊥-rec (¬full-⊆-bdInj _ (⊆-refl' (cong tail x₁)))
bdInj-injective {suc .(suc n)} (cyl n nothing x₂) (lid .(suc n) x₃) x₁ =
  ⊥-rec (¬nothing≡just (cong head x₁))
bdInj-injective {suc .(suc n)} (cyl n (just x) x₂) (lid .(suc n) x₃) x₁ =
  ⊥-rec (¬full-⊆-bdInj _ (⊆-refl' (cong tail (sym x₁))))

bdInj-injective {suc .(suc n)} (cyl n nothing x₂) (cyl .n nothing y) x₁ i =
  cyl n nothing ((bdInj-injective _ _ (cong tail x₁)) i)

bdInj-injective {suc .(suc n)} (cyl n nothing x₂) (cyl .n (just x) y) x₁ =
  ⊥-rec (¬nothing≡just (cong head x₁))
bdInj-injective {suc .(suc n)} (cyl n (just x) x₂) (cyl .n nothing y) x₁ =
  ⊥-rec (¬just≡nothing (cong head x₁))
bdInj-injective {suc .(suc n)} (cyl n (just x) x₂) (cyl .n (just x₃) y) x₁ i =
  cyl n (just ((just-inj _ _ (cong head x₁)) i))
        (bdInj-injective _ _ (cong tail x₁) i)

⊆ft-case : ∀ {n} → {x y : BdFacet n} → x ⊆ft y → (x ≡ y) ⊎ (x ⊂ft y) 
⊆ft-case {x = x} {y} z =
 Sum.map (bdInj-injective _ _)
 (λ x₂ → (fst x₂) , (fst (snd x₂)) , (cong (fst (snd x₂) +_) (cong suc (sym (sfDim=ftDim x)) ) ∙ snd (snd x₂) ∙ sfDim=ftDim y ))
 (⊆-case z)

fctProj :  ∀ {n}
           → (ft ft' : BdFacet n)
           → ft' ⊆ft ft
           → BdFacet (suc (toℕ (fctDim ft))) 
fctProj {.(suc n)} (lid n x₁) ft' x = ft'
fctProj {.(suc (suc n))} (cyl n (x₁) ft) (lid .(suc n) x₂) x = ⊥-rec (¬lid-⊆-cyl x)

fctProj {.(suc (suc n))} (cyl n nothing ft) (cyl .n nothing ft') x =
     cyl _ nothing (fctProj ft ft' (snd x))

fctProj {.(suc (suc n))} (cyl n nothing ft) (cyl .n (just x₁) ft') x =
     cyl _ (just x₁) (fctProj ft ft' (snd x))

fctProj {.(suc (suc n))} (cyl n (just x₁) ft) (cyl .n (just x₂) ft') x =
    fctProj ft ft' (snd x)


fctProjSF :  ∀ {n}
           → (ft ft' : BdFacet n)
           → ft' ⊆ft ft
           → SubFace (toℕ (fctDim ft)) 
fctProjSF (lid zero x₁) ft' x = []
fctProjSF (lid (suc n) x₁) (lid .(suc n) x₂) x = repeat nothing
fctProjSF (lid (suc n) x₁) (cyl .n (just x₂) ft') x = bdInj ft'
fctProjSF (cyl n x₁ ft) (lid .(suc n) x₂) x = ⊥-rec (¬lid-⊆-cyl x)
fctProjSF (cyl n nothing ft) (cyl .n nothing ft') x = nothing ∷ fctProjSF ft ft' (snd x)
fctProjSF (cyl n nothing ft) (cyl .n (just x₁) ft') x = just x₁ ∷ fctProjSF ft ft' (snd x)
fctProjSF (cyl n (just x₁) ft) (cyl .n (just x₂) ft') x = fctProjSF ft ft' (snd x)


fctProj⊂ :  ∀ {n}
           → (ft ft' : BdFacet n)
           → ft' ⊂ft ft
           → BdFacet (toℕ (fctDim ft)) 
fctProj⊂ ft (lid n x₁) = ⊥-rec ∘ ¬lid-⊂

fctProj⊂ (lid .(suc n) x₂) (cyl n (just x₁) ft') x = ft'
fctProj⊂ (cyl .n nothing ft) (cyl n nothing ft') x =
    cylF' nothing (fctProj⊂ ft ft' ((snd (fst x)) , (pred-≤-pred (snd x))))
fctProj⊂ (cyl .n nothing ft) (cyl n (just x₁) ft') x =
  fctProj ft ft' (snd (fst x))
fctProj⊂ (cyl .n (just x₂) ft) (cyl n (just x₁) ft') x =
    (fctProj⊂ ft ft' ((snd (fst x)) , snd x))


fctInj' : ∀ {n k} → (ft : BdFacet n) → k ≡ toℕ (fctDim ft) →  BdFacet (k) → BdFacet n

fctInj' {suc n} {suc k} (lid .n x₂) x x₁ = cylF' (just x₂) (substFct x x₁)

fctInj' {suc .(suc n)} {suc k} (cyl n (just x₂) ft) x x₁ = cyl _ (just x₂) (fctInj' ft x x₁)

fctInj' {suc .(suc n)} {suc k} (cyl n nothing ft) x x₁ with (facetCase x₁)
fctInj' {suc (suc n)} {suc k} (cyl n nothing ft) x _ | inl (((zero , x₂) , snd₁) , _) =
       (cyl _ (just snd₁) ft)
fctInj' {suc (suc n)} {suc k} (cyl n nothing ft) x _ | inl (((suc fst₁ , x₂) , snd₁) , _) =
       cyl _ nothing (fctInj' ft (injSuc x) (mkFace ((fst₁ , pred-≤-pred x₂) , snd₁)))
fctInj' {suc (suc n)} {suc k} (cyl n nothing ft) x _ | inr ((fst₁ , snd₁) , _) =
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
fctInj⊂' {suc (suc n)} {suc k} (cyl n nothing ft) ft' p | inl (((zero , x) , snd₁) , _) = ⊆-refl _
fctInj⊂' {suc (suc n)} {suc k} (cyl n nothing ft) ft' p | inl (((suc fst₁ , x) , snd₁) , _) =
                                                               tt , fctInj⊂' _ _ (injSuc p)
fctInj⊂' {suc (suc n)} {suc k} (cyl n nothing ft) ft' p | inr ((nothing , snd₁) , _) =
   _ , (fctInj⊂' ft snd₁ (injSuc p))
fctInj⊂' {suc (suc n)} {suc k} (cyl n nothing ft) ft' p | inr ((just x , snd₁) , _) =
    _ , (fctInj⊂' ft snd₁ (injSuc p))

fctInj⊂' {suc .(suc n)} {suc k} (cyl n (just x) ft) ft' p = refl , fctInj⊂' _ _ p



postulate fctDim-fctInj' : ∀ {n k} → (ft : BdFacet n) → (ft' : BdFacet k)
            →  ∀ p 
            →  toℕ (fctDim ft') ≡ toℕ (fctDim (fctInj' ft p ft'))
-- fctDim-fctInj' {suc zero} {suc k} (lid .0 x) ft' p = ⊥-rec (snotz p)
-- fctDim-fctInj' {suc (suc n)} {suc k} (lid .(suc n) x) ft' p = {!!}
-- fctDim-fctInj' {suc .(suc n)} {suc k} (cyl n (just x) ft) ft' p = fctDim-fctInj' ft ft' p
-- fctDim-fctInj' {suc .(suc n)} {suc k} (cyl n nothing ft) ft' p  with (facetCase ft')
-- ... | inl (((zero , x) , snd₁) , e) = sym (injSuc ((sym p) ∙ (cong (suc ∘ fst ∘ fctDim) e)))
-- ... | inl (((suc fst₁ , x) , snd₁) , e) =
--               {!!}
-- ... | inr (x , e) = {!!}


postulate fctInj-trans : ∀ {n k} → (ft : BdFacet n) → ∀ ft'₁ → (ft'₂ : BdFacet k)
            →  ∀ p → (b : ft'₁ ⊂ft ft'₂) 
            → (fctInj' (fctInj' ft p ft'₂) (fctDim-fctInj' ft ft'₂ p) (fctProj⊂ ft'₂ ft'₁ b))
                    ≡ (fctInj' ft p ft'₁)
--fctInj-trans ft ft'₁ ft'₂ p b = {!!}

fctInj⊂'F : ∀ {n k} → (ft : BdFacet n) → ∀ ft'₁ → (ft'₂ : BdFacet k)
            →  ∀ p → ft'₁ ⊆ft ft'₂
            →  (fctInj' {k = k} ft p ft'₁) ⊆ft (fctInj' {k = k} ft p ft'₂)
fctInj⊂'F ft ft'₁ ft'₂ p x = 

    Sum.elim {C = const _} (⊆-refl' ∘ cong _)
     (λ b →
        let z : fctInj' (fctInj' ft p ft'₂) (fctDim-fctInj' ft ft'₂ p) (fctProj⊂ ft'₂ ft'₁ b) ⊆ft
                  fctInj' ft p ft'₂
            z = fctInj⊂' ((fctInj' ft p ft'₂)) (fctProj⊂ _ _ b) ((fctDim-fctInj' ft ft'₂ p))
        in subst (_⊆ _) (cong bdInj (fctInj-trans ft ft'₁ ft'₂ p b)) z)
     (⊆ft-case x)




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


injSf₁ : ∀ {n} → ∀ (a : SubFace n) → (k : Fin (n ─ (toℕ (sfDim a))))
            → SubFace n 
injSf₁ [] (fst₁ , snd₁) = ⊥-rec (¬-<-zero snd₁)
injSf₁ (nothing ∷ a) (fst₁ , snd₁) = nothing ∷ injSf₁ a (fst₁ , snd₁)
injSf₁ (just x ∷ a) (zero , snd₁) = nothing ∷ a
injSf₁ {.1} (just x ∷ []) (suc fst₁ , snd₁) = ⊥-rec (¬-<-zero (pred-≤-pred snd₁))
injSf₁ {(suc (suc n))} (just x ∷ x₁ ∷ a) (suc fst₁ , snd₁) = 
  just x ∷ injSf₁ (x₁ ∷ a)
    (fst₁ , _ , injSuc ((sym (+-suc _ _)) ∙ snd snd₁ ∙ (sym (suc─ (suc (suc n)) (sfDim (x₁ ∷ a))))))
 

injSf₁-codim : ∀ {n} → ∀ (a : SubFace n) → (k : Fin (n ─ (toℕ (sfDim a))))
                → (toℕ (sfDim (injSf₁ a k))) ≡ suc (toℕ (sfDim a))
injSf₁-codim [] (fst₁ , snd₁) =  ⊥-rec (¬-<-zero snd₁)
injSf₁-codim (nothing ∷ a) k = cong suc (injSf₁-codim a k)
injSf₁-codim (_∷_ {n} (just x) a) (zero , snd₁) = refl
injSf₁-codim {.1} (_∷_ {zero} (just x) []) (suc fst₁ , snd₁) = ⊥-rec (¬-<-zero (pred-≤-pred snd₁))
injSf₁-codim {.(suc (suc n))} (_∷_ {suc n} (just x) (x₁ ∷ a)) (suc fst₁ , snd₁) =
    ((injSf₁-codim (x₁ ∷ a) (fst₁ , _ , injSuc ((sym (+-suc _ _)) ∙ snd snd₁ ∙ (sym (suc─ (suc (suc n))        (sfDim (x₁ ∷ a)))))))) 


injSf₁-⊂ : ∀ {n} → ∀ (a : SubFace n) → (k : Fin (n ─ (toℕ (sfDim a))))
            → a ⊂ injSf₁ a k 
injSf₁-⊂ [] (fst₁ , snd₁) =  ⊥-rec (¬-<-zero snd₁)
injSf₁-⊂ (nothing ∷ a) (fst₁ , snd₁) =
 let z =  injSf₁-⊂  a (fst₁ , snd₁)
 in (_ , (fst z)) ,  suc-≤-suc (snd z)
injSf₁-⊂ (just x ∷ a) (zero , snd₁) =
  (_ , ⊆-refl a) , ≤-refl
injSf₁-⊂ (_∷_ {zero} (just x) []) (suc fst₁ , snd₁) = ⊥-rec (¬-<-zero (pred-≤-pred snd₁))
injSf₁-⊂ (_∷_ {suc n} (just x) (x₁ ∷ a)) (suc fst₁ , snd₁) = 
 let z =  injSf₁-⊂ (x₁ ∷ a) ((fst₁ , _ , injSuc ((sym (+-suc _ _)) ∙ snd snd₁ ∙ (sym (suc─ (suc (suc n)) (sfDim (x₁ ∷ a)))))))
 in (refl , fst z) , (snd z)

injFct₁ : ∀ {n} → ∀ (a : BdFacet n) → suc (toℕ (fctDim a)) < n → (k : Fin (n ─ (toℕ (fctDim a))))
            → BdFacet n 
injFct₁ {suc n} a x k =
  let qq = (injSf₁ (bdInj a) (subst (λ x₁ → Fin (suc n ─ x₁)) (sym (sfDim=ftDim a)) k)) in
  fromSubFace
  (qq)
  λ x₁ →
     let z = injSf₁-codim (bdInj a) (subst (λ x₁ → Fin (suc n ─ x₁)) (sym (sfDim=ftDim a)) k)
         zz =  (cong (toℕ ∘ sfDim) x₁) ∙ sfDim-repeat {suc n}
         zzz  = cong suc (sym ((sfDim=ftDim a))) ∙ sym z ∙ zz
     in ¬m<m (subst (_< suc n) zzz x)
 

⊂-injSf₁ : ∀ {n} → ∀ (a b : SubFace n) →  a ⊂ b →
                  Σ (Fin (n ─ toℕ (sfDim a))) λ k → (injSf₁ a k) ⊆ b 
⊂-injSf₁ [] [] (fst₁ , snd₁) = ⊥-rec (¬m<m snd₁)
⊂-injSf₁ (nothing ∷ a) (nothing ∷ b) x =
  let (k , zz) = ⊂-injSf₁ a b ((snd (fst x)) , pred-≤-pred (snd x))
  in k  , tt , zz 
⊂-injSf₁ (just x₁ ∷ []) (nothing ∷ []) x = fzero , (_ , _)
⊂-injSf₁ {suc n} (just x₁ ∷ x₂ ∷ a) (nothing ∷ x₃ ∷ b) x =
 subst Fin ((suc─ (suc n) (sfDim (x₂ ∷ a))) ) fzero , fst x
⊂-injSf₁ (_∷_ {.0} (just x₁) []) (just x₂ ∷ []) (fst₁ , snd₁) = ⊥-rec (¬m<m snd₁)
⊂-injSf₁ (_∷_ {.(suc _)} (just x₁) (x₃ ∷ a)) (just x₂ ∷ x₄ ∷ b) x =
  let (k , zz) = ⊂-injSf₁ (x₃ ∷ a) (x₄ ∷ b) ((snd (fst x)) , (snd x))
  in (subst Fin (suc─ (suc _) (sfDim (x₃ ∷ a))) (fsuc k)) ,
      fst (fst x) ,  subst (λ kk → injSf₁ (x₃ ∷ a) kk ⊆ (x₄ ∷ b)) (toℕ-injective refl)  zz

injFct₁-⊂ : ∀ {n} → ∀ (a : BdFacet n) → ∀ p → (k : Fin (n ─ (toℕ (fctDim a))))
            → a ⊂ft injFct₁ a p k 
injFct₁-⊂ {suc n} a x k =
  let qq = (injSf₁ (bdInj a) (subst (λ x₁ → Fin (suc n ─ x₁)) (sym (sfDim=ftDim a)) k)) 
      k' = subst (λ kk → (Fin (suc n ─ kk))) (sym (sfDim=ftDim a)) k
      z = injSf₁-⊂ (bdInj a) k'
      qz =
        λ x₁ →
          let z = injSf₁-codim (bdInj a) (subst (λ x₁ → Fin (suc n ─ x₁)) (sym (sfDim=ftDim a)) k)
              zz =  (cong (toℕ ∘ sfDim) x₁) ∙ sfDim-repeat {suc n}
              zzz  = cong suc (sym ((sfDim=ftDim a))) ∙ sym z ∙ zz
          in ¬m<m (subst (_< suc n) zzz x)
      zz = sym (bdInj-fromSubFace _ qz)
  in ⊂→ft (subst (bdInj a ⊂_) zz z)

injFct₁-codim : ∀ {n} → ∀ (a : BdFacet n) → ∀ p → (k : Fin (n ─ (toℕ (fctDim a))))
                → (toℕ (fctDim (injFct₁ a p k))) ≡ suc (toℕ (fctDim a))
injFct₁-codim {zero} () p k
injFct₁-codim {suc n} a x k =
   let qq = (injSf₁ (bdInj a) (subst (λ x₁ → Fin (suc n ─ x₁)) (sym (sfDim=ftDim a)) k)) 
       k' = subst (λ kk → (Fin (suc n ─ kk))) (sym (sfDim=ftDim a)) k
       z = injSf₁-codim (bdInj a) k'
       qz =
        λ x₁ →
          let z = injSf₁-codim (bdInj a) (subst (λ x₁ → Fin (suc n ─ x₁)) (sym (sfDim=ftDim a)) k)
              zz =  (cong (toℕ ∘ sfDim) x₁) ∙ sfDim-repeat {suc n}
              zzz  = cong suc (sym ((sfDim=ftDim a))) ∙ sym z ∙ zz
          in ¬m<m (subst (_< suc n) zzz x)
       zz =  (bdInj-fromSubFace qq qz)
       zzz = (fromSubFace
               (injSf₁ (bdInj a)
                  (subst (λ x₁ → Fin (suc n ─ x₁)) (λ i → sfDim=ftDim a (~ i)) k))
                 (λ x₁ →
                    ¬m<m
                    (subst (_< suc n)
                     ((λ i → suc (sfDim=ftDim a (~ i))) ∙
                      (λ i →
                         injSf₁-codim (bdInj a)
                         (subst (λ x₂ → Fin (suc n ─ x₂)) (λ i₁ → sfDim=ftDim a (~ i₁)) k)
                         (~ i))
                      ∙ (λ i → fst (sfDim (x₁ i))) ∙ (λ i → suc (sfDim-repeat {n = n} i)))
                     x)))
       ww = sym (sfDim=ftDim zzz)
   in (ww ∙ (cong (toℕ ∘ sfDim) zz)) ∙ z ∙ cong suc (sfDim=ftDim a)


⊂-injFct₁ : ∀ {n} → ∀ (a b : BdFacet n) →  a ⊂ft b → ∀ p →
                  Σ (Fin (n ─ (toℕ (fctDim a)))) λ k → (injFct₁ a p k) ⊆ft b 
⊂-injFct₁ {suc n} a b x p = 
  let 
      (k , z) = ⊂-injSf₁ (bdInj a) (bdInj b) (⊂←ft x)
      k' = subst (λ kk → Fin (suc n ─ kk)) (sfDim=ftDim a) k
      qq = (injSf₁ (bdInj a) (subst (λ x₁ → Fin (suc n ─ x₁)) (sym (sfDim=ftDim a)) k'))
      qz =
        λ x₁ →
          let z = injSf₁-codim (bdInj a) (subst (λ x₁ → Fin (suc n ─ x₁)) (sym (sfDim=ftDim a)) k')
              zz =  (cong (toℕ ∘ sfDim) x₁) ∙ sfDim-repeat {suc n}
              zzz  = cong suc (sym ((sfDim=ftDim a))) ∙ sym z ∙ zz
          in ¬m<m (subst (_< suc n) zzz p)
     
      ll = bdInj-fromSubFace (injSf₁ (bdInj a) _) qz ∙ cong (injSf₁ (bdInj a))
            (transportTransport⁻  (cong Fin _) _ )
  in k' ,
      ⊆→ft (subst (_⊆ bdInj b) (sym ll) z)
  
  
isPba?Help : ∀ {n} → (pb : PartialBoundary n) → ∀ a
             → (fst pb) a ≡ true → ∀ p
             → ((k : Fin (n ─ (toℕ (fctDim a))))
                  → (fst pb) (injFct₁ a p k) ≡ false)
             → isPartialBoundaryAtom pb a 
fst (isPba?Help pb a x p x₁) = x
snd (isPba?Help pb a x p x₁) sf' x₂ =
  let (k , z) = ⊂-injFct₁ _ _ x₂ p 
  in
     Sum.elim {C = const _}
       (λ a₁ → cong (fst pb) (sym a₁) ∙ x₁ k  )
       (λ b → (snd pb) _ _ z (x₁ k))
       (⊆ft-case z)

isPba?Help-no : ∀ {n} → (pb : PartialBoundary n) → ∀ a → ∀ p
             → ¬ ((k : Fin (n ─ (toℕ (fctDim a))))
                  → (fst pb) (injFct₁ a p k) ≡ false)
             → ¬ (isPartialBoundaryAtom pb a) 
isPba?Help-no pb a p x x₁ =
  x λ k → snd x₁ _ (injFct₁-⊂ a p k)


postulate maxDim→¬⊂ : ∀ {n} → (x : BdFacet n) → suc (fst (fctDim x)) ≡ n
            → ∀ y → ¬ x ⊂ft y
-- maxDim→¬⊂ x x₁ y x₂ = {!!}

isPba? : ∀ {n} → (pb : PartialBoundary n) → ∀ x → Dec (isPartialBoundaryAtom pb x)
isPba? {n} pb x with (fst pb x) ≟Bool true
... | no ¬p = no (¬p ∘ fst)
... | yes p with suc (toℕ (fctDim x)) ≟ n 
... | lt x₁ =  mapDec
              (isPba?Help pb _ p x₁)
              (isPba?Help-no pb _ x₁)
              (decFin _ λ _ → _ ≟Bool _)
... | eq x₁ = yes (p , (λ sf' x₂ → ⊥-rec ( maxDim→¬⊂ x x₁ sf' x₂ )))
... | gt x₁ = ⊥-rec (<-asym (snd (fctDim x)) (pred-≤-pred x₁))

              

¬-x≡false→x≡true : ∀ {x} → ¬ ( x ≡ false ) → x ≡ true 
¬-x≡false→x≡true {false} p = ⊥-rec (p refl)
¬-x≡false→x≡true {true} p = refl


inPBcases' : ∀ {n} → ∀ m → (pb : PartialBoundary n) → ∀ x
                → (m ≡ n ─ (toℕ (fctDim x))) → ((fst pb) x ≡ true)
                → (isPartialBoundaryAtom pb x) ⊎
                  (Σ (PartialBoundaryAtom pb) λ a → x ⊂ft fst a)
inPBcases' zero pb x x₁ x₂ = ⊥-rec (n─Fin-n (fctDim x) x₁)
inPBcases' {n} (suc zero) pb a x₁ x₂ =
   inl (x₂ ,
       (λ sf' x → ⊥-rec (maxDim→¬⊂ a (─+ _ _ (inject₁ (fctDim a)) x₁) sf' x)))
inPBcases' {n} (suc (suc m)) pb a x₁ x₂ =
  let qq = (suc─ _ (fctDim a) ∙ (sym x₁))
      q = m , (+-suc m _ ∙ +-suc (suc m) _) ∙ (─+ _ _ (inject₁ (fctDim a)) x₁)
  in
     Sum.map
      (isPba?Help pb a x₂ q)
      (λ x → Sum.elim {C = const _}
        (λ a₁ → (_ , a₁) , (injFct₁-⊂ _ q _))
        (λ b → (fst b) , (⊂ft-trans (injFct₁-⊂ _ q _) (snd b)))
        (inPBcases' {n} (suc m) pb (injFct₁ a q (fst x))
         ((cong predℕ (x₁ ∙ sym (suc─ n (fctDim a))) ∙ sym (cong (n ─_)
           (injFct₁-codim a q (fst x)))))
         ((¬-x≡false→x≡true (snd x)))))
      (decFinCase {n = (n ─ (toℕ (fctDim a)))}
        (λ x₃ → (fst pb) (injFct₁ a q x₃) ≡ false)
        λ x₃ → (fst pb) (injFct₁ a q x₃) ≟Bool false
        )


inPBcases : ∀ {n} → (pb : PartialBoundary n) → ∀ x
                → ((fst pb) x ≡ true)
                → (isPartialBoundaryAtom pb x) ⊎
                  (Σ (PartialBoundaryAtom pb) λ a → x ⊂ft fst a)
inPBcases pb x = inPBcases' _ pb x refl 

notAtomCases : ∀ {n} → (pb : PartialBoundary n) → ∀ x
                → ¬ (isPartialBoundaryAtom pb x)
                → (fst pb x ≡ false) ⊎
                  ((fst pb x ≡ true) × Σ (PartialBoundaryAtom pb) λ a → x ⊂ft fst a) 
notAtomCases pb x x₁ with dichotomyBool ((fst pb) x)
... | inl x₂ = inr (x₂ , Sum.elim {C = const _} (⊥-rec ∘ x₁) (idfun _) (inPBcases pb x x₂))
... | inr x₂ = inl x₂

atomInj : ∀ {n} → {pb : PartialBoundary n} → ∀ sf
           → (sfNotInPb : fst pb sf ≡ false)
           → (x : PartialBoundaryAtom (partialBoundaryProj pb sf)) 
           → Σ (PartialBoundaryAtom pb)
             (λ a → fctInj sf (fst x) ⊆ft fst a)
atomInj {pb = pb} sf sfNotInPb x with inPBcases pb _ (fst (snd x))
... | inl x₁ = (_ , x₁) , ⊆-refl _
... | inr (x₁ , x₂) = x₁ , fst x₂



full : ∀ n → PartialBoundary n
fst (full n) _ = true
snd (full n) sf₁ sf₂ x x₁ = x₁


-- isProp-⊆ft : ∀ {n} → {x y : BdFacet n} → isProp (x ⊆ft y)
-- isProp-⊆ft = {!!}

-- FacetsPST : ∀ n → Poset ℓ-zero ℓ-zero
-- FacetsPST n = BdFacet n ,
--                 (λ x x₁ → (x ⊆ft x₁) , isProp-⊆ft {x = x} {x₁})
--                  ,
--                  {!!} , {!!}






-- --------------- OMEGA



-- skelFaceHalf : ∀ {ℓ} → (A : Type ℓ)
--                → ∀ n → ∀ k
--                → Skelω A (suc n) (inject₁ k)
--                → Bool
--                → Skelω A n k
-- skelFaceHalf = {!!}

-- skelFaceSkel :
--            ∀ {ℓ} → (A : Type ℓ) → ∀ n → ∀ k
--            → Skelω A n k
--            → (sf : Σ (SubFace n) (λ x → toℕ (sfDim x) ≡ suc (toℕ k)))
--            → Skelω A (suc (toℕ k)) ((suc (toℕ k) ) , (1 , refl))
-- skelFaceSkel A zero (zero , snd₁) x sf i ()
-- skelFaceSkel A zero (suc zero , zero , snd₁) x ([] , snd₂) i = {!!} --!!
-- skelFaceSkel A zero (suc (suc fst₁) , zero , snd₁) x sf i = {!!} -- !!
-- skelFaceSkel A zero (suc fst₁ , suc fst₂ , snd₁) x sf i = {!snd₁!} --!!

-- skelFaceSkel A (suc n) (_ , zero , snd₁) x (fst₁ , snd₂) i = {!!}
-- skelFaceSkel A (suc n) (zero , _  , snd₁) x sf i = {!!}
-- skelFaceSkel A (suc n) (suc fst₁ , suc fst₂ , snd₁) x sf i = {!!}




-- skelFaces : ∀ {ℓ} → (A : Type ℓ)
--           → ∀ n → (k : Fin (suc (suc n)))
--           → Skelω A n k → Σ (SubFace n) (λ x → toℕ (sfDim x) ≡ suc (toℕ k))
--           → Typeω
-- skelFaces A n (zero , _ , _) x _ = Partial i1 A
-- skelFaces A n (_ , zero , _) x _ = Partial i0 A
-- skelFaces A zero (suc fst₁ , suc fst₂ , snd₁) x _ = Partial i0 A
-- skelFaces A (suc n) (suc fst₁ , suc fst₂ , snd₁) x p =
--   let fsk : Partialⁿ A ((suc (suc fst₁))) (skelExpr (suc (suc fst₁))
--                ((suc (suc fst₁)) , 1 , refl))
--       fsk = skelFaceSkel A (suc n) (suc fst₁ , suc fst₂ , snd₁) x p
--   in Subⁿ A ((suc (suc fst₁)))
--      _
--      fsk


-- Skel↑ : ∀ {ℓ} → (A : Type ℓ)
--           → ∀ n → (k : Fin (suc (suc n)))
--           → (sk : Skelω A (suc n) (inject₁ k))
--           → (∀ sf → Subⁿ A ((suc (toℕ (inject₁ k)))) _
--                ((skelFaceSkel A (suc n) (inject₁ k) sk sf)) ) 
--           → Skelω A (suc n) (fsuc k)
-- Skel↑ A n (zero , zero , snd₁) sk x = {!!} --!!
-- Skel↑ A n (zero , suc zero , snd₁) sk x = {!!} --!!
-- Skel↑ A n (zero , suc (suc fst₁) , snd₁) sk x = {!!}
-- Skel↑ A n (suc zero , snd₁) sk x = {!snd₁!}
-- Skel↑ A n (suc (suc fst₁) , snd₁) sk x = {!!}

-- Skel↑ :  ∀ {ℓ} → (A : Type ℓ) → ∀ n → ∀ k → (sk : Skelω A (suc n) ((inject₁ k)) → ?
-- Skel↑ = ?


-- --            -- → ?
-- --            --  -- (∀ sf → Subⁿ A ((suc (toℕ (inject₁ k)))) _
-- --            --  --              (skelFaceSkel A (suc n) (inject₁ k) sk sf)
-- --            --  --              )
-- -- Skel↑ = ?            



-- -- skelFaceBoundary :
-- --            ∀ {ℓ} → (A : Type ℓ) → ∀ n → ∀ k
-- --            → Skelω A (suc n) (inject₁ k)
-- --            → Bool → Fin (suc n)
-- --            → Boundaryω A (toℕ k)
-- -- skelFaceBoundary A = {!!}

-- -- -- -- ⊥-recω (snotz (cong predℕ snd₁))

-- -- -- Boundaryω-elim : ∀ {ℓ} → (A : Type ℓ) → ∀ n
-- -- --          → (sk : Skelω A (suc n) (n , 2 , refl))
-- -- --          → ((b : Bool) → (l : Fin (suc n))
-- -- --               → InsideOfω {A = A} {n = suc n}
-- -- --                 (skelFaceBoundary A n (n , 2 , {!!}) {!sk!} b l ) )
-- -- --          → Boundaryω A (suc n)
-- -- -- Boundaryω-elim = {!!}

