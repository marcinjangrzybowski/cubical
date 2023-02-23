
{-# OPTIONS --safe #-}
module Cubical.Data.FinData.Properties where

-- WARNING : fromℕ' is in triple ! => to clean !
-- sort file + mix with Fin folder

-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Transport
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Univalence
-- open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.Nat renaming (zero to ℕzero ; suc to ℕsuc
                                      ;znots to ℕznots ; snotz to  ℕsnotz)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe
open import Cubical.Data.Bool using (true;false;Dec→Bool;if_then_else_;Bool;False)
import Cubical.Data.Bool as B


open import Cubical.Data.List renaming (map to mapList) 

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Involution

open import Cubical.Relation.Nullary

open import Cubical.Structures.Pointed

open import Cubical.HITs.PropositionalTruncation as PT


open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Generators
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Instances.Bool

private
 variable
   ℓ ℓ' : Level
   A : Type ℓ
   m n k : ℕ




toℕ<n : ∀ {n} (i : Fin n) → toℕ i < n
toℕ<n {n = ℕsuc n} zero = n , +-comm n 1
toℕ<n {n = ℕsuc n} (suc i) = toℕ<n i .fst , +-suc _ _ ∙ cong ℕsuc (toℕ<n i .snd)

znots : ∀{k} {m : Fin k} → ¬ (zero ≡ (suc m))
znots {k} {m} x = subst (Fin.rec (Fin k) ⊥) x m

znotsP : ∀ {k0 k1 : ℕ} {k : k0 ≡ k1} {m1 : Fin k1}
  → ¬ PathP (λ i → Fin (ℕsuc (k i))) zero (suc m1)
znotsP p = ℕznots (congP (λ i → toℕ) p)

snotz : ∀{k} {m : Fin k} → ¬ ((suc m) ≡ zero)
snotz {k} {m} x = subst (Fin.rec ⊥ (Fin k)) x m

snotzP : ∀ {k0 k1 : ℕ} {k : k0 ≡ k1} {m0 : Fin k0}
  → ¬ PathP (λ i → Fin (ℕsuc (k i))) (suc m0) zero
snotzP p = ℕsnotz (congP (λ i → toℕ) p)

-- alternative from
fromℕ' : (n : ℕ) → (k : ℕ) → (k < n) → Fin n
fromℕ' ℕzero k infkn = ⊥.rec (¬-<-zero infkn)
fromℕ' (ℕsuc n) ℕzero infkn = zero
fromℕ' (ℕsuc n) (ℕsuc k) infkn = suc (fromℕ' n k (pred-≤-pred infkn))

toFromId' : (n : ℕ) → (k : ℕ) → (infkn : k < n) → toℕ (fromℕ' n k infkn) ≡ k
toFromId' ℕzero k infkn = ⊥.rec (¬-<-zero infkn)
toFromId' (ℕsuc n) ℕzero infkn = refl
toFromId' (ℕsuc n) (ℕsuc k) infkn = cong ℕsuc (toFromId' n k (pred-≤-pred infkn))

fromToId' : (n : ℕ) → (k : Fin n ) → (r : toℕ k < n) → fromℕ' n (toℕ k) r ≡ k
fromToId' (ℕsuc n) zero r = refl
fromToId' (ℕsuc n) (suc k) r = cong suc (fromToId' n k (pred-≤-pred r))

fromℕForce : ℕ → Fin (ℕsuc n)
fromℕForce {ℕzero} x = zero
fromℕForce {ℕsuc n} ℕzero = zero
fromℕForce {ℕsuc n} (ℕsuc x) = suc (fromℕForce x)

inj-toℕ : {n : ℕ} → {k l : Fin n} → (toℕ k ≡ toℕ l) → k ≡ l
inj-toℕ {ℕsuc n}  {zero} {zero}   x = refl
inj-toℕ {ℕsuc n}  {zero} {suc l} x = ⊥.rec (ℕznots x)
inj-toℕ {ℕsuc n} {suc k} {zero}   x = ⊥.rec (ℕsnotz x)
inj-toℕ {ℕsuc n} {suc k} {suc l}  x = cong suc (inj-toℕ (injSuc x))

inj-cong : {n : ℕ} → {k l : Fin n} → (p : toℕ k ≡ toℕ l) → cong toℕ (inj-toℕ p) ≡ p
inj-cong p = isSetℕ _ _ _ _

isPropFin0 : isProp (Fin 0)
isPropFin0 = ⊥.rec ∘ ¬Fin0

isContrFin1 : isContr (Fin 1)
isContrFin1 .fst = zero
isContrFin1 .snd zero = refl

injSucFin : ∀ {n} {p q : Fin n} → suc p ≡ suc q → p ≡ q
injSucFin {ℕsuc ℕzero} {zero} {zero} pf = refl
injSucFin {ℕsuc (ℕsuc n)} pf = cong predFin pf

injSucFinP : ∀ {n0 n1 : ℕ} {pn : n0 ≡ n1} {p0 : Fin n0} {p1 : Fin n1}
  → PathP (λ i → Fin (ℕsuc (pn i))) (suc p0) (suc p1)
  → PathP (λ i → Fin (pn i)) p0 p1
injSucFinP {one} {one} {pn} {zero} {zero} sucp =
  transport (λ j → PathP (λ i → Fin (eqn j i)) zero zero) refl
  where eqn : refl ≡ pn
        eqn = isSetℕ one one refl pn
injSucFinP {one} {ℕsuc (ℕsuc n1)} {pn} {p0} {p1} sucp = ⊥.rec (ℕznots (injSuc pn))
injSucFinP {ℕsuc (ℕsuc n0)} {one} {pn} {p0} {p1} sucp = ⊥.rec (ℕsnotz (injSuc pn))
injSucFinP {ℕsuc (ℕsuc n0)} {ℕsuc (ℕsuc n1)} {pn} {p0} {p1} sucp =
  transport (λ j → PathP (λ i → Fin (eqn j i)) p0 p1) (
      congP (λ i → predFin) (
        transport (λ j → PathP (λ i → Fin (ℕsuc (eqn (~ j) i))) (suc p0) (suc p1)) sucp
      )
    )
  where pn' : 2 + n0 ≡ 2 + n1
        pn' = cong ℕsuc (injSuc pn)
        eqn : pn' ≡ pn
        eqn = isSetℕ (2 + n0) (2 + n1) pn' pn

discreteFin : ∀{k} → Discrete (Fin k)
discreteFin zero zero = yes refl
discreteFin zero (suc y) = no znots
discreteFin (suc x) zero = no snotz
discreteFin (suc x) (suc y) with discreteFin x y
... | yes p = yes (cong suc p)
... | no ¬p = no (λ q → ¬p (injSucFin q))

isSetFin : ∀{k} → isSet (Fin k)
isSetFin = Discrete→isSet discreteFin


data biEq {n : ℕ} (i j : Fin n) : Type where
  eq  :   i ≡ j → biEq i j
  ¬eq : ¬ i ≡ j → biEq i j

data triEq {n : ℕ} (i j a : Fin n) : Type where
  leq : a ≡ i → triEq i j a
  req : a ≡ j → triEq i j a
  ¬eq : (¬ a ≡ i) × (¬ a ≡ j) → triEq i j a

biEq? : (i j : Fin n) → biEq i j
biEq? i j = case (discreteFin i j) return (λ _ → biEq i j)
              of λ { (yes p) → eq p ; (no ¬p) → ¬eq ¬p }

triEq? : (i j a : Fin n) → triEq i j a
triEq? i j a =
  case (discreteFin a i) return (λ _ → triEq i j a) of
    λ { (yes p) → leq p
      ; (no ¬p) →
          case (discreteFin a j) return (λ _ → triEq i j a) of
            λ { (yes q) → req q
              ; (no ¬q) → ¬eq (¬p , ¬q) }}


weakenRespToℕ : ∀ {n} (i : Fin n) → toℕ (weakenFin i) ≡ toℕ i
weakenRespToℕ zero = refl
weakenRespToℕ (suc i) = cong ℕsuc (weakenRespToℕ i)

toFin : {n : ℕ} (m : ℕ) → m < n → Fin n
toFin {n = ℕzero} _ m<0 = ⊥.rec (¬-<-zero m<0)
toFin {n = ℕsuc n} _ (ℕzero , _) = fromℕ n --in this case we have m≡n
toFin {n = ℕsuc n} m (ℕsuc k , p) = weakenFin (toFin m (k , cong predℕ p))

toFin0≡0 : {n : ℕ} (p : 0 < ℕsuc n) → toFin 0 p ≡ zero
toFin0≡0 (ℕzero , p) = subst (λ x → fromℕ x ≡ zero) (cong predℕ p) refl
toFin0≡0 {ℕzero} (ℕsuc k , p) = ⊥.rec (ℕsnotz (+-comm 1 k ∙ (cong predℕ p)))
toFin0≡0 {ℕsuc n} (ℕsuc k , p) =
         subst (λ x → weakenFin x ≡ zero) (sym (toFin0≡0 (k , cong predℕ p))) refl

genδ-FinVec : (n k : ℕ) → (a b : A) → FinVec A n
genδ-FinVec (ℕsuc n) ℕzero a b zero = a
genδ-FinVec (ℕsuc n) ℕzero a b (suc x) = b
genδ-FinVec (ℕsuc n) (ℕsuc k) a b zero = b
genδ-FinVec (ℕsuc n) (ℕsuc k) a b (suc x) = genδ-FinVec n k a b x

δℕ-FinVec : (n k : ℕ) → FinVec ℕ n
δℕ-FinVec n k = genδ-FinVec n k 1 0

-- WARNING : harder to prove things about
genδ-FinVec' : (n k : ℕ) → (a b : A) → FinVec A n
genδ-FinVec' n k a b x with discreteℕ (toℕ x) k
... | yes p = a
... | no ¬p = b

-- doing induction on toFin is awkward, so the following alternative
enum : (m : ℕ) → m < n → Fin n
enum {n = ℕzero} _ m<0 = ⊥.rec (¬-<-zero m<0)
enum {n = ℕsuc n} 0 _ = zero
enum {n = ℕsuc n} (ℕsuc m) p = suc (enum m (pred-≤-pred p))

enum∘toℕ : (i : Fin n)(p : toℕ i < n) → enum (toℕ i) p ≡ i
enum∘toℕ {n = ℕsuc n} zero _ = refl
enum∘toℕ {n = ℕsuc n} (suc i) p t = suc (enum∘toℕ i (pred-≤-pred p) t)

toℕ∘enum : (m : ℕ)(p : m < n) → toℕ (enum m p) ≡ m
toℕ∘enum {n = ℕzero} _ m<0 = ⊥.rec (¬-<-zero m<0)
toℕ∘enum {n = ℕsuc n} 0 _ = refl
toℕ∘enum {n = ℕsuc n} (ℕsuc m) p i = ℕsuc (toℕ∘enum m (pred-≤-pred p) i)

enumExt : {m m' : ℕ}(p : m < n)(p' : m' < n) → m ≡ m' → enum m p ≡ enum m' p'
enumExt p p' q i = enum (q i) (isProp→PathP (λ i → isProp≤ {m = ℕsuc (q i)}) p p' i)

enumInj : (p : m < k) (q : n < k) → enum m p ≡ enum n q → m ≡ n
enumInj p q path = sym (toℕ∘enum _ p) ∙ cong toℕ path ∙ toℕ∘enum _ q

enumIndStep :
    (P : Fin n → Type ℓ)
  → (k : ℕ)(p : ℕsuc k < n)
  → ((m : ℕ)(q : m < n)(q' : m ≤ k )     → P (enum m q))
  → P (enum (ℕsuc k) p)
  → ((m : ℕ)(q : m < n)(q' : m ≤ ℕsuc k) → P (enum m q))
enumIndStep P k p f x m q q' =
  case (≤-split q') return (λ _ → P (enum m q)) of
    λ { (inl r') → f m q (pred-≤-pred r')
      ; (inr r') → subst P (enumExt p q (sym r')) x }

enumElim :
    (P : Fin n → Type ℓ)
  → (k : ℕ)(p : k < n)(h : ℕsuc k ≡ n)
  → ((m : ℕ)(q : m < n)(q' : m ≤ k) → P (enum m q))
  → (i : Fin n) → P i
enumElim P k p h f i =
  subst P (enum∘toℕ i (toℕ<n i)) (f (toℕ i) (toℕ<n i)
    (pred-≤-pred (subst (λ a → toℕ i < a) (sym h) (toℕ<n i))))


++FinAssoc : {n m k : ℕ} (U : FinVec A n) (V : FinVec A m) (W : FinVec A k)
           → PathP (λ i → FinVec A (+-assoc n m k i)) (U ++Fin (V ++Fin W)) ((U ++Fin V) ++Fin W)
++FinAssoc {n = ℕzero} _ _ _ = refl
++FinAssoc {n = ℕsuc n} U V W i zero = U zero
++FinAssoc {n = ℕsuc n} U V W i (suc ind) = ++FinAssoc (U ∘ suc) V W i ind

++FinRid : {n : ℕ} (U : FinVec A n) (V : FinVec A 0)
         → PathP (λ i → FinVec A (+-zero n i)) (U ++Fin V) U
++FinRid {n = ℕzero} U V = funExt λ i → ⊥.rec (¬Fin0 i)
++FinRid {n = ℕsuc n} U V i zero = U zero
++FinRid {n = ℕsuc n} U V i (suc ind) = ++FinRid (U ∘ suc) V i ind

++FinElim : {P : A → Type ℓ'} {n m : ℕ} (U : FinVec A n) (V : FinVec A m)
          → (∀ i → P (U i)) → (∀ i → P (V i)) → ∀ i → P ((U ++Fin V) i)
++FinElim {n = ℕzero} _ _ _ PVHyp i = PVHyp i
++FinElim {n = ℕsuc n} _ _ PUHyp _ zero = PUHyp zero
++FinElim {P = P} {n = ℕsuc n} U V PUHyp PVHyp (suc i) =
          ++FinElim {P = P} (U ∘ suc) V (λ i → PUHyp (suc i)) PVHyp i

++FinPres∈ : {n m : ℕ} {α : FinVec A n} {β : FinVec A m} (S : ℙ A)
           → (∀ i → α i ∈ S) → (∀ i → β i ∈ S) → ∀ i → (α ++Fin β) i ∈ S
++FinPres∈ {n = ℕzero} S hα hβ i = hβ i
++FinPres∈ {n = ℕsuc n} S hα hβ zero = hα zero
++FinPres∈ {n = ℕsuc n} S hα hβ (suc i) = ++FinPres∈ S (hα ∘ suc) hβ i

-- sends i to n+i if toℕ i < m and to i∸n otherwise
-- then +Shuffle²≡id and over the induced path (i.e. in PathP (ua +ShuffleEquiv))
-- ++Fin is commutative, but how to go from there?
+Shuffle : (m n : ℕ) → Fin (m + n) → Fin (n + m)
+Shuffle m n i with <Dec (toℕ i) m
... | yes i<m = toFin (n + (toℕ i)) (<-k+ i<m)
... | no ¬i<m = toFin (toℕ i ∸ m)
                  (subst (λ x → toℕ i ∸ m < x) (+-comm m n) (≤<-trans (∸-≤ (toℕ i) m) (toℕ<n i)))


finSucMaybeIso : Iso (Fin (ℕ.suc n)) (Maybe (Fin n))
Iso.fun finSucMaybeIso zero = nothing
Iso.fun finSucMaybeIso (suc i) = just i
Iso.inv finSucMaybeIso nothing = zero
Iso.inv finSucMaybeIso (just i) = suc i
Iso.rightInv finSucMaybeIso nothing = refl
Iso.rightInv finSucMaybeIso (just i) = refl
Iso.leftInv finSucMaybeIso zero = refl
Iso.leftInv finSucMaybeIso (suc i) = refl

finSuc≡Maybe : Fin (ℕ.suc n) ≡ Maybe (Fin n)
finSuc≡Maybe = isoToPath finSucMaybeIso

finSuc≡Maybe∙ : (Fin (ℕ.suc n) , zero) ≡ Maybe∙ (Fin n)
finSuc≡Maybe∙ = pointed-sip _ _ ((isoToEquiv finSucMaybeIso) , refl)

-- Proof that Fin n ⊎ Fin m ≃ Fin (n+m)
module FinSumChar where

 fun : (n m : ℕ) → Fin n ⊎ Fin m → Fin (n + m)
 fun ℕzero m (inr i) = i
 fun (ℕsuc n) m (inl zero) = zero
 fun (ℕsuc n) m (inl (suc i)) = suc (fun n m (inl i))
 fun (ℕsuc n) m (inr i) = suc (fun n m (inr i))

 invSucAux : (n m : ℕ) → Fin n ⊎ Fin m → Fin (ℕsuc n) ⊎ Fin m
 invSucAux n m (inl i) = inl (suc i)
 invSucAux n m (inr i) = inr i

 inv : (n m : ℕ) → Fin (n + m) → Fin n ⊎ Fin m
 inv ℕzero m i = inr i
 inv (ℕsuc n) m zero = inl zero
 inv (ℕsuc n) m (suc i) = invSucAux n m (inv n m i)

 ret : (n m : ℕ) (i : Fin n ⊎ Fin m) → inv n m (fun n m i) ≡ i
 ret ℕzero m (inr i) = refl
 ret (ℕsuc n) m (inl zero) = refl
 ret (ℕsuc n) m (inl (suc i)) = subst (λ x → invSucAux n m x ≡ inl (suc i))
                                       (sym (ret n m (inl i))) refl
 ret (ℕsuc n) m (inr i) = subst (λ x → invSucAux n m x ≡ inr i) (sym (ret n m (inr i))) refl

 sec : (n m : ℕ) (i : Fin (n + m)) → fun n m (inv n m i) ≡ i
 sec ℕzero m i = refl
 sec (ℕsuc n) m zero = refl
 sec (ℕsuc n) m (suc i) = helperPath (inv n m i) ∙ cong suc (sec n m i)
  where
  helperPath : ∀ x → fun (ℕsuc n) m (invSucAux n m x) ≡ suc (fun n m x)
  helperPath (inl _) = refl
  helperPath (inr _) = refl

 Equiv : (n m : ℕ) → Fin n ⊎ Fin m ≃ Fin (n + m)
 Equiv n m = isoToEquiv (iso (fun n m) (inv n m) (sec n m) (ret n m))

 ++FinInl : (n m : ℕ) (U : FinVec A n) (W : FinVec A m) (i : Fin n)
          → U i ≡ (U ++Fin W) (fun n m (inl i))
 ++FinInl (ℕsuc n) m U W zero = refl
 ++FinInl (ℕsuc n) m U W (suc i) = ++FinInl n m (U ∘ suc) W i

 ++FinInr : (n m : ℕ) (U : FinVec A n) (W : FinVec A m) (i : Fin m)
          → W i ≡ (U ++Fin W) (fun n m (inr i))
 ++FinInr ℕzero (ℕsuc m) U W i = refl
 ++FinInr (ℕsuc n) m U W i = ++FinInr n m (U ∘ suc) W i

-- Proof that Fin n × Fin m ≃ Fin nm
module FinProdChar where

 open Iso
 sucProdToSumIso : (n m : ℕ) → Iso (Fin (ℕsuc n) × Fin m) (Fin m ⊎ (Fin n × Fin m))
 fun (sucProdToSumIso n m) (zero , j) = inl j
 fun (sucProdToSumIso n m) (suc i , j) = inr (i , j)
 inv (sucProdToSumIso n m) (inl j) = zero , j
 inv (sucProdToSumIso n m) (inr (i , j)) = suc i , j
 rightInv (sucProdToSumIso n m) (inl j) = refl
 rightInv (sucProdToSumIso n m) (inr (i , j)) = refl
 leftInv (sucProdToSumIso n m) (zero , j) = refl
 leftInv (sucProdToSumIso n m) (suc i , j) = refl

 Equiv : (n m : ℕ) → (Fin n × Fin m) ≃ Fin (n · m)
 Equiv ℕzero m = uninhabEquiv (λ x → ¬Fin0 (fst x)) ¬Fin0
 Equiv (ℕsuc n) m = Fin (ℕsuc n) × Fin m    ≃⟨ isoToEquiv (sucProdToSumIso n m) ⟩
                    Fin m ⊎ (Fin n × Fin m) ≃⟨ isoToEquiv (⊎Iso idIso (equivToIso (Equiv n m))) ⟩
                    Fin m ⊎ Fin (n · m)     ≃⟨ FinSumChar.Equiv m (n · m) ⟩
                    Fin (m + n · m)         ■

-- Exhaustion of decidable predicate

∀Dec :
    (P : Fin m → Type ℓ)
  → (dec : (i : Fin m) → Dec (P i))
  → ((i : Fin m) → P i) ⊎ (Σ[ i ∈ Fin m ] ¬ P i)
∀Dec {m = 0} _ _ = inl λ ()
∀Dec {m = ℕsuc m} P dec = helper (dec zero) (∀Dec _ (dec ∘ suc))
  where
    helper :
        Dec (P zero)
      → ((i : Fin m) → P (suc i))  ⊎ (Σ[ i ∈ Fin m ] ¬ P (suc i))
      → ((i : Fin (ℕsuc m)) → P i) ⊎ (Σ[ i ∈ Fin (ℕsuc m) ] ¬ P i)
    helper (yes p) (inl q) = inl λ { zero → p ; (suc i) → q i }
    helper (yes _) (inr q) = inr (suc (q .fst) , q .snd)
    helper (no ¬p) _ = inr (zero , ¬p)

∀Dec2 :
    (P : Fin m → Fin n → Type ℓ)
  → (dec : (i : Fin m)(j : Fin n) → Dec (P i j))
  → ((i : Fin m)(j : Fin n) → P i j) ⊎ (Σ[ i ∈ Fin m ] Σ[ j ∈ Fin n ] ¬ P i j)
∀Dec2 {m = 0} {n = n} _ _ = inl λ ()
∀Dec2 {m = ℕsuc m} {n = n} P dec = helper (∀Dec (P zero) (dec zero)) (∀Dec2 (P ∘ suc) (dec ∘ suc))
  where
    helper :
        ((j : Fin n) → P zero j) ⊎ (Σ[ j ∈ Fin n ] ¬ P zero j)
      → ((i : Fin m)(j : Fin n) → P (suc i) j)  ⊎ (Σ[ i ∈ Fin m ] Σ[ j ∈ Fin n ] ¬ P (suc i) j)
      → ((i : Fin (ℕsuc m))(j : Fin n) → P i j) ⊎ (Σ[ i ∈ Fin (ℕsuc m) ] Σ[ j ∈ Fin n ] ¬ P i j)
    helper (inl p) (inl q) = inl λ { zero j → p j ; (suc i) j → q i j }
    helper (inl _) (inr q) = inr (suc (q .fst) , q .snd .fst , q .snd .snd)
    helper (inr p) _ = inr (zero , p)

suc-predFin : (k : Fin (ℕsuc (ℕsuc n))) → ¬ k ≡ zero → k ≡ suc (predFin k)
suc-predFin zero x = ⊥.rec (x refl)
suc-predFin (suc k) x = refl

toℕ∘predFin≡predℕ∘toFin : toℕ ∘ predFin {n} ≡ predℕ ∘ toℕ
toℕ∘predFin≡predℕ∘toFin = funExt λ { zero → refl ; (suc k) → refl }

0<→ℕsuc∘toℕ∘predFin : (x : Fin (ℕsuc (ℕsuc n))) → ℕzero < toℕ x → ℕsuc (toℕ (predFin x)) ≡ toℕ x
0<→ℕsuc∘toℕ∘predFin zero = ⊥.rec ∘ ¬-<-zero
0<→ℕsuc∘toℕ∘predFin (suc _) _ = refl


-- sucPerm : Fin n ≃ Fin m → Fin (ℕsuc n) ≃ Fin (ℕsuc m)
-- sucPerm {n} {m} e =
--      invEquiv (FinSumChar.Equiv 1 n)
--   ∙ₑ ⊎-equiv (idEquiv _) e
--   ∙ₑ FinSumChar.Equiv 1 m

sucPermIso : Iso (Fin n) (Fin m) → Iso (Fin (ℕsuc n)) (Fin (ℕsuc m))
sucPermIso {n} {m} e = w
  where
    open Iso e

    w : Iso (Fin (ℕsuc n)) (Fin (ℕsuc m))
    Iso.fun w zero = zero
    Iso.fun w (suc x) = suc (fun x)
    Iso.inv w zero = zero
    Iso.inv w (suc x) = suc (inv x)
    Iso.rightInv w zero = refl
    Iso.rightInv w (suc b) = cong suc (rightInv b)
    Iso.leftInv w zero = refl
    Iso.leftInv w (suc a) = cong suc (leftInv a)

+k : ∀ {n k} → Fin n → Fin (k + n)
+k {k = ℕzero} x = x
+k {k = ℕsuc k} x = suc (+k x)


k+ : ∀ {n k} → Fin n → Fin (n + k)
k+ {.(ℕsuc _)} zero = zero
k+ {.(ℕsuc n)} {k} (suc {n} x) = suc (k+ {n} x)


sucPerm : Fin n ≃ Fin m → Fin (ℕsuc n) ≃ Fin (ℕsuc m)
sucPerm {n} {m} e = isoToEquiv (sucPermIso (equivToIso e))

+Perm : ∀ k → Fin n ≃ Fin m → Fin (k + n) ≃ Fin (k + m)
+Perm ℕzero = idfun _
+Perm (ℕsuc k) = sucPerm ∘ +Perm k

infixr 4  _=→_

=■ : ∀ {ℓ} {A : Type ℓ} {f g : Fin ℕzero → A} → f ≡ g
=■ i ()

cons→ : A → (Fin n → A) → Fin (ℕsuc n) →  A
cons→ x x₁ zero = x
cons→ x x₁ (suc x₂) = x₁ x₂


_=→_ : ∀ {ℓ} {A : Type ℓ} {f g : Fin (ℕsuc n) → A}
            → f zero ≡ g zero
            → (f ∘ suc ≡ g ∘ suc )
            → f ≡ g
_=→_ x x₁ i zero = x i
_=→_ x x₁ i (suc x₂) = x₁ i x₂




infixr 4  _sq→_

_sq→_ : ∀ {ℓ} {A : Type ℓ} {f g f' g'  : Fin (ℕsuc n) → A}
            -- → {fg0 : f zero ≡ g zero}
            --   {f'g'0 : f' zero ≡ g' zero}
            --   {ff'0 : f zero ≡ f' zero}
            --   {gg'0 : g zero ≡ g' zero}
            → {fg : f ≡ g}
              {f'g' : f' ≡ g'}
              {ff' : f ≡ f'}
              {gg' : g ≡ g'}
            → Square (funExt⁻ fg zero)
                     (funExt⁻ f'g' zero)
                     (funExt⁻ ff' zero)
                     (funExt⁻ gg' zero)  
            → Square (cong (_∘ suc) fg)
                     (cong (_∘ suc) f'g')
                     (cong (_∘ suc) ff')
                     (cong (_∘ suc) gg') 
            → Square (fg)
                     (f'g')
                     (ff')
                     (gg')
(x sq→ x₁) i i₁ zero = x i i₁
(x sq→ x₁) i i₁ (suc x₂) = x₁ i i₁ x₂

=→∙ : ∀ {ℓ} {A : Type ℓ} {f g h : Fin (ℕsuc n) → A}
            → (p0 : f zero ≡ g zero ) (q0 : g zero ≡ h zero)
            → (p : f ∘ suc ≡ g ∘ suc) (q : g ∘ suc ≡ h ∘ suc)
            → Path (f ≡ h)
               ((_=→_ {g = g} p0 p) ∙ (q0 =→ q)) (p0 ∙ q0 =→ p ∙ q )
=→∙ p0 q0 p q = refl sq→ refl


sucPermId : sucPerm (idEquiv (Fin n)) ≡ idEquiv _
sucPermId = equivEq ( refl =→ refl)

isInjectiveSucPerm : (e f : Fin n ≃ Fin m) → sucPerm e ≡ sucPerm f → e ≡ f
isInjectiveSucPerm {ℕzero} {ℕzero} _ _ _ = equivEq (funExt (⊥.rec ∘ ¬Fin0))
isInjectiveSucPerm {ℕzero} {ℕsuc m} e _ _ = ⊥.rec (¬Fin0 (invEq e zero))
isInjectiveSucPerm {ℕsuc _} {ℕzero} e _ _ = ⊥.rec (¬Fin0 (equivFun e zero))
isInjectiveSucPerm {ℕsuc _} {ℕsuc _} _ _ p =
  equivEq (funExt (cong predFin ∘ funExt⁻ (cong fst p) ∘ suc))

respectsCompSucPerm : (e : Fin n ≃ Fin m) (f : Fin m ≃ Fin k)
        → sucPerm e ∙ₑ sucPerm f ≡ sucPerm (e ∙ₑ f)
respectsCompSucPerm e f = equivEq λ { i zero → zero ; i (suc k) → suc (f .fst (e .fst k)) }

respectsComp+Perm : ∀ l → (e : Fin n ≃ Fin m) (f : Fin m ≃ Fin k)
        → +Perm l e ∙ₑ +Perm l f ≡ +Perm l (e ∙ₑ f)
respectsComp+Perm ℕzero e f = refl
respectsComp+Perm (ℕsuc l) e f =
  respectsCompSucPerm _ _ ∙
  cong sucPerm (respectsComp+Perm l e f) 



swap0and1 : Fin (ℕsuc (ℕsuc n)) → Fin (ℕsuc (ℕsuc n))
swap0and1 zero = one
swap0and1 one = zero
swap0and1 (suc (suc x)) = suc (suc x)

swap0and2 : Fin (ℕsuc (ℕsuc (ℕsuc n))) → Fin (ℕsuc (ℕsuc (ℕsuc n)))
swap0and2 zero = two
swap0and2 one = one
swap0and2 two = zero
swap0and2 (suc (suc (suc x))) = suc (suc (suc x))

swap0and2≃ : Fin (ℕsuc (ℕsuc (ℕsuc n))) ≃ Fin (ℕsuc (ℕsuc (ℕsuc n)))
swap0and2≃ = swap0and2 , involIsEquiv (funExt⁻ (refl =→ refl =→ refl =→ refl))

swap0and1Iso : Iso (Fin (ℕsuc (ℕsuc n))) (Fin (ℕsuc (ℕsuc n)))
swap0and1Iso = w
  where
    f∘f : _
    f∘f zero = refl
    f∘f one = refl
    f∘f (suc (suc b)) = refl

    w : Iso _ _
    Iso.fun w = swap0and1
    Iso.inv w = swap0and1
    Iso.rightInv w = f∘f
    Iso.leftInv w = f∘f

ℕswap0and1 : ℕ → ℕ
ℕswap0and1 ℕzero = one
ℕswap0and1 one = ℕzero
ℕswap0and1 (ℕsuc (ℕsuc x)) = (ℕsuc (ℕsuc x))


-- =f : ∀ {ℓ} {A : Type ℓ} {f g : ∀ n → Fin (ℕsuc (ℕsuc n)) → A}
--      → f ℕzero zero ≡ g ℕzero zero → (∀ n → f n ≡ f n → f (ℕsuc n) ≡ f (ℕsuc n))
--        → ∀ n → f n ≡ g n
-- =f = {!!}


ℕswap0and1≃ : ℕ ≃ ℕ
ℕswap0and1≃ =
  involEquiv {f = ℕswap0and1}
   λ {ℕzero  → refl ; one → refl ; (ℕsuc (ℕsuc _)) → refl }



swap0and1≃ : Fin (ℕsuc (ℕsuc n)) ≃ Fin (ℕsuc (ℕsuc n))
swap0and1≃ = swap0and1 , isoToIsEquiv (swap0and1Iso)

swap0and1≃²=idEquiv : swap0and1≃ ∙ₑ swap0and1≃ ≡ idEquiv (Fin (ℕsuc (ℕsuc n)))
swap0and1≃²=idEquiv = equivEq (refl =→ refl =→ refl)


swap0and1≃=invEquivSwap0and1 : swap0and1≃ {n} ≡ invEquiv swap0and1≃
swap0and1≃=invEquivSwap0and1 = equivEq (refl =→ refl =→ refl)

swap0and1Braid : (swap0and1≃ ∙ₑ sucPerm (swap0and1≃ {n = n}) ∙ₑ swap0and1≃ 
                  ∙ₑ sucPerm swap0and1≃ ∙ₑ swap0and1≃ ∙ₑ sucPerm swap0and1≃) ≡ idEquiv _
swap0and1Braid = 
   equivEq (refl =→ refl =→ refl =→ refl)

-- adjTransposition' : (k : Fin n) → Fin (ℕsuc n) ≃ Fin (ℕsuc n)
-- adjTransposition' {ℕsuc n} k = {!swap0and1≃ {n = ℕzero}!}

adjTransposition : Fin n → Fin (ℕsuc n) ≃ Fin (ℕsuc n)
adjTransposition zero = swap0and1≃
adjTransposition (suc k) = sucPerm (adjTransposition k)

adjTransposition* : Fin (predℕ n) → Fin n ≃ Fin n
adjTransposition* {n = ℕzero} _ = idEquiv _
adjTransposition* {n = ℕsuc n} k = adjTransposition k


adjTransposition²=idEquiv : ∀ k → adjTransposition k ∙ₑ adjTransposition k
                                     ≡ idEquiv (Fin (ℕsuc n))
adjTransposition²=idEquiv zero = swap0and1≃²=idEquiv
adjTransposition²=idEquiv {ℕsuc n} (suc k) = 
   respectsCompSucPerm _ _ ∙ cong sucPerm (adjTransposition²=idEquiv k)
     ∙   equivEq  (refl =→ refl)


adjTransposition*²=idEquiv : ∀ k → adjTransposition* k ∙ₑ adjTransposition* k
                                     ≡ idEquiv (Fin n)
adjTransposition*²=idEquiv {ℕsuc n} k = adjTransposition²=idEquiv k


adjTranspositionBraid : (adjTransposition (+k zero) ∙ₑ adjTransposition (+k one)
                      ∙ₑ adjTransposition (+k zero) ∙ₑ adjTransposition (+k one)
                      ∙ₑ adjTransposition (+k zero) ∙ₑ adjTransposition (+k one))
                       ≡ idEquiv (Fin (ℕsuc (k + ℕsuc (ℕsuc n))))
adjTranspositionBraid {ℕzero} = swap0and1Braid
adjTranspositionBraid {ℕsuc k} =
   equivEq 
     λ { i zero → zero
       ; i (suc l) → suc (fst (adjTranspositionBraid {k = k} i) l) }



-- sucPermFDMorphism : ∀ n → GroupHom (SymData n) (SymData (suc n))
-- fst (sucPermFDMorphism n) = sucPerm
-- IsGroupHom.pres· (snd (sucPermFDMorphism n)) x y =
--   equivEq λ { i zero → zero ; i (suc k) → suc (y .fst (x .fst k)) }
-- IsGroupHom.pres1 (snd (sucPermFDMorphism n)) =
--   equivEq λ { i zero → zero ; i (suc k) → suc k }
-- IsGroupHom.presinv (snd (sucPermFDMorphism n)) x =
--   equivEq λ { i zero → zero ; i (suc k) → suc (snd x .equiv-proof k .fst .fst) }



commSwap0and1SucSuc : (e : Fin n ≃ Fin n) →
                        swap0and1≃ ∙ₑ sucPerm (sucPerm e)
                      ≡ sucPerm (sucPerm e) ∙ₑ swap0and1≃  
commSwap0and1SucSuc e =
  equivEq (refl =→ refl =→ refl)


commTranspositions : (k : Fin n) → adjTransposition zero ∙ₑ adjTransposition (suc (suc k))
                      ≡ adjTransposition (suc (suc k)) ∙ₑ adjTransposition zero  
commTranspositions k = commSwap0and1SucSuc _

commTranspositions' : (k : Fin n) → adjTransposition (+k zero) ∙ₑ adjTransposition (+k (suc (suc k)))
                      ∙ₑ adjTransposition (+k zero) ∙ₑ adjTransposition (+k (suc (suc k)))
                      ≡ idEquiv (Fin (ℕsuc (m + ℕsuc (ℕsuc n))))
commTranspositions' {m = ℕzero} k = 
  cong (((adjTransposition zero) ∙ₑ_) ∘ ((adjTransposition (suc (suc k))) ∙ₑ_))
    (commTranspositions k) ∙
      (cong (swap0and1≃ ∙ₑ_) (compEquiv-assoc _ _ _ ∙
        cong (_∙ₑ swap0and1≃)
          ((adjTransposition²=idEquiv (suc (suc k)))) ∙ compEquivIdEquiv _))
       ∙ swap0and1≃²=idEquiv
commTranspositions' {m = ℕsuc m} k =
  equivEq
     λ { i zero → zero
       ; i (suc l) → suc (fst (commTranspositions' {m = m} k i) l) }
 

-- x = 0       ⇒  k
-- 0 < x =< k  ⇒  x - 1
-- k < x       ⇒  x
rot≃ : Fin n →  Fin n ≃ Fin n
rot≃ zero = idEquiv _
rot≃ (suc {ℕsuc n} x) = swap0and1≃ ∙ₑ sucPerm (rot≃ x)

_ρ_ : ∀ {n} → Fin n → Fin n → Fin n
_ρ_ e0 e1 = (invEq (rot≃ e0) e1)

rot≃-zero : (k : Fin (ℕsuc n)) → equivFun (rot≃ k) zero ≡ k
rot≃-zero zero = refl
rot≃-zero {ℕsuc n} (suc k) = cong suc (rot≃-zero k)

rot≃-k  : (k : Fin (ℕsuc n)) → invEq (rot≃ k) k ≡ zero
rot≃-k k = sym (invEq (equivAdjointEquiv (rot≃ k)) (rot≃-zero k))

rot≃-k<  : (k l : Fin (ℕsuc n)) → toℕ k < toℕ l → invEq (rot≃ k) l ≡ l
rot≃-k< zero l x = refl
rot≃-k< (suc k) zero = ⊥.rec ∘ ¬-<-zero
rot≃-k< {ℕsuc n} (suc k) one = ⊥.rec ∘ ¬-<-zero ∘ predℕ-≤-predℕ
rot≃-k< {ℕsuc (ℕsuc n)} (suc k) (suc (suc l)) x = 
  cong swap0and1 (cong suc (rot≃-k< {(ℕsuc n)} (k) (suc l) (predℕ-≤-predℕ x)))

suc< : ∀ n → (k l : Fin n) → toℕ l < toℕ k → Fin n
suc< .(ℕsuc _) zero l = ⊥.rec ∘ ¬-<-zero
suc< .(ℕsuc (ℕsuc n)) (suc {ℕsuc n} k) zero x = one
suc< .(ℕsuc (ℕsuc n)) (suc {ℕsuc n} k) (suc l) x = suc (suc< _ k l (predℕ-≤-predℕ x)) 

rot≃-<k  : (k l : Fin (ℕsuc n)) → (p : toℕ l < toℕ k)
                             →  weakenFin (invEq (rot≃ k) l) ≡ (suc l)
rot≃-<k zero l = ⊥.rec ∘ ¬-<-zero
rot≃-<k {ℕsuc n} (suc k) zero p = refl
rot≃-<k one (suc l) = ⊥.rec ∘ ¬-<-zero ∘ predℕ-≤-predℕ
rot≃-<k (suc (suc {ℕsuc n} k)) one p = refl
rot≃-<k (suc (suc {ℕsuc n} k)) (suc (suc l)) x = 
  let z = rot≃-<k (suc k) (suc l) (predℕ-≤-predℕ x)
  in  funExt⁻ {f = weakenFin ∘ swap0and1 ∘ suc  } {g = swap0and1 ∘ suc ∘ weakenFin}
         (refl =→ refl) (swap0and1 (suc (invEq (rot≃ k) l)) )
         ∙ cong swap0and1 (cong suc z)

toℕ∘predFin≡predℕ∘toℕ : toℕ ∘ predFin {n} ≡ predℕ ∘ toℕ
toℕ∘predFin≡predℕ∘toℕ = refl =→ refl

zzzqqq : toℕ ∘ predFin {n = n} ≡ toℕ ∘ predFin ∘ weakenFin
zzzqqq = toℕ∘predFin≡predℕ∘toℕ ∙ cong (predℕ ∘_) (sym (funExt (weakenRespToℕ)))
          ∙ sym (cong (_∘ weakenFin) toℕ∘predFin≡predℕ∘toℕ)

rot≃-<k'  : (k l : Fin (ℕsuc m)) → (p : toℕ (weakenFin l) < toℕ (suc k))
                             →  (predFin (invEq (swap0and1≃ ∙ₑ sucPerm (rot≃ k)) (weakenFin l)))
                                 ≡ l
rot≃-<k' k l p =
  let z = rot≃-<k (suc k) (weakenFin l) p 
  in inj-toℕ (funExt⁻ {f = toℕ ∘ predFin} {g = toℕ ∘ predFin ∘ weakenFin}
                zzzqqq
              (invEq (swap0and1≃ ∙ₑ sucPerm (rot≃ k)) (weakenFin l))
          ∙ cong (toℕ ∘ predFin) z ∙
           weakenRespToℕ _)
-- rot≃-≠k  : (k l : Fin (ℕsuc n)) → (p : ¬ toℕ l ≡ toℕ k)
--                              →  0 < toℕ (invEq (rot≃ k) l)
-- rot≃-≠k k l p with toℕ k ≟ toℕ l
-- ... | lt x = let z' = rot≃-k< k l x
--              in subst ((0 <_) ∘ toℕ) (sym z') (≤-trans (suc-≤-suc zero-≤) x)
-- ... | eq x = ⊥.rec (p (sym x))
-- ... | gt x = let z' = rot≃-<k k l x
--              in subst ((0 <_)) (sym z') (suc-≤-suc zero-≤)

¬Fin1≃Fin[suc[sucN]] : ¬ Fin 1 ≃ Fin (ℕsuc (ℕsuc n))
¬Fin1≃Fin[suc[sucN]] e =
  znots (invEq (congEquiv (invEquiv e))
    ((isContr→isProp isContrFin1)
       (invEq e zero) (invEq e (suc zero))))

predFin' : Fin n → Fin (ℕsuc n) → Fin n
predFin' x zero = x
predFin' _ (suc x₁) = x₁



unwindPermHead : (e : Fin (ℕsuc n) ≃ Fin (ℕsuc m))
                     → Σ (Fin n ≃ Fin m) λ e'
                       → e ≡ sucPerm e' ∙ₑ rot≃ (equivFun e zero)
unwindPermHead {ℕzero} {ℕzero} e =
  idEquiv _ , equivEq λ { i zero → (rot≃-zero (equivFun e zero)) (~ i)}
unwindPermHead {ℕzero} {ℕsuc _} = ⊥.rec ∘ ¬Fin1≃Fin[suc[sucN]]
unwindPermHead {ℕsuc _} {ℕzero} = ⊥.rec ∘ ¬Fin1≃Fin[suc[sucN]] ∘ invEquiv
unwindPermHead {ℕsuc _} {ℕsuc _} e = isoToEquiv w , equivEq (funExt ww)

  where
    e' = e ∙ₑ invEquiv (rot≃ (equivFun e zero))
    p = sym (rot≃-k (equivFun e zero))

    w : Iso _ _
    Iso.fun w = predFin ∘ fst e' ∘ suc
    Iso.inv w = predFin ∘ invEq e' ∘ suc
    Iso.rightInv w b =
       cong predFin (cong (equivFun e')
       (sym (suc-predFin (invEq e' (suc b))
        λ x → znots (p ∙ invEq≡→equivFun≡ e' x))) ∙ secEq e' (suc b))
    Iso.leftInv w a =
       cong (predFin ∘ invEq e')
        (sym (suc-predFin _ λ x → snotz (invEq (congEquiv e') (x ∙ p))))
       ∙ cong predFin (retEq e' (suc a))

    ww : _
    ww zero = sym (rot≃-zero (equivFun e zero))
    ww (suc x) = sym (secEq (rot≃ (equivFun e zero)) _)
         ∙ cong (equivFun (rot≃ (equivFun e zero)))
            (suc-predFin _ λ x₁ →
              znots
               (invEq (congEquiv (e ∙ₑ invEquiv (rot≃ (equivFun e zero))))
                (rot≃-k (equivFun e zero) ∙ (sym x₁))) )




-- unwindPermHead' : (e : Fin (ℕsuc n) ≃ Fin (ℕsuc m))
--                      → Σ (Fin n ≃ Fin m) λ e'
--                        → e ≡ sucPerm e' ∙ₑ rot≃ (equivFun e zero)
-- unwindPermHead' {n = n} {m = m} e = (f , {!!}) , {!!}

--  where
--     e' = e ∙ₑ invEquiv (rot≃ (equivFun e zero))

--     f : Fin n → Fin m
--     f x = predFin' (fst (fst (unwindPermHead e)) x) (fst e' (suc x))

--     f= : f ≡ {!(unwindPermHead e)!}
--     f= = {!!}

-- unwindPermHeadCompSwap0and1Suc'' : (e0 e1 : Fin (ℕsuc (ℕsuc m))) → ¬ e0 ≡ e1
--    →    toℕ (predFin (invEq (rot≃ (suc e1)) (suc e0)))
--       ≡ toℕ (suc (predFin (invEq (rot≃ e1) e0)))
-- unwindPermHeadCompSwap0and1Suc'' e0 e1 p with toℕ e0 ≟ toℕ e1
-- ... | lt x = let z = rot≃-<k (suc e1) (suc e0) (suc-≤-suc x )
--                  z' = rot≃-<k e1 e0 x
--              in funExt⁻ toℕ∘predFin≡predℕ∘toFin ((invEq (rot≃ (suc e1)) (suc e0)))
--                    ∙ cong predℕ (z ∙ sym (cong ℕsuc z')) ∙
--                      sym ( 0<→ℕsuc∘toℕ∘predFin _ (rot≃-≠k _ _ (p ∘ inj-toℕ)))
-- ... | eq x = ⊥.rec (p (inj-toℕ x))
-- ... | gt x = let z = rot≃-k< (suc e1) (suc e0) (suc-≤-suc x )
--                  z' = rot≃-k< e1 e0 x
--              in  cong (toℕ ∘ predFin) (z ∙ cong suc (sym z')) ∙
--                   sym ( 0<→ℕsuc∘toℕ∘predFin _ ((rot≃-≠k _ _ (p ∘ inj-toℕ))))


-- unwindPermHeadCompSwap0and1Suc' : (e0 e1 : Fin (ℕsuc (ℕsuc m))) → ¬ e0 ≡ e1 
--            →  sucPerm (rot≃ (predFin (invEq (rot≃ (suc e1)) (suc e0))))
--                 ≡ 
--               sucPerm (swap0and1≃) ∙ₑ 
--               sucPerm (sucPerm (rot≃ (predFin (invEq (rot≃ e1) e0))))
-- unwindPermHeadCompSwap0and1Suc' e0 e1 x =
--    cong sucPerm (
--            rot≃ (predFin (invEq (rot≃ (suc e1)) (suc e0)))
--          ≡⟨ cong rot≃ (inj-toℕ (unwindPermHeadCompSwap0and1Suc'' e0 e1 x)) ⟩
--          (rot≃ (suc (predFin (invEq (rot≃ e1) e0)))) ∎) 
--     ∙ sym (respectsCompSucPerm _ _)

-- unwindPermHeadCompSwap0and1Suc : (e0 e1 : Fin (ℕsuc (ℕsuc m))) → ¬ e0 ≡ e1 
--            →  sucPerm (rot≃ (predFin (invEq (rot≃ (suc e1)) (suc e0))))
--             ∙ₑ rot≃ (suc e1) ≡
--               sucPerm (swap0and1≃) ∙ₑ swap0and1≃ ∙ₑ
--                 sucPerm (sucPerm (rot≃ (predFin (invEq (rot≃ e1) e0)))
--             ∙ₑ rot≃ e1)
-- unwindPermHeadCompSwap0and1Suc e0 e1 x = 
--        _
--     ≡⟨ equivEq (cong (λ x → fst (x ∙ₑ rot≃ (suc e1)) )
--          (unwindPermHeadCompSwap0and1Suc' e0 e1 x)) ⟩
--               sucPerm (swap0and1≃) ∙ₑ 
--               sucPerm (sucPerm (rot≃ (predFin (invEq (rot≃ e1) e0))))
--             ∙ₑ (rot≃ (suc e1))
--     ≡⟨ equivEq (cong
--              (λ x → fst (sucPerm (swap0and1≃) ∙ₑ x ∙ₑ sucPerm (rot≃ e1)))
--              ( sym (commSwap0and1SucSuc (rot≃ (predFin (invEq (rot≃ e1) e0)))) )) ⟩
--        sucPerm (swap0and1≃) ∙ₑ swap0and1≃ ∙ₑ
--                 sucPerm (sucPerm (rot≃ (predFin (invEq (rot≃ e1) e0))))
--             ∙ₑ sucPerm (rot≃ e1)
--     ≡⟨ cong (λ x → sucPerm (swap0and1≃) ∙ₑ swap0and1≃ ∙ₑ x) (respectsCompSucPerm _ _) ⟩
--       sucPerm (swap0and1≃) ∙ₑ swap0and1≃ ∙ₑ
--                 sucPerm (sucPerm (rot≃ (predFin (invEq (rot≃ e1) e0)))
--             ∙ₑ rot≃ e1) ∎ 




-- unwindPermHeadCompSwap0and1' : 
--   (e0 e1 : Fin (ℕsuc (ℕsuc m))) → ¬ e0 ≡ e1 
--   →  swap0and1≃ ∙ₑ
--      sucPerm (rot≃ (predFin (invEq (rot≃ e0) e1)))
--            ∙ₑ rot≃ e0
--       ≡  sucPerm (rot≃ (predFin (invEq (rot≃ e1) e0)))
--             ∙ₑ rot≃ e1
-- unwindPermHeadCompSwap0and1' zero zero p = ⊥.rec (p refl)
-- unwindPermHeadCompSwap0and1' zero (suc e1) x =
--   equivEq (funExt λ {zero → refl ; (suc k) → refl })
-- unwindPermHeadCompSwap0and1' (suc e0) zero x =
--   equivEq (funExt λ {zero → refl ; one → refl ; (suc (suc k)) → refl })
-- unwindPermHeadCompSwap0and1' {ℕzero} (suc e0) (suc e1) p =
--   ⊥.rec (p (cong suc (isContr→isProp isContrFin1 _ _)))
-- unwindPermHeadCompSwap0and1' {ℕsuc m} (suc e0) (suc e1) p = 
--   let z = unwindPermHeadCompSwap0and1' e0 e1 (p ∘ cong suc)
--   in cong (swap0and1≃ ∙ₑ_) (unwindPermHeadCompSwap0and1Suc e1 e0 (p ∘ cong suc ∘ sym))
--      ∙ (equivEq (funExt
--           (λ {zero → refl ; one → refl ; two → refl ; (suc (suc (suc k))) → refl }))
--      ∙ cong (λ x → sucPerm swap0and1≃ ∙ₑ swap0and1≃ ∙ₑ x)
--         (respectsCompSucPerm _ _ ∙ cong sucPerm z))
--      ∙ sym (unwindPermHeadCompSwap0and1Suc e0 e1 (p ∘ cong suc))

-- e0>e1

helperFin< : (e0 e1 : Fin (ℕsuc m)) → toℕ e1 < toℕ e0
               → Σ ((Σ _ λ e0' → suc e0' ≡ e0) × (Σ _ λ e1' → weakenFin e1' ≡ e1))
                  λ ((e0' , _) , (e1' , _)) → toℕ e1' < toℕ (suc e0')
helperFin< zero _ = ⊥.rec ∘ ¬-<-zero 
helperFin< {ℕsuc m} (suc e0) zero p = ((e0 , refl) , (zero , refl)) , p
helperFin< {ℕsuc m} (suc e0) (suc e1) = 
  (λ {s} (x , y) → map-× (λ x → _ , cong suc (snd x)) ((λ x → _ , cong suc (snd x))) x
     , (_ ≡≤⟨ cong (ℕsuc ∘ ℕsuc) (sym (weakenRespToℕ _) ∙ cong toℕ (snd (snd x))) ⟩
        _ ≤≡⟨ s ⟩ sym (cong (ℕsuc ∘ toℕ) (snd (fst x))))
      )
   ∘ helperFin< e0 e1 ∘ pred-≤-pred
  where open <-Reasoning

diferentFinElim : {A : (e0 e1 : Fin (ℕsuc m)) → Type ℓ}
         → (∀ e0 e1 → toℕ e1 < toℕ (suc e0) → A (suc e0) (weakenFin e1))
         → (∀ e0 e1 → toℕ e0 < toℕ (suc e1) → A (weakenFin e0) (suc e1))
         → ∀ e0 e1 → ¬ e0 ≡ e1 → A e0 e1
diferentFinElim {A = A} x< x> e0 e1 =
     (⊎.elim
        (λ (((e1' , p1) , (e0' , p0)) , p) → subst2 A p0 p1 (x> e0' e1' p))
        (λ (((e0' , p0) , (e1' , p1)) , p) → subst2 A p0 p1 (x< e0' e1' p)))
   ∘ map-⊎ (helperFin< e1 e0) (helperFin< e0 e1)
   ∘ ¬≡ℕ-cases (toℕ e0) (toℕ e1)
   ∘ (_∘ inj-toℕ) 


unwindPermHeadCompSwap0and1'Case> : 
  (e0 : Fin (ℕsuc m)) → (e1 : Fin (ℕsuc m)) → toℕ e1 < toℕ (suc e0) 
  →  fst (swap0and1≃ ∙ₑ
     sucPerm (rot≃ e1) ∙ₑ rot≃ (suc e0))
      ≡  fst (sucPerm (rot≃ e0) ∙ₑ rot≃ (weakenFin e1))
unwindPermHeadCompSwap0and1'Case> e0 zero x = refl =→ refl =→ refl
unwindPermHeadCompSwap0and1'Case> {ℕsuc m} zero (suc e1) x = ⊥.rec (¬-<-zero (pred-≤-pred x))
unwindPermHeadCompSwap0and1'Case> {ℕsuc m} (suc e0) (suc e1) x =
  let w = unwindPermHeadCompSwap0and1'Case> e0 e1 (pred-≤-pred x)
      z = cong {B = λ _ → Fin (ℕsuc (ℕsuc (ℕsuc m)))} (suc {n = ℕsuc (ℕsuc m)}) ∘ funExt⁻ w
  in (z zero) =→ z one =→ refl =→ funExt (z ∘ suc ∘ suc)

-- unwindPermHeadCompSwap0and1'Case>* : 
--   (e0 : Fin (ℕsuc m)) → (e1 : Fin (ℕsuc m)) → toℕ e1 < toℕ (suc e0) 
--   →  
--       fst (swap0and1≃ ∙ₑ
--       sucPerm (rot≃ (predFin (invEq (rot≃ (suc e0)) (weakenFin e1)))) ∙ₑ
--       rot≃ (suc e0))
--       ≡
--       fst (sucPerm (rot≃ (predFin (invEq (rot≃ (weakenFin e1)) (suc e0)))) ∙ₑ
--       rot≃ (weakenFin e1))
-- unwindPermHeadCompSwap0and1'Case>* {m = m} e0 e1 p =
--   let z : invEq (rot≃ (weakenFin e1)) (suc e0) ≡ suc e0
--       z = rot≃-k< {n = ℕsuc m} (weakenFin e1) (suc e0) (subst (_< _) (sym (weakenRespToℕ _)) p)
--       v : (predFin (invEq (swap0and1≃ ∙ₑ sucPerm (rot≃ e0)) (weakenFin e1))) ≡ e1
--       v = rot≃-<k' e0 e1 (subst (_< _) (sym (weakenRespToℕ _)) p)  
--   in  cong (λ e1 → fst
--       (swap0and1≃ ∙ₑ
--        sucPerm (rot≃ e1) ∙ₑ swap0and1≃ ∙ₑ sucPerm (rot≃ e0)))
--         v
--     ∙ unwindPermHeadCompSwap0and1'Case> e0 e1 p ∙
--      cong (λ x → fst (sucPerm (rot≃ (predFin x)) ∙ₑ
--       rot≃ (weakenFin e1))) (sym z) 

rotRotCase : (e0 e1 : Fin (ℕsuc (ℕsuc m))) → Type
rotRotCase e0 e1 =
  (Σ ((Σ _ λ e0' → suc e0' ≡ e0) × (Σ _ λ e1' → weakenFin e1' ≡ e1))
                  λ ((e0' , _) , (e1' , _)) →
                   (toℕ e1' < toℕ (suc e0'))
                    × ((predFin (invEq (swap0and1≃ ∙ₑ sucPerm (rot≃ e0')) (weakenFin e1'))) ≡ e1') × 
                        (invEq (rot≃ (weakenFin e1')) (suc e0') ≡ suc e0'))

<→rotRotCase : (e0 e1 : Fin (ℕsuc (ℕsuc m))) → toℕ e1 < toℕ e0 → rotRotCase e0 e1
<→rotRotCase e0 e1 x =
  let (z@((e0' , p0) , (e1' , p1)) , p) = helperFin< _ _ x
  in z , p , (rot≃-<k' e0' e1' ((subst (_< (ℕsuc (toℕ e0'))) (sym (weakenRespToℕ _)) p))) ,
    rot≃-k< (weakenFin e1') (suc e0') (subst (_< (ℕsuc (toℕ e0'))) (sym (weakenRespToℕ _)) p)

rotRotCases : (e0 e1 : Fin (ℕsuc (ℕsuc m))) → ¬ e0 ≡ e1 →
               rotRotCase e1 e0 ⊎ rotRotCase e0 e1
rotRotCases e0 e1 =
      map-⊎ (<→rotRotCase _ _) (<→rotRotCase _ _)
   ∘ ¬≡ℕ-cases (toℕ e0) (toℕ e1)
   ∘ (_∘ inj-toℕ) 

rotRotElim : (A :  (e0 e1 : Fin (ℕsuc (ℕsuc m))) (e0' e1' : Fin (ℕsuc m)) → Type ℓ)
          → (∀ e0 e1 → toℕ e1 < toℕ (suc e0) → A (suc e0) (weakenFin e1) e0 e1)
          → (∀ e0 e1 → toℕ e0 < toℕ (suc e1) → A (weakenFin e0) (suc e1)  e0 e1)
          → (e0 e1 : Fin (ℕsuc (ℕsuc m))) → ¬ e0 ≡ e1
          → A e0 e1 (predFin (invEq (rot≃ e1) e0)) (predFin (invEq (rot≃ e0) e1))
rotRotElim A c< c> e0 e1 =
  ⊎.elim (λ (((e0' , p0) , (e1' , p1)) , p , q , r) →
          let pe0 : e0' ≡ (predFin (invEq (rot≃ e0) e1))
              pe0 = cong predFin (sym r) ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p1 p0
              pe1 : e1' ≡ (predFin (invEq (rot≃ e1) e0))
              pe1 = sym q ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p0 p1
          in
           transport (λ i → A (p1 i) (p0 i) (pe1 i) (pe0 i)) (c> e1' e0' p))
         (λ (((e0' , p0) , (e1' , p1)) , p , q , r) →
          let pe0 : e0' ≡ (predFin (invEq (rot≃ e1) e0))
              pe0 = cong predFin (sym r) ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p1 p0
              pe1 : e1' ≡ (predFin (invEq (rot≃ e0) e1))
              pe1 = sym q ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p0 p1
          in transport {B = A e0 e1 (predFin (invEq (rot≃ e1) e0)) (predFin (invEq (rot≃ e0) e1))}
              (λ i → A (p0 i) (p1 i) (pe0 i) (pe1 i)) (c< e0' e1' p))
   ∘ rotRotCases _ _

rotRotElimDep : {A :  (e0 e1 : Fin (ℕsuc (ℕsuc m))) (e0' e1' : Fin (ℕsuc m)) → Type ℓ}
          → {c< : ∀ e0 e1 → toℕ e1 < toℕ (suc e0) → A (suc e0) (weakenFin e1) e0 e1}
          → {c> : ∀ e0 e1 → toℕ e0 < toℕ (suc e1) → A (weakenFin e0) (suc e1)  e0 e1}
          → (B :  (e0 e1 : Fin (ℕsuc (ℕsuc m))) (e0' e1' : Fin (ℕsuc m))
                  → A e0 e1 e0' e1' → Type ℓ')
          → (∀ e0 e1 → (p : toℕ e1 < toℕ (suc e0)) → B (suc e0) (weakenFin e1) e0 e1 (c< e0 e1 p))
          → (∀ e0 e1 → (p : toℕ e0 < toℕ (suc e1)) → B (weakenFin e0) (suc e1)  e0 e1 (c> e0 e1 p))
          → (e0 e1 : Fin (ℕsuc (ℕsuc m))) → (p : ¬ e0 ≡ e1)
          → B e0 e1 (predFin (invEq (rot≃ e1) e0)) (predFin (invEq (rot≃ e0) e1))
             (rotRotElim A c< c> e0 e1 p)
rotRotElimDep {A = A} {c<} {c>} B d< d> e0 e1 p = 
  ⊎.elim {C = λ x₂ → B e0 e1 (predFin (invEq (rot≃ e1) e0)) (predFin (invEq (rot≃ e0) e1))
             ((  ⊎.elim (λ (((e0' , p0) , (e1' , p1)) , p , q , r) →
          let pe0 : e0' ≡ (predFin (invEq (rot≃ e0) e1))
              pe0 = cong predFin (sym r) ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p1 p0
              pe1 : e1' ≡ (predFin (invEq (rot≃ e1) e0))
              pe1 = sym q ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p0 p1
          in
           transport (λ i → A (p1 i) (p0 i) (pe1 i) (pe0 i)) (c> e1' e0' p))
         (λ (((e0' , p0) , (e1' , p1)) , p , q , r) →
          let pe0 : e0' ≡ (predFin (invEq (rot≃ e1) e0))
              pe0 = cong predFin (sym r) ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p1 p0
              pe1 : e1' ≡ (predFin (invEq (rot≃ e0) e1))
              pe1 = sym q ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p0 p1
          in transport {B = A e0 e1 (predFin (invEq (rot≃ e1) e0)) (predFin (invEq (rot≃ e0) e1))}
              (λ i → A (p0 i) (p1 i) (pe0 i) (pe1 i)) (c< e0' e1' p))) x₂)}
    ((λ (((e0' , p0) , (e1' , p1)) , p , q , r) →
       let  --pe0 : e0' ≡ (predFin (invEq (rot≃ e0) e1))
            pe0 = cong predFin (sym r) ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p1 p0
            pe1 : e1' ≡ (predFin (invEq (rot≃ e1) e0))
            pe1 = sym q ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p0 p1

            Ap = toPathP refl
        in transport (λ i → B (p1 i) (p0 i) (pe1 i) (pe0 i) (Ap i)) (d> e1' e0' p) ))
      ((λ (((e0' , p0) , (e1' , p1)) , p , q , r) →
          let pe0 : e0' ≡ (predFin (invEq (rot≃ e1) e0))
              pe0 = cong predFin (sym r) ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p1 p0
              pe1 : e1' ≡ (predFin (invEq (rot≃ e0) e1))
              pe1 = sym q ∙ cong₂ (λ e0 → predFin ∘ (invEq (rot≃ e0))) p0 p1
              Ap = toPathP refl
          in transport 
              (λ i → B (p0 i) (p1 i) (pe0 i) (pe1 i) (Ap i)) (d< e0' e1' p)))
    (rotRotCases _ _ p)



unwindPermHeadCompSwap0and1' : 
  (e0 e1 : Fin (ℕsuc (ℕsuc m))) → ¬ e0 ≡ e1 
  →  swap0and1≃ ∙ₑ
     sucPerm (rot≃ (predFin (invEq (rot≃ e0) e1)))
           ∙ₑ rot≃ e0
      ≡  sucPerm (rot≃ (predFin (invEq (rot≃ e1) e0)))
            ∙ₑ rot≃ e1
unwindPermHeadCompSwap0and1' {m} =
   rotRotElim (λ e0 e1 e0' e1' →
         swap0and1≃ ∙ₑ sucPerm (rot≃ e1') ∙ₑ rot≃ e0
      ≡  sucPerm (rot≃ e0') ∙ₑ rot≃ e1)
     (λ e0 e1 → equivEq ∘ (unwindPermHeadCompSwap0and1'Case> e0 e1))
     λ e0 e1 p →
       equivEq
           (cong (_∘ swap0and1) (sym (unwindPermHeadCompSwap0and1'Case> e1 e0 p))
            ∙ cong {x = swap0and1 {m} ∘ swap0and1} {y = idfun _}
                (λ f  → fst (sucPerm (rot≃ e0) ∙ₑ swap0and1≃ ∙ₑ sucPerm (rot≃ e1)) ∘ f)
                  ((cong fst (swap0and1≃²=idEquiv {n = m}))))

unwindPermHeadCompSwap0and1 : (e : Fin (ℕsuc (ℕsuc m)) ≃ Fin (ℕsuc (ℕsuc m)))
  →  swap0and1≃ ∙ₑ
     sucPerm (rot≃ (predFin (invEq (rot≃ (fst e zero)) (equivFun e one))))
           ∙ₑ rot≃ (equivFun e zero)
      ≡  sucPerm (rot≃ (predFin (invEq (rot≃ (fst e one)) (equivFun e zero))))
            ∙ₑ rot≃ (equivFun e one)
unwindPermHeadCompSwap0and1 e =
  unwindPermHeadCompSwap0and1'
    (equivFun e zero) (equivFun e one)
    (znots ∘ invEq (congEquiv e))


unwindPermHeadCompSwap0and1FST : (e : Fin (ℕsuc (ℕsuc m)) ≃ Fin (ℕsuc (ℕsuc m)))
       → fst (unwindPermHead (fst (unwindPermHead e))) ≡
         fst (unwindPermHead (fst (unwindPermHead (swap0and1≃ ∙ₑ e))))
unwindPermHeadCompSwap0and1FST e = isInjectiveSucPerm _ _ (isInjectiveSucPerm _ _
       (∙ₑrightCancel _ _
          (sucPerm (rot≃ (equivFun (fst (unwindPermHead e)) zero))
            ∙ₑ rot≃ (equivFun e zero))
          (equivEq ((refl =→ refl =→ refl)
                 ∙ (cong (λ x → fst
                    (sucPerm x
                     ∙ₑ rot≃ (equivFun e zero)))
                      (sym ((snd (unwindPermHead (fst (unwindPermHead e))))))
                ∙ cong fst (sym (snd (unwindPermHead e)))
                ∙ (refl =→ refl =→ refl)
                ∙ cong (fst ∘ (swap0and1≃ ∙ₑ_)) (snd (unwindPermHead (swap0and1≃ ∙ₑ e))))
                ∙ cong (λ x → fst
                     (swap0and1≃ ∙ₑ sucPerm x
                     ∙ₑ rot≃ (equivFun e one)))
                      (((snd (unwindPermHead (fst (unwindPermHead (swap0and1≃ ∙ₑ e)))))))
                ∙ cong (λ x → fst (rot≃ (equivFun e one)) ∘ x ∘ swap0and1)
                      (cong fst ( sym (respectsCompSucPerm _ _)))
                ∙ cong (_∘ ( 
                 fst ((sucPerm (sucPerm (fst (unwindPermHead (fst (unwindPermHead (swap0and1≃ ∙ₑ e))))))))
                   ∘ swap0and1))
                   (cong fst (sym (unwindPermHeadCompSwap0and1 e)))
                ∙ (refl =→ refl =→ refl)))))


unwindPermId : fst (unwindPermHead (idEquiv (Fin (ℕsuc n)))) ≡ idEquiv _
unwindPermId {ℕzero} = refl
unwindPermId {ℕsuc n} = equivEq refl

unwindPermHeadCompAdjTranspFST : ∀ k → (e : Fin (ℕsuc (ℕsuc m)) ≃ Fin (ℕsuc (ℕsuc m)))
       → (adjTransposition k ∙ₑ (fst (unwindPermHead e))) ≡
         fst (unwindPermHead (adjTransposition (suc k) ∙ₑ e))
unwindPermHeadCompAdjTranspFST k e = equivEq refl

-- unwindPermHeadSucSubst : (e : Fin (ℕsuc m) ≃ Fin (ℕsuc m)) →
--       ∀ {ℓ} → (A : Type ℓ) → (f : (Fin (ℕsuc (ℕsuc m)) → Fin (ℕsuc (ℕsuc m))) → A)
--         → {!!} 
-- unwindPermHeadSucSubst = {!!}

-- unwindPermHeadCompAdjTranspFST' : ∀ k → (e : Fin (ℕsuc (ℕsuc m)) ≃ Fin (ℕsuc (ℕsuc m)))
--        → Square
--           (cong ((adjTransposition (suc k)) ∙ₑ_) (snd (unwindPermHead (e))))         
--           (snd (unwindPermHead (adjTransposition (suc k) ∙ₑ e)))
--           refl
--           (equivEq (refl =→ refl)
--            ∙ cong ((_∙ₑ rot≃ (equivFun e zero)) ∘ sucPerm) (unwindPermHeadCompAdjTranspFST k e))
          
-- unwindPermHeadCompAdjTranspFST' k e = {!!}



-- unwindPermIdSq :  Square
--                          (snd (unwindPermHead (idEquiv (Fin (ℕsuc n)))))
--                          {!!}
--                          refl
--                          {!unwindPermId!}
-- unwindPermIdSq = {!!}

unwindPermHeadIso : Iso (Fin (ℕsuc n) ≃ Fin (ℕsuc m))
                        (Fin (ℕsuc m) × (Fin n ≃ Fin m) )
Iso.fun unwindPermHeadIso e = equivFun e zero , fst (unwindPermHead e)
Iso.inv unwindPermHeadIso (k , e') = sucPerm e' ∙ₑ rot≃ k
Iso.rightInv unwindPermHeadIso (k , e') =
  ΣPathP (rot≃-zero _ ,
    isInjectiveSucPerm _ _
     ( ∙ₑrightCancel _ _ (rot≃ k)
         (cong (sucPerm (fst (unwindPermHead (sucPerm e' ∙ₑ rot≃ k))) ∙ₑ_)
            (cong rot≃ (sym (rot≃-zero k)))
          ∙ sym (snd (unwindPermHead (sucPerm e' ∙ₑ rot≃ k))))  ))
Iso.leftInv unwindPermHeadIso e = sym (snd (unwindPermHead e))


isInjectiveFin≃ : Fin n ≃ Fin m → n ≡ m
isInjectiveFin≃ {ℕzero} {ℕzero} x = refl
isInjectiveFin≃ {ℕzero} {ℕsuc _} x = ⊥.rec (¬Fin0 (invEq x zero))
isInjectiveFin≃ {ℕsuc _} {ℕzero} x = ⊥.rec (¬Fin0 (equivFun x zero))
isInjectiveFin≃ {ℕsuc _} {ℕsuc _} x = cong ℕsuc (isInjectiveFin≃ (fst (unwindPermHead x)))

≡→Fin≃ : n ≡ m → Fin n ≃ Fin m
≡→Fin≃ = isoToEquiv ∘ pathToIso ∘ cong Fin

rot≃∙ₑ≡→Fin≃ : (p : n ≡ m) → ∀ k →
   PathP (λ i → Fin (p i) ≃ Fin m)
      (invEquiv (rot≃ k) ∙ₑ ≡→Fin≃ p)
      (invEquiv (rot≃ (subst Fin p k)))
rot≃∙ₑ≡→Fin≃ =
  J (λ m p → ∀ k →  PathP (λ i → Fin (p i) ≃ Fin m)
      (invEquiv (rot≃ k) ∙ₑ ≡→Fin≃ p)
      (invEquiv (rot≃ (subst Fin p k))))
       λ k → equivEq (funExt λ _ → transportRefl _)
         ∙ cong (invEquiv ∘ rot≃) (sym (transportRefl k))

transportFin-suc : (p' : n ≡ m) → (p : (ℕsuc n) ≡ (ℕsuc m)) → ∀ k
                  → (subst Fin p (suc k)) ≡ suc (subst Fin p' k)
transportFin-suc =
  J (λ _ p' → ∀ p k → (subst Fin p (suc k)) ≡ suc (subst Fin p' k))
     λ _ k → isSet-subst {B = Fin} isSetℕ _ _ ∙ cong suc (sym (transportRefl k))

transportFin-zero : (p : (ℕsuc n) ≡ (ℕsuc m))
                  → zero ≡ subst Fin p zero
transportFin-zero =
  J (λ {ℕzero _ → Unit ; (ℕsuc _) p → zero ≡ subst Fin p zero })
    (sym (transportRefl zero))

-- transposeHead : Fin n →  Fin n ≃ Fin n
-- transposeHead zero = idEquiv _
-- transposeHead (suc k) = rot≃ (suc k) ∙ₑ invEquiv (rot≃ (weakenFin k))

transposeHead : Fin n → Iso (Fin (ℕsuc n)) (Fin (ℕsuc n))
transposeHead zero = swap0and1Iso
transposeHead (suc k) = compIso swap0and1Iso (compIso (sucPermIso (transposeHead k)) swap0and1Iso)

transposeHead' : Fin n → Iso (Fin n) (Fin n)
transposeHead' zero = idIso
transposeHead' (suc x) = transposeHead x

transposition : Fin n → Fin n → Iso (Fin n) (Fin n)
transposition zero = transposeHead'
transposition (suc x) zero = transposeHead x
transposition (suc x) (suc x₁) = sucPermIso (transposition x x₁)

SymData : ℕ → Group ℓ-zero
SymData n = Symmetric-Group (Fin n) isSetFin

IsoFin2Bool : Iso (Fin 2) Bool
Iso.fun IsoFin2Bool = λ {zero → true ; one → false }
Iso.inv IsoFin2Bool = λ {true → zero ; false → one }
Iso.rightInv IsoFin2Bool = λ {true → refl ; false → refl }
Iso.leftInv IsoFin2Bool = λ {zero → refl ; one → refl }

IsoFin≃2Bool≃ : ⟨ SymData 2 ⟩ ≃ Bool
IsoFin≃2Bool≃ =  ( cong≃ (λ x → x ≃ x) (isoToEquiv IsoFin2Bool)
 ∙ₑ invEquiv univalence) ∙ₑ (invEquiv (B.BoolReflection.reflectEquiv))

BoolElim : ∀ {ℓ} {A : Bool → Type ℓ}
              → A true → A false → ∀ x → A x 
BoolElim {A = A} xId xNot false = xNot
BoolElim {A = A} xId xNot true = xId


Perm2Elim : ∀ {ℓ} {A : ⟨ SymData 2 ⟩ → Type ℓ}
              → A (idEquiv _) → A swap0and1≃ → ∀ x → A x 
Perm2Elim {ℓ} {A} xId xNot =
  let z = subst (λ X → Σ (X × X) λ (t , f) → {A : X → Type ℓ}
              → A t → A f → ∀ x → A x) (sym (ua IsoFin≃2Bool≃)) (_ , BoolElim)
      ww : fst z ≡ (swap0and1≃ , (idEquiv _) )
      ww = ΣPathP
          ((equivEq ((λ i → transp (λ i → Fin 2) i
                      ((Iso.inv IsoFin2Bool)
                       (B.not
                        (Iso.fun IsoFin2Bool
                         (transp (λ j → Fin 2) i zero)))))
                         
                  =→ ((λ i → transp (λ i → Fin 2) i
                      ((Iso.inv IsoFin2Bool)
                       (B.not
                        (Iso.fun IsoFin2Bool
                         (transp (λ j → Fin 2) i one))))))
                  =→ =■))
          , equivEq ((λ i → transp (λ i → Fin 2) i
                         ((Iso.inv IsoFin2Bool)
                          (Iso.fun IsoFin2Bool
                           (transp (λ j → Fin 2) i zero)))
                         ) =→ ((λ i → transp (λ i → Fin 2) i
                         ((Iso.inv IsoFin2Bool)
                          (Iso.fun IsoFin2Bool
                           (transp (λ j → Fin 2) i one)))
                         )) =→ =■))
  in snd z (subst A (sym (cong (fst) ww)) xNot)
           ((subst A (sym (cong (snd) ww)) xId))
  
sucConcat : ∀ l →
           concatG (SymData (ℕsuc (ℕsuc n)))
             ((mapList adjTransposition (mapList suc l)))
             ≡ sucPerm
                  (concatG (SymData (ℕsuc n))
                   (mapList adjTransposition l)) 
sucConcat =
  ind (equivEq λ { _ zero → zero ; _ (suc k) → suc k })
      λ {a} p → equivEq (
         (λ { i zero → fst (p i) zero
            ; i (suc k) → fst (p i) (suc (adjTransposition a .fst k))
            }))


punchHeadInOutL : (k : Fin (ℕsuc n)) → Σ (List (Fin n))
  λ l → concatG (SymData _) (mapList adjTransposition l) ≡ rot≃ k 
punchHeadInOutL {n = n} zero = [] , refl
fst (punchHeadInOutL {n = ℕsuc n} (suc k)) = zero ∷ mapList suc (fst (punchHeadInOutL k))
snd (punchHeadInOutL {n = ℕsuc n} (suc k)) = 
  cong ( swap0and1≃ ∙ₑ_)
    (sucConcat (fst (punchHeadInOutL k)) ∙ cong sucPerm (snd (punchHeadInOutL k)))


generatedSym : ∀ n → GeneratedByConstr (SymData (ℕsuc n)) adjTransposition 
generatedSym ℕzero = λ _ → [] , equivEq (funExt λ x → isContr→isProp isContrFin1 _ _) 
generatedSym (ℕsuc n) e = 
  let (e' , p) = unwindPermHead e
      (l , p') = (generatedSym n e')
  in (mapList suc l ++ fst (punchHeadInOutL (equivFun e zero))   ,
         (cong (concatG (SymData (ℕsuc (ℕsuc n))))
           (map-++ (adjTransposition) (mapList suc l)
                          ((fst (punchHeadInOutL (fst e zero)))))
          ∙ sym (concatG· {G = (SymData (ℕsuc (ℕsuc n)))}
           (mapList adjTransposition (mapList suc l))
             (mapList adjTransposition (fst (punchHeadInOutL (equivFun e zero)))))
           
       ∙ cong₂ _∙ₑ_
           (sucConcat l ∙ cong sucPerm p') (snd (punchHeadInOutL (equivFun e zero)))) ∙ sym p)

-- elimSymFin : ∀ {ℓ} → (A : ∀ n → fst (SymData (ℕsuc n)) → Type ℓ)
--              → (∀ n → A n (idEquiv _))
--              → (∀ n →  ∀ e → A (ℕsuc n) e → A (ℕsuc n) (swap0and1≃ ∙ₑ e))
--              → (∀ n →  ∀ (k : Fin {!!})
--                 -- → ?
--                   → ∀ e
--                   → A (ℕsuc n) e
--                   → A (ℕsuc n) (adjTransposition (suc k) ∙ₑ e))
--              -- → (∀ n → (∀ e → A n e) → ∀ k e
--              -- →  A (ℕsuc n) e → A (ℕsuc n) (rot≃ k ∙ₑ e))
--              →  ∀ n → ∀ k → A n k
-- elimSymFin A A𝟙 _ _ ℕzero k = subst (A ℕzero) (equivEq (snd isContrFin1 _ =→ =■)) (A𝟙 ℕzero) 
-- elimSymFin A A𝟙 x x₁ (ℕsuc n) =
--   GeneratedElimConstr'
--     (SymData (ℕsuc (ℕsuc n)))
--     (generatedSym (ℕsuc n))
--     _
--     (A𝟙 _)
--     z
--   where
--     z : _
--     z zero = x _
--     z (suc a) e z = {!x₁ n ? ? ? !}

sucPermFDMorphism : ∀ n → GroupHom (SymData n) (SymData (ℕsuc n))
fst (sucPermFDMorphism n) = sucPerm
IsGroupHom.pres· (snd (sucPermFDMorphism n)) x y =
  equivEq λ { i zero → zero ; i (suc k) → suc (y .fst (x .fst k)) }
IsGroupHom.pres1 (snd (sucPermFDMorphism n)) =
  equivEq λ { i zero → zero ; i (suc k) → suc k }
IsGroupHom.presinv (snd (sucPermFDMorphism n)) x =
  equivEq λ { i zero → zero ; i (suc k) → suc (snd x .equiv-proof k .fst .fst) }


isInjectiveSucPermFDMorphism : ∀ n → isInjective (sucPermFDMorphism n)
isInjectiveSucPermFDMorphism n x x₁ =
  isInjectiveSucPerm x (idEquiv _) (x₁ ∙ sym sucPermId) 


generatedSymId : ∀ n → fst (generatedSym n (idEquiv (Fin (ℕsuc n)))) ≡ []
generatedSymId ℕzero = refl
generatedSymId (ℕsuc n) =
         cong ((_++ []) ∘ mapList suc)
        (cong (fst ∘ (generatedSym n)) (equivEq refl)
          ∙ generatedSymId n) 



permutationFromList : (l : List ℕ) → Fin (length l) ≃ Fin (length l)
permutationFromList = ind (idEquiv _) λ {a} x → sucPerm x ∙ₑ rot≃ (fromℕForce a)
