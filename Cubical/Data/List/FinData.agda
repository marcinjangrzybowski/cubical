{-# OPTIONS --safe #-}
module Cubical.Data.List.FinData where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

open import Cubical.Data.List
open import Cubical.Data.FinData
open import Cubical.Data.Nat renaming (snotz to ℕsnotz ; znots to ℕznots)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎


open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.HITs.GroupoidQuotients as GQ renaming ([_] to [_]//)


open import Cubical.HITs.FiniteMultiset as FM
  renaming (_∷_ to _∷fm_ ; [] to []fm ; _++_ to _++fm_) hiding ([_])
open import Cubical.HITs.FreeComMonoids using (FreeComMonoid;AssocList≃FreeComMonoid)
open import Cubical.HITs.AssocList using (FMSet≃AssocList)

variable
  ℓ : Level
  A : Type ℓ

-- copy-paste from agda-stdlib
lookup : ∀ (xs : List A) → Fin (length xs) → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

tabulate : ∀ n → (Fin n → A) → List A
tabulate zero ^a = []
tabulate (suc n) ^a = ^a zero ∷ tabulate n (^a ∘ suc)

length-tabulate : ∀ n → (^a : Fin n → A) → length (tabulate n ^a) ≡ n
length-tabulate zero ^a = refl
length-tabulate (suc n) ^a = cong suc (length-tabulate n (^a ∘ suc))

tabulate-lookup : ∀ (xs : List A) → tabulate (length xs) (lookup xs) ≡ xs
tabulate-lookup [] = refl
tabulate-lookup (x ∷ xs) = cong (x ∷_) (tabulate-lookup xs)

lookup-tabulate : ∀ n → (^a : Fin n → A)
  → PathP (λ i → (Fin (length-tabulate n ^a i) → A)) (lookup (tabulate n ^a)) ^a
lookup-tabulate (suc n) ^a i zero = ^a zero
lookup-tabulate (suc n) ^a i (suc p) = lookup-tabulate n (^a ∘ suc) i p

lookup-tabulateT : ∀ n → (^a : Fin n → A) → ∀ k
    → lookup (tabulate n ^a) (subst⁻ Fin (length-tabulate n ^a) k) ≡ ^a k
lookup-tabulateT n ^a k = (sym (transportRefl _)) ∙ funExt⁻ (fromPathP (lookup-tabulate n ^a)) k

permute : ∀ {n} (l : List A) → Fin n ≃ Fin (length l) → List A
permute l e = tabulate _ (lookup l ∘ (equivFun e))

length-permute : ∀ {n} (l : List A) → (e : Fin n ≃ Fin (length l)) →
                  length (permute l e) ≡ n 
length-permute l e = length-tabulate _ _


infix 4  _↔_

_↔_ : List A → List A → Type _
x ↔ y =
  Σ (Fin (length x) ≃ Fin (length y))
     λ e → ∀ k → lookup x k ≡ lookup y (equivFun e k)

↔permute : ∀ {n} (l : List A) → (e : Fin n ≃ Fin (length l))
                → l ↔ (permute l e) 
↔permute l e = invEquiv e ∙ₑ ≡→Fin≃ (sym (length-permute l e)) ,
    λ k → cong (lookup l) (sym (secEq e k))
      ∙ sym (lookup-tabulateT _ (lookup l ∘ (fst e)) (invEq e k))

isRefl↔ : BinaryRelation.isRefl (_↔_ {A = A})
isRefl↔ = (λ _ → idEquiv _ , (λ _ → refl))

isSym↔ : BinaryRelation.isSym (_↔_ {A = A})
isSym↔ _ b (e , p) = invEquiv e , λ k → cong (lookup b) (sym (secEq e _)) ∙ sym (p _)

isTrans↔ : BinaryRelation.isTrans (_↔_ {A = A})
isTrans↔ _ _ _ (e , p) (f , q) = e ∙ₑ f , λ _ → p _ ∙ q _

infixr 30 _∙↔_

_∙↔_ : {a b c : List A} → a ↔ b → b ↔ c → a ↔ c
_∙↔_ {a = a} {b} {c} p q = isTrans↔ a b c p q

isEquivRel↔ : BinaryRelation.isEquivRel {ℓ = ℓ} {A = List A} _↔_
isEquivRel↔ = BinaryRelation.equivRel isRefl↔ isSym↔ isTrans↔

↔→length≡ : ∀ {x y : List A} →  x ↔ y → length x ≡ length y
↔→length≡ = isInjectiveFin≃ ∘ fst

¬nil↔cons : ∀ {x : A} {xs} → ¬ ([] ↔ x ∷ xs)
¬nil↔cons = ℕznots ∘ ↔→length≡ {x = []}  

¬cons↔nil : ∀ {x : A} {xs} → ¬ (x ∷ xs ↔ [])
¬cons↔nil = ℕsnotz ∘ ↔→length≡ {y = []}  

_∷↔_ : ∀ (a : A) {xs ys} → xs ↔ ys → a ∷ xs ↔ a ∷ ys
a ∷↔ (e , p) = sucPerm e , λ { zero → refl ; (suc _) → p _}

≡→↔ : ∀ {xs ys : List A} → xs ≡ ys → xs ↔ ys
≡→↔ {xs = xs} = J (λ ys p → xs ↔ ys) (isRefl↔ xs)

headSwap↔ : (x y : A) → ∀ l → x ∷ y ∷ l ↔ y ∷ x ∷ l
headSwap↔ x y l =
  swapHead , λ { zero → refl ; one → refl ; (suc (suc k)) → refl }


_∷↔∷ʳ_ : ∀ xs → (x : A) → xs ∷ʳ x ↔ x ∷ xs
_∷↔∷ʳ_ = ind (isRefl↔ ∘ [_])
  λ x _ → ≡→↔ (++-assoc [ _ ] _ [ _ ]) ∙↔ (_ ∷↔ x _) ∙↔ headSwap↔ _ _ _
 
_↔∷ʳ_ : ∀ {xs ys} → xs ↔ ys → ∀ (a : A) → xs ∷ʳ a ↔ ys ∷ʳ a
_↔∷ʳ_ {xs = xs} {ys} r _ =
  isTrans↔ (xs ∷ʳ _) _ (ys ∷ʳ _) (xs ∷↔∷ʳ _)
   (isTrans↔ _ _ (ys ∷ʳ _) (_ ∷↔ r) (isSym↔ (ys ∷ʳ _) (_ ∷ ys)  (ys ∷↔∷ʳ _)))


lookup-FinSumChar : ∀ {xs ys : List A} →
        ∀ k → lookup (xs ++ ys) k ≡
         ⊎.rec (lookup xs) (lookup ys) (invEq (FinSumChar.Equiv (length xs) (length ys)
            ∙ₑ ≡→Fin≃ (sym (length++ xs ys))) k)
lookup-FinSumChar {xs = []} {ys} k = cong (lookup ys) (sym (transport⁻Transport refl k))
lookup-FinSumChar {xs = x ∷ xs} {ys} zero = 
  cong (⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘ (FinSumChar.inv _ _))
  (transportFinFix-zero _ ∙ substComposite Fin _ _ zero)

lookup-FinSumChar {xs = x ∷ xs} {ys} (suc k) =
   _ ≡⟨ lookup-FinSumChar {xs = xs} {ys} k ⟩
   _ ≡⟨ h (FinSumChar.inv _ _ _) ⟩
   _ ≡⟨ cong (⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘ FinSumChar.inv _ _)
           (_ ≡⟨ sym (cong {B = λ _ → Fin _} suc (substComposite Fin _ _ k)) ⟩
            _ ≡⟨ sym (transportFinFix _ _ k) ⟩
            _ ≡⟨ substComposite Fin _ _ (suc k) ⟩ _
            ∎) ⟩
   _ ∎ 

  where

    h : ∀ z → ⊎.rec (lookup xs) (lookup ys) z ≡
              ⊎.rec (lookup (x ∷ xs)) (lookup ys)
              (FinSumChar.invSucAux _ _ z)
    h (inl _) = refl
    h (inr _) = refl


cong↔++R : ∀ {xs ys : List A} → xs ↔ ys → ∀ l → xs ++ l ↔ ys ++ l
fst (cong↔++R {xs = xs} {ys} x l) =
     ≡→Fin≃ (length++ xs l) ∙ₑ
    (invEquiv (FinSumChar.Equiv (length xs) (length l))
     ∙ₑ ⊎-equiv (fst x) (idEquiv _)
     ∙ₑ FinSumChar.Equiv (length ys) (length l) )
     ∙ₑ ≡→Fin≃ (sym (length++ ys l))
snd (cong↔++R {A = A} {xs = xs} {ys} x l) k =
  lookup-FinSumChar {xs = xs} {l} k ∙
   (λ i → ⊎.rec (λ k' → snd x k' i) (lookup l) (invEq
       (FinSumChar.Equiv (length xs) (length l) ∙ₑ
        ≡→Fin≃ (sym (length++ xs l)))
       k))
   ∙ sym (recMap (equivFun (fst x)) (lookup ys) (idfun _) (lookup l)
      (invEq
       (FinSumChar.Equiv (length xs) (length l) ∙ₑ ≡→Fin≃ (sym (length++ xs l))) k))
   ∙ cong (⊎.rec (lookup ys) (lookup l))
      (h (transp (λ j → Fin (length++ xs l j)) i0 k))
   ∙ sym (lookup-FinSumChar {xs = ys} {l} _)
  where
    h : (k : Fin (length xs + length l)) →           
         ⊎.map (fst (fst x)) (λ x₁ → x₁)
         (FinSumChar.inv (length xs) (length l)
          (transp (λ i → Fin (length xs + length l)) i0
           (k)))
         ≡
         FinSumChar.inv (length ys) (length l)
         (transp (λ i → Fin (length ys + length l)) i0
          (transp (λ j → Fin (length++ ys l j)) i0
           (transp (λ i → Fin (length++ ys l (~ i))) i0
            (FinSumChar.fun (length ys) (length l)
             (⊎Iso (equivToIso (fst x)) (equivToIso (idEquiv (Fin (length l))))
              .Iso.fun
              (FinSumChar.inv (length xs) (length l)
               k))))))
    h k =
         cong (⊎.map (fst (fst x)) (λ x₁ → x₁) ∘ (FinSumChar.inv (length xs) (length l)))
           (transportRefl k)
      ∙  (⊎.elim
           {C = (λ y → ⊎.map (fst (fst x)) (λ x₁ → x₁) y ≡
                  ⊎Iso (equivToIso (fst x)) (equivToIso (idEquiv (Fin (length l))))
                      .Iso.fun y)}
           (λ _ → refl) (λ _ → refl)
          (FinSumChar.inv (length xs) (length l) k)) 
      ∙ sym (FinSumChar.ret (length ys) (length l) _)
      ∙ cong (FinSumChar.inv (length ys) (length l))
            (sym (transportRefl (FinSumChar.fun (length ys) (length l)
        (⊎Iso (equivToIso (fst x)) (equivToIso (idEquiv (Fin (length l))))
         .Iso.fun (FinSumChar.inv (length xs) (length l) k)))))
      ∙ cong (FinSumChar.inv (length ys) (length l)
           ∘ transp (λ i → Fin (length ys + length l)) i0)
            (sym (transportTransport⁻ (cong Fin (length++ ys l))
              (FinSumChar.fun (length ys) (length l)
             (⊎Iso (equivToIso (fst x)) (equivToIso (idEquiv (Fin (length l))))
              .Iso.fun
              (FinSumChar.inv (length xs) (length l)
               k)))))
 
_++↔_ : (x y : List A) → x ++ y ↔ y ++ x
x ++↔ [] = ≡→↔ (++-unit-r x)
[] ++↔ y@(_ ∷ _) = ≡→↔ (sym (++-unit-r y) )
(x ∷ xs) ++↔ (y ∷ ys) = 
  isTrans↔ (x ∷ (xs ++ y ∷ ys)) (x ∷ y ∷ ys ++ xs) (y ∷ (ys ++ x ∷ xs))
    (x ∷↔ ((xs ++↔ (y ∷ ys))))
      (isTrans↔ _ _ _ (headSwap↔ x y (ys ++ xs))
        (y ∷↔ isTrans↔ _ ((ys ++ [ x ]) ++ xs) (ys ++ x ∷ xs)
         (cong↔++R {ys = ( ys ∷ʳ x)} (isSym↔ ( ys ∷ʳ x) _ (ys ∷↔∷ʳ x)) xs)
         (≡→↔ (++-assoc ys [ x ] xs))))


rev↔ : (xs : List A) → xs ↔ rev xs
rev↔ [] = isRefl↔ []
rev↔ (x ∷ xs) =
  isTrans↔ _ _ (rev xs ++ [ x ])
    (x ∷↔ rev↔ xs) (isSym↔ ((rev xs) ∷ʳ x) _ ((rev xs) ∷↔∷ʳ x))

List/↔ : (A : Type ℓ) → Type ℓ
List/↔ A =  List A / _↔_

pattern []/ = [ [] ]/

_∷/_ : A → List/↔ A → List/↔ A
_∷/_ {A = A} a = SQ.rec squash/ ([_]/ ∘ (a ∷_))
            λ _ _ r → eq/ _ _ (sucPerm (fst r)
             , λ { zero → refl ; (suc _) → snd r _})


List→FMSet : List A → FMSet A
List→FMSet {A = A} = foldr {B = FMSet A} _∷fm_ []fm

h-swap : (l : List A) → ∀ k → List→FMSet l ≡ List→FMSet (permute l (PunchInOut≃ k))
h-swap (x ∷ l) zero = cong List→FMSet (sym (tabulate-lookup (x ∷ l)))
h-swap (x ∷ x₁ ∷ l) one i = comm x x₁ (List→FMSet (tabulate-lookup l (~ i))) i
h-swap (x ∷ x₁ ∷ l) (suc (suc k)) = cong (x ∷fm_) (h-swap (x₁ ∷ l) (suc k)) ∙ comm _ _ _

↔→FMSet≡ : (a b : List A) → a ↔ b → List→FMSet a ≡ List→FMSet b
↔→FMSet≡ a b r =  h (length a) a b refl (sym (↔→length≡ {x = a} {y = b} r)) r
 where
  h : ∀ n → (a b : List A) → length a ≡ n → length b ≡ n →
         a ↔ b → List→FMSet a ≡ List→FMSet b
  h zero [] [] x x₁ x₂ = refl
  h zero [] (x₃ ∷ b) x x₁ x₂ = ⊥.rec (ℕsnotz x₁)
  h zero (x₃ ∷ a) _ x x₁ x₂ = ⊥.rec (ℕsnotz x)
  h (suc n) [] b x x₁ x₂ = ⊥.rec (ℕznots x)
  h (suc n) (x₃ ∷ a) [] x x₁ x₂ = ⊥.rec (ℕznots x₁)
  h (suc n) (x ∷ xs) (y ∷ ys) pX pY ro@(e , p) =
    let (e' , p') = Fin≃SucEquiv'' e
        y' = lookup (y ∷ ys) (equivFun (PunchInOut≃ (equivFun e zero)) zero)
        ys' = tabulate (length xs)
                 (lookup (y ∷ ys) ∘ 
                    (equivFun (sucPerm e' ∙ₑ PunchInOut≃ (equivFun e zero))) ∘ suc)

    in cong List→FMSet (sym (tabulate-lookup (x ∷ xs)) ∙
            cong (tabulate _) (funExt p ∙ cong (lookup (y ∷ ys) ∘_) (cong equivFun p')))
         ∙∙
         cong (y' ∷fm_)
         (h n ys' (permute ys' (invEquiv e' ∙ₑ ≡→Fin≃ (sym (length-tabulate _ _))))
           (length-tabulate _ _ ∙ injSuc pX) (length-tabulate (length ys) _ ∙ sym (isInjectiveFin≃ e')
              ∙ injSuc pX)
           (↔permute ys' ((invEquiv e' ∙ₑ ≡→Fin≃ (sym (length-tabulate _ _)))))
           ∙ cong (List→FMSet ∘ tabulate (length ys))
             (cong (_∘ invEq e') (funExt (lookup-tabulateT _ _)) ∙
              cong (((
                 lookup (y ∷ ys) ∘ 
                  (equivFun (PunchInOut≃ (equivFun e zero))) ∘  suc) ∘_) ∘ fst) ((invEquiv-is-linv e'))))
          ∙∙
           sym (h-swap (y ∷ ys) (equivFun e zero))


IsoList/↔FMSet : Iso (List/↔ A) (FMSet A)
IsoList/↔FMSet {A = A} = w
  where

    toFM : _
    toFM = SQ.rec trunc List→FMSet ↔→FMSet≡      

    fromFM : _
    fromFM = FM.Rec.f squash/
        []/ _∷/_
        λ _ _ → SQ.elimProp (λ _ → squash/ _ _)
          λ _ → eq/ _ _ (swapHead ,
             λ { zero → refl ; one → refl ; (suc (suc k)) → refl})

    w : Iso (List/↔ A) (FMSet A)
    Iso.fun w = toFM
    Iso.inv w = fromFM
    Iso.rightInv w = 
      FM.ElimProp.f (trunc _ _) refl
        λ a {xs} →
          ((SQ.elimProp {P = λ x → toFM (a ∷/ x) ≡ _ ∷fm toFM x}
               (λ _ → trunc _ _) (λ _ → refl) ∘ fromFM) xs ∙_) ∘ cong (_ ∷fm_)

    Iso.leftInv w = SQ.elimProp (λ x → squash/ _ _) (ind refl (cong (_ ∷/_)))


List/↔≃FreeComMonoid : List/↔ A ≃ FreeComMonoid A
List/↔≃FreeComMonoid = isoToEquiv IsoList/↔FMSet ∙ₑ FMSet≃AssocList ∙ₑ AssocList≃FreeComMonoid

List//↔ : (A : Type ℓ) → Type ℓ
List//↔ A =  List A // isTrans↔

_∷//_ : A → List//↔ A → List//↔ A
_∷//_ {A = A} = (λ a → GQ.rec isTrans↔ squash// ([_]// ∘ (a ∷_))
          (λ {x} {y} r → eq// ((sucPerm (fst r)) , w {x = x} {y} {r} a ))
           λ r s →
             comp// 
                 ((sucPerm (fst r)) , w a )
                 ((sucPerm (fst s)) , w a ) ▷
                  cong eq//
                    (ΣPathP
                       ((equivEq (funExt (λ { zero → refl ; (suc _) → refl })))
                         , funExt (λ { zero → sym compPathRefl ; (suc _) → refl }))))
  where
    w : {x y : List A} → {r : x ↔ y } → ∀ a _ → _
    w _ zero = refl
    w {r = r} _ (suc _) = snd r _


-- funExt∙ : ∀ {ℓ'} {B C : Type ℓ'} {f g h : B → A}
--             → (p : ∀ k → f k ≡ g k) → (q : ∀ k → g k ≡ h k)
--             → funExt (λ k → p k ∙ q k ) ≡ funExt p ∙ funExt q
-- funExt∙ p q = refl

module FC2M where
  open import Cubical.HITs.FiniteMultiset.Base2 as FM2
       renaming (_∷_ to _∷fm2_ ; [] to []fm2 ; _++_ to _++fm2_) hiding ([_])

  List→FMSet2 : List A → FMSet2 A
  List→FMSet2 {A = A} = foldr {B = FMSet2 A} _∷fm2_ []fm2

  h-swap2 : (l : List A) → ∀ k → List→FMSet2 l ≡ List→FMSet2 (permute l (PunchInOut≃ k))
  h-swap2 (x ∷ l) zero = cong List→FMSet2 (sym (tabulate-lookup (x ∷ l)))
  h-swap2 (x ∷ x₁ ∷ l) one i = comm x x₁ (List→FMSet2 (tabulate-lookup l (~ i))) i
  h-swap2 (x ∷ x₁ ∷ l) (suc (suc k)) = cong (x ∷fm2_) (h-swap2 (x₁ ∷ l) (suc k)) ∙ comm _ _ _

  ↔→FMSet≡2 : (a b : List A) → a ↔ b → List→FMSet2 a ≡ List→FMSet2 b
  ↔→FMSet≡2 a b r =  h (length a) a b refl (sym (↔→length≡ {x = a} {y = b} r)) r
   where
    h : ∀ n → (a b : List A) → length a ≡ n → length b ≡ n →
           a ↔ b → List→FMSet2 a ≡ List→FMSet2 b
    h zero [] [] x x₁ x₂ = refl
    h zero [] (x₃ ∷ b) x x₁ x₂ = ⊥.rec (ℕsnotz x₁)
    h zero (x₃ ∷ a) _ x x₁ x₂ = ⊥.rec (ℕsnotz x)
    h (suc n) [] b x x₁ x₂ = ⊥.rec (ℕznots x)
    h (suc n) (x₃ ∷ a) [] x x₁ x₂ = ⊥.rec (ℕznots x₁)
    h (suc n) (x ∷ xs) (y ∷ ys) pX pY ro@(e , p) =
      let (e' , p') = Fin≃SucEquiv'' e
          y' = lookup (y ∷ ys) (equivFun (PunchInOut≃ (equivFun e zero)) zero)
          ys' = tabulate (length xs)
                   (lookup (y ∷ ys) ∘ 
                      (equivFun (sucPerm e' ∙ₑ PunchInOut≃ (equivFun e zero))) ∘ suc)

      in cong List→FMSet2 (sym (tabulate-lookup (x ∷ xs))) ∙
           ((cong (List→FMSet2 ∘ tabulate _) (funExt p))
            ∙ ((cong (List→FMSet2 ∘ tabulate _ ∘ (lookup (y ∷ ys) ∘_) ∘ equivFun) p')
           ∙∙
           cong (y' ∷fm2_)
           (h n ys' (permute ys' (invEquiv e' ∙ₑ ≡→Fin≃ (sym (length-tabulate _ _))))
             (length-tabulate _ _ ∙ injSuc pX) (length-tabulate (length ys) _ ∙ sym (isInjectiveFin≃ e')
                ∙ injSuc pX)
             (↔permute ys' ((invEquiv e' ∙ₑ ≡→Fin≃ (sym (length-tabulate _ _)))))
             ∙ cong (List→FMSet2 ∘ tabulate (length ys))
               (cong (_∘ invEq e') (funExt (lookup-tabulateT _ _)) ∙
                cong (((
                   lookup (y ∷ ys) ∘ 
                    (equivFun (PunchInOut≃ (equivFun e zero))) ∘  suc) ∘_) ∘ fst) ((invEquiv-is-linv e'))))
            ∙∙
             sym (h-swap2 (y ∷ ys) (equivFun e zero))))

  ↔→FMSet≡2Trans : (a b c : List A) → (p : a ↔ b) → (q : b ↔ c)
                    → ↔→FMSet≡2 a b p ∙ ↔→FMSet≡2 b c q ≡
                      ↔→FMSet≡2 a c (isTrans↔ a b c p q)
  ↔→FMSet≡2Trans = {!!}
  -- ↔→FMSet≡2Trans [] [] [] p q = sym (doubleCompPath-filler refl _ _)
  -- ↔→FMSet≡2Trans [] [] (x ∷ c) p q = {!!}
  -- ↔→FMSet≡2Trans [] (x ∷ b) [] p q = {!!}
  -- ↔→FMSet≡2Trans [] (x ∷ b) (x₁ ∷ c) p q = {!!}
  -- ↔→FMSet≡2Trans (x ∷ a) [] [] p q = {!!}
  -- ↔→FMSet≡2Trans (x ∷ a) [] (x₁ ∷ c) p q = {!!}
  -- ↔→FMSet≡2Trans (x ∷ a) (x₁ ∷ b) [] p q = {!!}
  -- ↔→FMSet≡2Trans (x ∷ xs) (y ∷ ys) (z ∷ zs) (e , p) (f , q) =
  --   sym (assoc _ _ _) ∙
  --      (cong ((cong List→FMSet2 (sym (tabulate-lookup (x ∷ xs)))) ∙_)
  --        (sym (assoc _ _ _)
  --           ∙  cong ((cong (List→FMSet2 ∘ tabulate _) (funExt p)) ∙_)
  --          {!!}
  --          ∙ assoc _ _ {!!}
  --         ∙ cong₂ _∙_ (sym (cong-∙ (List→FMSet2 ∘ tabulate _) (funExt p)
  --                           (cong (_∘ (equivFun e)) (funExt q))))
  --                         {!!}))



  IsoList//↔FMSet2 : Iso (List//↔ A) (FMSet2 A)
  IsoList//↔FMSet2 {A = A} = w
    where

      toFM : _
      toFM = GQ.rec isTrans↔ trunc List→FMSet2
        (λ {a} {b} → ↔→FMSet≡2 a b)
         λ {a} {b} {c} _ _ →
           compPath-filler _ _ ▷ ↔→FMSet≡2Trans a b c _ _     

      fromFM : _
      fromFM = FM2.Rec.f
         squash// [ [] ]// _∷//_
         (λ x y → GQ.elimSet _ (λ _ → squash// _ _)
             (λ _ → eq// (headSwap↔ _ _ _)) (λ {a} {b} r i j → h x y {a} {b} r j i) )
         (λ x y → GQ.elimProp _ (λ _ → squash// _ _ _ _)
                {!!})
         {!!}
         {!!}
         {!!}

         where

           h'' : ∀ x y → {a b : List A} (r : a ↔ b) →
                      (λ i → (y ∷// (x ∷// eq// {a = a} {b} r i)))
                    ≡ eq// {a = y ∷ x ∷ a} {y ∷ x ∷ b} (y ∷↔ (x ∷↔ r))
           h'' x y r = cong eq// (ΣPathP (refl ,
                funExt λ { zero → refl ; one → refl ; (suc (suc k)) → refl }))


           -- h' : ∀ x y → {a b : List A} (r : a ↔ b) →
           --         eq// {a = x ∷ y ∷ a} {y ∷ x ∷ a} (headSwap↔ x y a) ∙
           --            (λ i → (y ∷// (x ∷// eq// {a = a} {b} r i)))
           --          ≡ {!!}
           -- h' = {!!}

           h : ∀ x y → {a b : List A} (r : a ↔ b) →
                   Square
                   (λ i → (x ∷// (y ∷// eq// {a = a} {b} r i)))
                   (λ i → (y ∷// (x ∷// eq// {a = a} {b} r i)))
                   (eq// {a = x ∷ y ∷ a} {y ∷ x ∷ a} (headSwap↔ x y a))
                   (eq// {a = x ∷ y ∷ b} {y ∷ x ∷ b} (headSwap↔ x y b))
           h x y r =
            (h'' y x r) ◁
            {!!}
            ▷ sym (h'' x y r)

       -- FM.Rec.f squash/
       --    []/ _∷/_
       --    λ _ _ → SQ.elimProp (λ _ → squash/ _ _)
       --      λ _ → eq/ _ _ (swapHead ,
       --         λ { zero → refl ; one → refl ; (suc (suc k)) → refl})

      w : Iso (List//↔ A) (FMSet2 A)
      Iso.fun w = toFM
      Iso.inv w = fromFM
      Iso.rightInv w =
        FM2.ElimSet.f
          refl
          (λ x {xs} p → {!!} ∙ cong (x ∷fm2_) p)
          {!!}
          {!!}
          λ _ →  trunc _ _
        -- FM.ElimProp.f (trunc _ _) refl
        --   λ a {xs} →
        --     ((SQ.elimProp {P = λ x → toFM (a ∷/ x) ≡ _ ∷fm toFM x}
        --          (λ _ → trunc _ _) (λ _ → refl) ∘ fromFM) xs ∙_) ∘ cong (_ ∷fm_)

      Iso.leftInv w =
        GQ.elimSet
          _
          (λ _ → squash// _ _)
          (ind refl (cong (_ ∷//_)))
          {!!} 
       -- SQ.elimProp (λ x → squash/ _ _) (ind refl (cong (_ ∷/_)))
