{-# OPTIONS  --safe --experimental-lossy-unification  #-}
module Cubical.Data.List.FinDataSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

open import Cubical.Data.List renaming (map to mapList)
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
  A B : Type ℓ

-- copy-paste from agda-stdlib
lookup : ∀ (xs : List A) → Fin (length xs) → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

lookup-map : ∀ (f : A → B) (xs : List A)
  → (p0 : Fin (length (mapList f xs)))
  → (p1 : Fin (length xs))
  → (p : PathP (λ i → Fin (length-map f xs i)) p0 p1)
  → lookup (mapList f xs) p0 ≡ f (lookup xs p1)
lookup-map f (x ∷ xs) zero zero p = refl
lookup-map f (x ∷ xs) zero (suc p1) p = ⊥.rec (znotsP p)
lookup-map f (x ∷ xs) (suc p0) zero p = ⊥.rec (snotzP p)
lookup-map f (x ∷ xs) (suc p0) (suc p1) p = lookup-map f xs p0 p1 (injSucFinP p)

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
length-permute _ _ = length-tabulate _ _

tabulate∘ : ∀ {n m} → (e : Fin n → A)
               (g : Fin m → Fin n)  →
                tabulate m (lookup (tabulate n e)
                  ∘ subst⁻ Fin (length-tabulate _ _) ∘ g)  ≡
                  tabulate m (e ∘ g)
tabulate∘ {m = zero} _ _ = refl
tabulate∘ {m = suc _} e _ =
  cong₂ _∷_
    ( congP (λ i → lookup-tabulate _ e i)
     (toPathP (transportTransport⁻ (cong Fin _) _)))
    (tabulate∘ e _)

lookup-swap : ∀ (x y : A) (l : List A) → ∀ k →
               lookup (x ∷ y ∷ l) k
                ≡
               lookup (y ∷ x ∷ l) (swap0and1 k)
lookup-swap x y l zero = refl
lookup-swap x y l one = refl
lookup-swap x y l (suc (suc k)) = refl



infix 4  _↔_

record _↔_ {ℓ} {A : Type ℓ} (x y : List A) : Type ℓ where
  constructor prm
  field
    F≃ : (Fin (length x) ≃ Fin (length y))
    l≡ : ∀ k → lookup x k ≡ lookup y (equivFun F≃ k)

open _↔_

↔permute : ∀ {n} (l : List A) → (e : Fin n ≃ Fin (length l))
                → l ↔ (permute l e)
F≃ (↔permute l e) = invEquiv e ∙ₑ ≡→Fin≃ (sym (length-permute l e))
l≡ (↔permute l e) k =
        cong (lookup l) (sym (secEq e k))
      ∙ sym (lookup-tabulateT _ (lookup l ∘ (fst e)) (invEq e k))


isRefl↔ : BinaryRelation.isRefl (_↔_ {A = A})
F≃ (isRefl↔ a) = idEquiv _
l≡ (isRefl↔ a) _ = refl

isSym↔ : BinaryRelation.isSym (_↔_ {A = A})
F≃ (isSym↔ _ b (prm e p)) = invEquiv e
l≡ (isSym↔ _ b (prm e p)) k = cong (lookup b) (sym (secEq e _)) ∙ sym (p _)

sym↔ : {a b : List A} → a ↔ b → b ↔ a
sym↔ = isSym↔ _ _

isTrans↔ : BinaryRelation.isTrans (_↔_ {A = A})
F≃ (isTrans↔ a b c (prm e p) (prm f q)) = e ∙ₑ f
l≡ (isTrans↔ a b c (prm e p) (prm f q)) _ = p _ ∙ q _

-- Some helpful notation:

_∙↔_ : {a b c : List A} → a ↔ b → b ↔ c → a ↔ c
_∙↔_ {a = a} {b} {c} = isTrans↔ a b c

infixr 30 _∙↔_

_↔⟨_⟩_ : ∀ a → {b c : List A} → a ↔ b → b ↔ c → a ↔ c
_↔⟨_⟩_ a {b} {c} = isTrans↔ a b c

_■↔ : (a : List A) → (a ↔ a)
_■↔ = isRefl↔

infixr  0 _↔⟨_⟩_
infix   1 _■↔


isEquivRel↔ : BinaryRelation.isEquivRel {ℓ = ℓ} {A = List A} _↔_
isEquivRel↔ = BinaryRelation.equivRel isRefl↔ isSym↔ isTrans↔

comp↔Refl : ∀ {a : List A} → isRefl↔ a ≡ isRefl↔ a ∙↔ isRefl↔ a
comp↔Refl = cong₂ prm (equivEq refl) (funExt λ _ → compPathRefl)


↔→length≡ : ∀ {x y : List A} →  x ↔ y → length x ≡ length y
↔→length≡ = isInjectiveFin≃ ∘ F≃

¬nil↔cons : ∀ {x : A} {xs} → ¬ ([] ↔ x ∷ xs)
¬nil↔cons = ℕznots ∘ ↔→length≡ {x = []}

¬cons↔nil : ∀ {x : A} {xs} → ¬ (x ∷ xs ↔ [])
¬cons↔nil = ℕsnotz ∘ ↔→length≡ {y = []}

_∷↔_ : ∀ (a : A) {xs ys} → xs ↔ ys → a ∷ xs ↔ a ∷ ys
a ∷↔ (prm e p) = prm (sucPerm e)  λ { zero → refl ; (suc _) → p _}

≡→↔ : ∀ {xs ys : List A} → xs ≡ ys → xs ↔ ys
≡→↔ {xs = xs} p = prm (≡→Fin≃ (cong length p)) λ _ → cong₂ lookup p (toPathP refl) 


headSwap↔ : {x y : A} → ∀ {l} → x ∷ y ∷ l ↔ y ∷ x ∷ l
headSwap↔ =
  prm swap0and1≃ λ { zero → refl ; one → refl ; (suc (suc k)) → refl }


_∷↔∷ʳ_ : ∀ xs → (x : A) → xs ∷ʳ x ↔ x ∷ xs
_∷↔∷ʳ_ =
  ind (isRefl↔ ∘ [_])
        λ x _ → ≡→↔ (++-assoc [ _ ] _ [ _ ])
          ∙↔ (_ ∷↔ x _)
          ∙↔ headSwap↔

_↔∷ʳ_ : ∀ {xs ys} → xs ↔ ys → ∀ (a : A) → xs ∷ʳ a ↔ ys ∷ʳ a
r ↔∷ʳ _ = (_ ∷↔∷ʳ _) ∙↔ (_ ∷↔ r) ∙↔ sym↔ (_ ∷↔∷ʳ _)


_++↔_ : (x y : List A) → x ++ y ↔ y ++ x
x ++↔ [] = ≡→↔ (++-unit-r x)
[] ++↔ y@(_ ∷ _) = ≡→↔ (sym (++-unit-r y) )
(x ∷ xs) ++↔ (y ∷ ys) =
       (x ∷↔ ((xs ++↔ (y ∷ ys))))
    ∙↔ headSwap↔
    ∙↔ (y ∷↔ (cong↔++R (sym↔ (ys ∷↔∷ʳ x)) xs)
              ∙↔ (≡→↔ (++-assoc ys [ x ] xs)))
  where

  lookup-FinSumChar : ∀ {xs ys : List A} →
          ∀ k → lookup (xs ++ ys) k ≡
           ⊎.rec (lookup xs) (lookup ys)
             (FinSumChar.inv (length xs) (length ys)
               (subst Fin (length++ xs ys) k))
  lookup-FinSumChar {xs = []} {ys} _ = cong (lookup ys) (sym (transportRefl _))
  lookup-FinSumChar {xs = x ∷ xs} {ys} zero =
     cong (⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘ (FinSumChar.inv _ _))
       (transportFin-zero _)
  lookup-FinSumChar {xs = x ∷ xs} {ys} (suc _) =
     _ ≡⟨ lookup-FinSumChar {xs = xs} _ ⟩
     _ ≡⟨ h (FinSumChar.inv _ _ _) ⟩
     _ ≡⟨ cong (⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘ FinSumChar.inv _ _)
             (sym (transportFin-suc (length++ xs ys) _ _)) ⟩ _ ∎

    where
      h : ∀ z → ⊎.rec _ _ z ≡ ⊎.rec (lookup (x ∷ xs)) _ (FinSumChar.invSucAux _ _ z)
      h (inl _) = refl
      h (inr _) = refl

  cong↔++R : {xs ys : List A} → xs ↔ ys → ∀ l → xs ++ l ↔ ys ++ l
  cong↔++R {xs = xs} {ys} (prm e p) _ =
   let h = ⊎-equiv e (idEquiv _)
   in prm (≡→Fin≃ _ ∙ₑ invEquiv (FinSumChar.Equiv _ _) ∙ₑ h ∙ₑ FinSumChar.Equiv _ _  ∙ₑ ≡→Fin≃ _)
    λ _ →
     let k' = FinSumChar.inv _ _ _
     in _ ≡⟨ lookup-FinSumChar {xs = xs} _ ⟩
        _ ≡⟨ cong (λ g → ⊎.rec g _ k') (funExt p) ⟩
        _ ≡⟨ recMap k' ⟩
        _ ≡⟨ cong (⊎.rec _ _)
             ( _ ≡⟨ ⊎.elim {C = (λ y → ⊎.mapl _ y ≡ equivFun h y)} (λ _ → refl) (λ _ → refl) k' ⟩
               _ ≡⟨ sym (FinSumChar.ret _ _ _) ⟩
               _ ≡⟨ cong (FinSumChar.inv _ _)
                    (sym (transportTransport⁻ (cong Fin _) _)) ⟩ _ ∎ ) ⟩
        _ ≡⟨ sym (lookup-FinSumChar {xs = ys} _) ⟩ _ ∎


rev↔ : (xs : List A) → xs ↔ rev xs
rev↔ [] = isRefl↔ []
rev↔ (x ∷ xs) = (x ∷↔ rev↔ xs) ∙↔ (sym↔ ((rev xs) ∷↔∷ʳ x))

List/↔ : (A : Type ℓ) → Type ℓ
List/↔ A =  List A / _↔_

pattern []/ = [ [] ]/

_∷/_ : A → List/↔ A → List/↔ A
_∷/_ {A = A} a = SQ.rec squash/ ([_]/ ∘ (a ∷_))
            λ _ _ r → eq/ _ _ (prm (sucPerm (F≃ r))
              λ { zero → refl ; (suc _) → l≡ r _})


List→FMSet : List A → FMSet A
List→FMSet {A = A} = foldr {B = FMSet A} _∷fm_ []fm


PunchHeadInOut/≡ : (l : List A) → ∀ k
  → List→FMSet l ≡ List→FMSet (permute l (PunchHeadInOut≃ k))
PunchHeadInOut/≡ (x ∷ l) zero =
  cong List→FMSet (sym (tabulate-lookup (x ∷ l)))
PunchHeadInOut/≡ (x ∷ x₁ ∷ l) one i =
  comm x x₁ (List→FMSet (tabulate-lookup l (~ i))) i
PunchHeadInOut/≡ (x ∷ x₁ ∷ l) (suc (suc k)) =
  cong (x ∷fm_) (PunchHeadInOut/≡ (x₁ ∷ l) (suc k)) ∙ comm _ _ _


PunchHeadInOut/≡⁻ : ∀ (x : A) (l : List A) → ∀ k
      → List→FMSet (x ∷ l) ≡
         List→FMSet (permute (x ∷ l) (invEquiv (PunchHeadInOut≃ k)))

PunchHeadInOut/≡⁻ x l zero = cong (List→FMSet ∘ (x ∷_))  (sym (tabulate-lookup l))
PunchHeadInOut/≡⁻ x (x₁ ∷ l) one i =
  comm x x₁ (List→FMSet ((tabulate-lookup l) (~ i))) i
PunchHeadInOut/≡⁻ x (x₁ ∷ l) (suc (suc k)) =
  _ ≡⟨ comm _ _ _ ⟩
  _ ≡⟨ cong (x₁ ∷fm_) (PunchHeadInOut/≡⁻ x l (suc k)) ⟩
  _ ≡⟨ cong ((x₁ ∷fm_) ∘ List→FMSet ∘ tabulate (suc _))
       (funExt (lookup-swap x₁ x l ∘
          suc ∘ equivFun (invEquiv (PunchHeadInOut≃ (suc k))))) ⟩
  _ ∎

↔→FMSet≡ : (a b : List A) → a ↔ b → List→FMSet a ≡ List→FMSet b
↔→FMSet≡ [] [] _ = refl
↔→FMSet≡ [] (_ ∷ _) = ⊥.rec ∘ ¬nil↔cons
↔→FMSet≡ (_ ∷ _) [] = ⊥.rec ∘ ¬cons↔nil
↔→FMSet≡ {A = A} (x ∷ xs) (y ∷ ys) r@(prm e _) =
   let (e' , p') = unwindPermHead e
       k' = equivFun e zero
       xs' = permute xs (invEquiv e')
       (prm _ p⁻) = isSym↔ _ _ r
       pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))
   in
      _ ≡⟨ cong (x ∷fm_) (↔→FMSet≡ xs xs' (↔permute xs (invEquiv e'))) ⟩
      _ ≡⟨ PunchHeadInOut/≡⁻ x xs' (subst Fin pL k') ⟩
      _ ≡⟨ cong List→FMSet
          (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'))
                    (PunchHeadInOut≃∙ₑ≡→Fin≃ pL k')) ⟩
           _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'))
                           (invEq (PunchHeadInOut≃ k'))  ⟩
           _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p') ⟩
           _ ≡⟨ cong (tabulate _) (sym (funExt p⁻)) ⟩
           _ ≡⟨ tabulate-lookup _ ⟩ (y ∷ ys) ∎
          ) ⟩ _ ∎


-- factor↔ : (a b : List A) → (r : a ↔ b) →
--             r ≡ ≡→↔ (sym (tabulate-lookup a) ∙ cong (tabulate (length a)) (funExt (l≡ r)))
--                    ∙↔ sym↔ (↔permute b (F≃ r)) 
-- factor↔ a b r =
--    cong₂ prm
--      (equivEq (cong ((F≃ r .fst) ∘_) (sym (funExt (isSet-subst {B = Fin} isSetℕ _))
--             ∙ funExt (substComposite Fin _ _))))
--      ({!!})

-- factor↔Σ : (a b : List A) → (r : a ↔ b) →
--             Σ[ p ∈ a ≡ permute b (F≃ r) ]
--               r ≡ ≡→↔ p  ∙↔ sym↔ (↔permute b (F≃ r)) 
-- factor↔Σ a b r = {!!}

module _ (isSetA : isSet A) where

  isSetLA = isOfHLevelList zero isSetA
  -- isSetLA = isOfHLevelList zero isSetA

  prmEq : {a b : List A} → (r r' : a ↔ b) →
          F≃ r ≡ F≃ r' → r ≡ r'
  prmEq r r' p =
    cong₂ prm p (isProp→PathP (λ i → isPropΠ λ _ → isSetA _ _) (l≡ r) (l≡ r'))
    
  factor↔Σ' : (a b : List A) → (r : a ↔ b) →
              Σ[ p ∈ permute a (invEquiv (F≃ r)) ≡ b ]
                r ≡ ↔permute a (invEquiv (F≃ r)) ∙↔ ≡→↔ p 
  fst (factor↔Σ' a b r) = cong (tabulate (length b)) (funExt (l≡ r ∘ invEq (F≃ r)))
                               ∙ cong ((tabulate (length b)) ∘ ((lookup b) ∘_))
                                (funExt (secEq (F≃ r)) ) ∙ tabulate-lookup b
  snd (factor↔Σ' a b r@(prm e p)) =
    prmEq _ _ ((equivEq (funExt λ x → sym (isSet-subst {B = Fin} isSetℕ _ ((fst (F≃ r) x)))
       ∙ substComposite Fin _ _ (fst (F≃ r) x)))) 
     

  -- IsoList/↔FMSet : Iso (List/↔ A) (FMSet A)
  -- IsoList/↔FMSet = w
  --   where

  --     toFM = SQ.rec trunc List→FMSet ↔→FMSet≡

  --     fromFM = FM.Rec.f squash/
  --         []/ _∷/_
  --         λ _ _ → SQ.elimProp (λ _ → squash/ _ _)
  --           λ _ → eq/ _ _ (prm swap0and1≃
  --              λ { zero → refl ; one → refl ; (suc (suc k)) → refl})

  --     w : Iso _ _
  --     Iso.fun w = toFM
  --     Iso.inv w = fromFM
  --     Iso.rightInv w =
  --       FM.ElimProp.f (trunc _ _) refl
  --         λ a {xs} →
  --           ((SQ.elimProp {P = λ x → toFM (a ∷/ x) ≡ _ ∷fm toFM x}
  --               (λ _ → trunc _ _)
  --               (λ _ → refl) ∘ fromFM) xs ∙_)
  --            ∘ cong (_ ∷fm_)

  --     Iso.leftInv w =
  --       SQ.elimProp
  --         (λ x → squash/ _ _)
  --         (ind refl (cong (_ ∷/_)))


  -- List/↔≃FreeComMonoid : List/↔ A ≃ FreeComMonoid A
  -- List/↔≃FreeComMonoid =
  --       isoToEquiv IsoList/↔FMSet
  --    ∙ₑ FMSet≃AssocList
  --    ∙ₑ AssocList≃FreeComMonoid



  List//↔ : (A : Type ℓ) → Type ℓ
  List//↔ A =  List A // isTrans↔

  _∷//_ : A → List//↔ A → List//↔ A
  _∷//_  = λ a → GQ.rec isTrans↔ squash// ([_]// ∘ (a ∷_))
            (λ {x} {y} r → eq// (prm (sucPerm (F≃ r)) (w {x = x} {y} {r} a) ))
             λ r s →
               comp// (prm (sucPerm (F≃ r)) (w a)) (prm (sucPerm (F≃ s)) (w a) ) ▷
                    cong eq//
                      (cong₂ prm
                          (equivEq (funExt (λ { zero → refl ; (suc _) → refl })))
                          (funExt (λ { zero → sym compPathRefl ; (suc _) → refl })))
    where
      w : {x y : List A} → {r : x ↔ y } → ∀ a _ → _
      w _ zero = refl
      w {r = r} _ (suc _) = l≡ r _

  length// : List//↔ A → ℕ
  length// = GQ.elimSet isTrans↔ (λ _ → isSetℕ) length ↔→length≡


  -- -- -- funExt∙ : ∀ {ℓ'} {B C : Type ℓ'} {f g h : B → A}
  -- -- --             → (p : ∀ k → f k ≡ g k) → (q : ∀ k → g k ≡ h k)
  -- -- --             → funExt (λ k → p k ∙ q k ) ≡ funExt p ∙ funExt q
  -- -- -- funExt∙ p q = refl


  module FC2M where
    open import Cubical.HITs.FiniteMultiset.Base2 as FM2
         renaming (_∷_ to _∷fm2_ ; [] to []fm2 ; _++_ to _++fm2_) hiding ([_])

    List→FMSet2 : List A → FMSet2 A
    List→FMSet2 = foldr {B = FMSet2 A} _∷fm2_ []fm2



    PunchHeadInOut//≡ : (l : List A) → ∀ k
      → List→FMSet2 l ≡ List→FMSet2 (permute l (PunchHeadInOut≃ k))
    PunchHeadInOut//≡ (x ∷ l) zero =
      cong List→FMSet2 (sym (tabulate-lookup (x ∷ l)))
    PunchHeadInOut//≡ (x ∷ x₁ ∷ l) one i =
      comm x x₁ (List→FMSet2 (tabulate-lookup l (~ i))) i
    PunchHeadInOut//≡ (x ∷ x₁ ∷ l) (suc (suc k)) =
      cong (x ∷fm2_) (PunchHeadInOut//≡ (x₁ ∷ l) (suc k)) ∙ comm _ _ _


    PunchHeadInOut//≡⁻ : ∀ (x : A) (l : List A) → ∀ k
          → List→FMSet2 (x ∷ l) ≡
             List→FMSet2 (permute (x ∷ l) (invEquiv (PunchHeadInOut≃ k)))
    PunchHeadInOut//≡⁻ x l zero = cong (List→FMSet2 ∘ (x ∷_))  (sym (tabulate-lookup l))
    PunchHeadInOut//≡⁻ x (x₁ ∷ l) one i =
      comm x x₁ (List→FMSet2 ((tabulate-lookup l) (~ i))) i
    PunchHeadInOut//≡⁻ x (x₁ ∷ l) (suc (suc k)) =
      _ ≡⟨ comm _ _ _ ⟩
      _ ≡⟨ cong (x₁ ∷fm2_) (PunchHeadInOut//≡⁻ x l (suc k)) ⟩
      _ ≡⟨ cong ((x₁ ∷fm2_) ∘ List→FMSet2 ∘ tabulate (suc _))
           (funExt (lookup-swap x₁ x l ∘
              suc ∘ equivFun (invEquiv (PunchHeadInOut≃ (suc k))))) ⟩
      _ ∎


    ↔→FMSet2≡Refl : (a : List A) → Path (Path (List//↔ A) _ _)
                                     (eq// (isRefl↔ a))
                                     refl  
    ↔→FMSet2≡Refl a =
      ∙²≡id→≡refl (sym (cong eq// comp↔Refl 
            ∙ comp'// _ isTrans↔ (isRefl↔ a) (isRefl↔ a)))

    len2 : FMSet2 A → ℕ
    len2 = RecSet.f
      isSetℕ 0 (λ _ → suc) (λ _ _ _ → refl) λ _ _ _ _ → refl

    permute→FMSet2≡EQ : (x : A) → (xs : List A) → ∀ n
         → (e : Fin (suc n) ≃ Fin (length (x ∷ xs))) → _ 
    permute→FMSet2≡EQ x xs n eP =
     let r@(prm e _) = ↔permute (x ∷ xs) eP       
         (e' , p') = unwindPermHead e
         k' = equivFun e zero
         xs' = permute xs (invEquiv e')
         (prm _ p⁻) = isSym↔ _ _ r
         pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))

     in      _ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'))
                      (PunchHeadInOut≃∙ₑ≡→Fin≃ pL k')) ⟩
             _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'))
                             (invEq (PunchHeadInOut≃ k'))  ⟩
             _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p') ⟩
             _ ≡⟨ cong (tabulate _) (sym (funExt p⁻)) ⟩
             _ ≡⟨ tabulate-lookup _ ⟩ (permute (x ∷ xs) eP) ∎

    permute→FMSet2≡↔ : (x : A) → (xs : List A) → ∀ n
         → (e : Fin (suc n) ≃ Fin (length (x ∷ xs)))
          → List→FMSet2 (x ∷ xs) ≡
              List→FMSet2 (permute (x ∷ permute xs _) (invEquiv (PunchHeadInOut≃ _))) 


    permute→FMSet2≡ : (xs : List A) → ∀ {n} → (e : Fin n ≃ Fin (length xs))
         → List→FMSet2 xs ≡ List→FMSet2 (permute xs e)
    permute→FMSet2≡ [] {zero} e = refl
    permute→FMSet2≡ [] {suc n} e = ⊥.rec (¬Fin0 (fst e zero))
    permute→FMSet2≡ (x ∷ xs) {zero} e = ⊥.rec (¬Fin0 (invEq e zero))
    permute→FMSet2≡ (x ∷ xs) {suc n} eP =
     let r@(prm e _) = ↔permute (x ∷ xs) eP       
         (e' , p') = unwindPermHead e
         k' = equivFun e zero
         xs' = permute xs (invEquiv e')
         (prm _ p⁻) = isSym↔ _ _ r
         pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))

     in permute→FMSet2≡↔ x xs n eP
        ∙ (cong List→FMSet2 (permute→FMSet2≡EQ x xs n eP))

    permute→FMSet2≡↔ x xs n eP =
     let r@(prm e _) = ↔permute (x ∷ xs) eP       
         (e' , p') = unwindPermHead e
         k' = equivFun e zero
         xs' = permute xs (invEquiv e')
         (prm _ p⁻) = isSym↔ _ _ r
         pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))

     in (cong (x ∷fm2_) (permute→FMSet2≡ xs (invEquiv e'))
             ∙ PunchHeadInOut//≡⁻ x xs' (subst Fin pL k') )


    ↔→FMSet2≡COMM : ∀ n → (a b : List A) → (p : a ≡ b) → _
    ↔→FMSet2≡COMM n a b =
       J (λ b p → (r : Fin n ≃ Fin (length b)) →
                       Σ[ r' ∈  Fin n ≃ Fin (length a) ]
                       Σ[ p' ∈ permute a r' ≡ permute b r ] 
                       cong List→FMSet2 p ∙ permute→FMSet2≡ b r ≡
                       permute→FMSet2≡ a r' ∙ cong List→FMSet2 p')
                        w         
      where
        w : _
        fst (w r) = r
        fst (snd (w r)) = refl
        snd (snd (w r)) = sym (lUnit _) ∙ rUnit _



    ↔→FMSet2≡ : (a b : List A) → a ↔ b → List→FMSet2 a ≡ List→FMSet2 b
    ↔→FMSet2≡ xs _ r =
       let r' = factor↔Σ' _ _ r
       in permute→FMSet2≡ xs (invEquiv (F≃ r)) ∙ cong List→FMSet2 (fst r')


    -- ↔→FMSet≡2Trans : (a b c : List A) → (p : a ↔ b) → (q : b ↔ c)
    --                   → ↔→FMSet2≡ a b p ∙ ↔→FMSet2≡ b c q ≡
    --                     ↔→FMSet2≡ a c (isTrans↔ a b c p q)
    -- ↔→FMSet≡2Trans a b c p q =
    --    let p' = factor↔Σ' _ _ p
    --        q' = factor↔Σ' _ _ q
    --        pq' = factor↔Σ' _ _ (p ∙↔ q)
    --        (r* , p* , P) =
    --          ↔→FMSet2≡COMM (length c) (permute a (invEquiv (F≃ p))) b (fst p') (invEquiv (F≃ q))

    --    in sym (assoc _ _ _) ∙
    --        cong ((λ i → permute→FMSet2≡ a (invEquiv (F≃ p)) i) ∙_)
    --          ((assoc _ _ _) ∙
    --             cong  
    --                (_∙ (cong List→FMSet2 (fst q'))) P
    --           ∙ sym (assoc _ _ _) )
    --           ∙
    --           assoc _ _ _
    --           ∙ cong₂ _∙_ refl
    --              (sym (cong-∙ {x = permute (permute a (invEquiv (F≃ p))) r*} List→FMSet2 p* (fst q')))
    --           ∙ (_∙_ {y = List→FMSet2 (permute (permute a (invEquiv (F≃ p))) r*)} _ _
    --                ≡⟨ {!!} ⟩
    --              ( _∙_ {y = List→FMSet2 (permute a ((invEquiv (F≃ p ∙ₑ F≃ q))))}
    --                (λ i → permute→FMSet2≡ a (invEquiv (F≃ (isTrans↔ a b c p q))) i)
    --               (cong List→FMSet2 (fst pq'))) ∎ ) 

  -- ↔→FMSet≡2TransEqLem : ∀ n m → (x : A) (xs : List A) → (e : {!!}) → (f : {!!})
  --                        → {!!}
  -- ↔→FMSet≡2TransEqLem = {!!}


    ↔→FMSet≡2Trans : (a b c : List A) → (p : a ↔ b) → (q : b ↔ c)
                      → ↔→FMSet2≡ a b p ∙ ↔→FMSet2≡ b c q ≡
                        ↔→FMSet2≡ a c (isTrans↔ a b c p q)
    ↔→FMSet≡2Trans [] [] [] _ _ = cong₂ _∙_ (sym compPathRefl) (sym compPathRefl)
    ↔→FMSet≡2Trans [] [] (_ ∷ _) _ q = ⊥.rec (¬nil↔cons q)
    ↔→FMSet≡2Trans [] (_ ∷ _) _ p _ = ⊥.rec (¬nil↔cons p)
    ↔→FMSet≡2Trans (_ ∷ _) [] _ p _ = ⊥.rec (¬cons↔nil p)
    ↔→FMSet≡2Trans (_ ∷ _) (_ ∷ _) [] _ q = ⊥.rec (¬cons↔nil q)
    ↔→FMSet≡2Trans a@(x ∷ xs) b@(y ∷ ys) c@(z ∷ zs) p q = 
           

           --      -- ((p↔ ∙ (permute→FMSet2≡ a' ↔*)) ∙ ((cong List→FMSet2 (p* ∙ (fst q')))))
           --      --  ≡⟨ {!!} ⟩
           --      -- (permute→FMSet2≡ a (invEquiv (F≃ p ∙ₑ F≃ q)) ∙ cong List→FMSet2 (fst pq')) ∎
 

         (LL ∙ RR)
           ∙ cong ((permute→FMSet2≡↔ x xs (length zs) (invEquiv (F≃ p ∙ₑ F≃ q))) ∙_)
                  (cong-∙ {x = aaR}
                    List→FMSet2 (permute→FMSet2≡EQ x xs (length zs) (invEquiv (F≃ p ∙ₑ F≃ q))) (fst pq')) 
           ∙ assoc _ _ _
        where

           p' = factor↔Σ' _ _ p
           p= = permute→FMSet2≡EQ x xs (length ys) (invEquiv (F≃ p))
           p↔ = permute→FMSet2≡↔ x xs (length ys) (invEquiv (F≃ p))

           e' = (fst (unwindPermHead (F≃ (↔permute a (invEquiv (F≃ p))))) )

           q' = factor↔Σ' _ _ q
           q= = permute→FMSet2≡EQ y ys (length zs) (invEquiv (F≃ q))
           q↔ = permute→FMSet2≡↔ y ys (length zs) (invEquiv (F≃ q))
           a' = permute (x ∷ permute xs _) _
           
           zzz = ↔→FMSet2≡COMM _ a' _ (p= ∙ fst p') (invEquiv (F≃ q))
           ↔* = fst zzz
           p* = fst (snd zzz)
           P = snd (snd zzz)
           pq' = factor↔Σ' _ _ (p ∙↔ q) 
        

           LL : ((p↔ ∙ cong List→FMSet2 p=) ∙ cong List→FMSet2 (fst p'))
                  ∙ (↔→FMSet2≡ b c q) ≡
                    ((p↔ ∙ (permute→FMSet2≡ a' ↔*)) ∙ ((cong List→FMSet2 (p* ∙ (fst q')))))
           LL = _ ≡⟨ cong (_∙ (↔→FMSet2≡ b c q))
                       (sym (assoc p↔ (cong List→FMSet2 p=) (cong List→FMSet2 (fst p')))
                         ∙ cong (p↔ ∙_) (sym (cong-∙ List→FMSet2 p= (fst p'))))
                       -- (sym (assoc q↔ (cong List→FMSet2 q=) (cong List→FMSet2 (fst q')))
                       --   ∙ cong (q↔ ∙_) (sym (cong-∙ List→FMSet2 q= (fst q'))))
                         ⟩
               _ ≡⟨ sym (assoc p↔ _ (↔→FMSet2≡ b c q)) ⟩
               _ ≡⟨ (cong (p↔ ∙_)
                  ((assoc _ _ ((cong List→FMSet2 (fst q'))))
                    ∙ cong (_∙ (cong List→FMSet2 (fst q'))) P ∙ sym (assoc _ _ _))) ∙
                      (assoc p↔ (permute→FMSet2≡ a' ↔*) ((cong List→FMSet2 p*) ∙ (cong List→FMSet2 (fst q')))) ⟩
               _ ≡⟨⟩ cong ((p↔ ∙ (permute→FMSet2≡ a' ↔*)) ∙_) (sym (cong-∙ List→FMSet2 p* (fst q'))) 
          

           aaL = permute  (permute (x ∷ permute xs _) _) ↔*
           aaR = permute (x ∷ permute xs _) _

           aa= : aaL ≡ aaR
           aa= = {!!}

           sqMain : Square
                       (p↔ ∙ (permute→FMSet2≡ a' ↔*))
                       (permute→FMSet2≡↔ x xs (length zs) (invEquiv (F≃ p ∙ₑ F≃ q)))
                       refl
                       (cong List→FMSet2 aa=)
           sqMain = {!!}


           RR : _ ≡ _
                --  ( _∙_ {y = List→FMSet2 aaL}
                --     (p↔ ∙ (permute→FMSet2≡ a' ↔*)) ((cong List→FMSet2 (p* ∙ (fst q'))))) ≡
                -- (_∙_ {y = List→FMSet2 aaR}
                --      (permute→FMSet2≡ a (invEquiv (F≃ p ∙ₑ F≃ q))) (cong List→FMSet2 (fst pq')))
                --        -- ↔→FMSet2≡ a c (isTrans↔ a b c p q)
           RR = λ i → _∙_ {x = List→FMSet2 a} {y = List→FMSet2 (aa= i)} {z = List→FMSet2 c}
                     (sqMain i)
                     λ j → List→FMSet2
                             (isSet→isSet' (isSetLA)
                                (p* ∙ (fst q'))
                                ((permute→FMSet2≡EQ x xs (length zs) (invEquiv (F≃ p ∙ₑ F≃ q))) ∙ fst pq')
                                aa= refl i j )






        --LL ∙ RR
         -- ((p↔ ∙ cong List→FMSet2 p=) ∙ cong List→FMSet2 (fst p'))
         --     ∙ (↔→FMSet2≡ b c q)
         --        --((q↔ ∙ cong List→FMSet2 q=) ∙ cong List→FMSet2 (fst q'))
         --    ≡⟨ cong (_∙ (↔→FMSet2≡ b c q))
         --          (sym (assoc p↔ (cong List→FMSet2 p=) (cong List→FMSet2 (fst p')))
         --            ∙ cong (p↔ ∙_) (sym (cong-∙ List→FMSet2 p= (fst p'))))
         --          -- (sym (assoc q↔ (cong List→FMSet2 q=) (cong List→FMSet2 (fst q')))
         --          --   ∙ cong (q↔ ∙_) (sym (cong-∙ List→FMSet2 q= (fst q'))))
         --            ⟩
         --  _ ≡⟨ sym (assoc p↔ _ (↔→FMSet2≡ b c q)) ⟩
         --  _ ≡⟨ (cong (p↔ ∙_)
         --     ((assoc _ _ ((cong List→FMSet2 (fst q'))))
         --       ∙ cong (_∙ (cong List→FMSet2 (fst q'))) P ∙ sym (assoc _ _ _))) ∙
         --         (assoc p↔ (permute→FMSet2≡ a' ↔*) ((cong List→FMSet2 p*) ∙ (cong List→FMSet2 (fst q')))) ⟩
         --  -- _ ≡⟨ {!!} ⟩
         --  ((p↔ ∙ (permute→FMSet2≡ a' ↔*)) ∙ ((cong List→FMSet2 p*) ∙ (cong List→FMSet2 (fst q')))) ≡⟨ {!!} ⟩
         --    (↔→FMSet2≡ a c (isTrans↔ a b c p q)) ∎
          -- _ ≡⟨ {!!} ⟩ _
      --     -- _ ≡⟨ {!!} ⟩ _
      --     -- _ ≡⟨ {!!} ⟩ _
      --     -- _ ≡⟨ {!!} ⟩ _
      --     -- _ ≡⟨⟩ _
      -- -- cong₂ _∙_ (sym (assoc _ _ _)) (sym (assoc _ _ _))
      -- --      ∙ ?
      -- --      ∙ assoc _ _ _



         -- ((p↔ ∙ cong List→FMSet2 p=) ∙ cong List→FMSet2 (fst p'))
         --     ∙ ((q↔ ∙ cong List→FMSet2 q=) ∙ cong List→FMSet2 (fst q'))
         --    ≡⟨ cong₂ _∙_
         --          (sym (assoc p↔ (cong List→FMSet2 p=) (cong List→FMSet2 (fst p')))
         --            ∙ cong (p↔ ∙_) (sym (cong-∙ List→FMSet2 p= (fst p'))))
         --          (sym (assoc q↔ (cong List→FMSet2 q=) (cong List→FMSet2 (fst q')))
         --            ∙ cong (q↔ ∙_) (sym (cong-∙ List→FMSet2 q= (fst q')))) ⟩
         --  _ ≡⟨ sym (assoc p↔ _ _) ⟩
         --  -- _ ≡⟨ cong (p↔ ∙_)
         --  --    ((assoc _ _ ((cong List→FMSet2 (q= ∙ fst q'))))
         --  --      ∙ cong (_∙ (cong List→FMSet2 (q= ∙ fst q'))) ?) ⟩
         --  _ ≡⟨ ? ⟩
         --    (↔→FMSet2≡ a c (isTrans↔ a b c p q)) ∎
          -- _ ≡⟨ {!!} ⟩ _
      --     -- _ ≡⟨ {!!} ⟩ _
      --     -- _ ≡⟨ {!!} ⟩ _
      --     -- _ ≡⟨ {!!} ⟩ _
      --     -- _ ≡⟨⟩ _
      -- -- cong₂ _∙_ (sym (assoc _ _ _)) (sym (assoc _ _ _))
      -- --      ∙ ?
      -- --      ∙ assoc _ _ _



  --   -- step : ∀ n → Iso (Σ (List//↔ A) ((n ≡_) ∘ length//))
  --   --                        (Σ (FMSet2 A) ((n ≡_) ∘ len2))
  --   --            → Iso (Σ (List//↔ A) (((suc n) ≡_) ∘ length//))
  --   --                        (Σ (FMSet2 A) (((suc n) ≡_) ∘ len2))
  --   -- step {A = A} n prv = w
  --   --  where
  --   --   open Iso prv

  --   --   toFM : (Σ (List//↔ A) (((suc n) ≡_) ∘ length//))
  --   --            → (Σ (FMSet2 A) (((suc n) ≡_) ∘ len2))
  --   --   toFM (x , p) =
  --   --     GQ.elim {A = List A} isTrans↔ {λ x → suc n ≡ length// x → Σ (FMSet2 A) λ z → suc n ≡ len2 z} 
  --   --       (λ _ → isGroupoidΠ (λ _ → isOfHLevelΣ 3 trunc (λ z → isSet→isGroupoid (isProp→isSet (isSetℕ (suc n)
  --   --                      (len2 z))))))
  --   --        (λ { [] → ⊥.rec ∘ ℕsnotz
  --   --           ; (a ∷ xs) p → let (xs' , p') = (fun ([ xs ]// , injSuc p))
  --   --                          in (a ∷fm2 xs') , cong suc p'
  --   --                          })
  --   --        (λ { {[]} {[]} r i p → ⊥.rec (ℕsnotz p)
  --   --           ; {[]} {_ ∷ _} → ⊥.rec ∘ ¬nil↔cons 
  --   --           ; {_ ∷ _} {[]} → ⊥.rec ∘ ¬cons↔nil
  --   --           ; {x ∷ xs} {y ∷ ys} r → {!!}
  --   --           })
  --   --        {!!}
  --   --        x
  --   --       p
  --   --    -- (GQ.rec isTrans↔ trunc List→FMSet2
  --   --    --  (λ {a} {b} → {!!})
  --   --    --   (λ {a} {b} {c} _ _ →
  --   --    --     compPath-filler _ _ ▷ {!!}) x)
  --   --    --     , {!!}    



  --   --   w : Iso _ _
  --   --   Iso.fun w = toFM
  --   --   Iso.inv w = {!!}
  --   --   Iso.rightInv w = {!!}
  --   --   Iso.leftInv w = {!!}


  --   -- IsoList//↔FMSet2 : ∀ n → Iso (Σ (List//↔ A) ((n ≡_) ∘ length//))
  --   --                        (Σ (FMSet2 A) ((n ≡_) ∘ len2))
  --   -- IsoList//↔FMSet2 {A = A} n = {!!}





  --   -- ↔→FMSet2≡ : (a b : List A) → a ↔ b → List→FMSet2 a ≡ List→FMSet2 b
  --   -- ↔→FMSet2≡ [] [] _ = refl
  --   -- ↔→FMSet2≡ [] (_ ∷ _) = ⊥.rec ∘ ¬nil↔cons
  --   -- ↔→FMSet2≡ (_ ∷ _) [] = ⊥.rec ∘ ¬cons↔nil
  --   -- ↔→FMSet2≡ {A = A} (x ∷ xs) (y ∷ ys) r@(prm e _) =
  --   --    let (e' , p') = unwindPermHead e
  --   --        k' = equivFun e zero
  --   --        xs' = permute xs (invEquiv e')
  --   --        (prm _ p⁻) = isSym↔ _ _ r
  --   --        pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))
  --   --    in
  --   --       _ ≡⟨ cong (x ∷fm2_) (↔→FMSet2≡ xs xs' (↔permute xs (invEquiv e'))) ⟩
  --   --       _ ≡⟨ PunchHeadInOut//≡⁻ x xs' (subst Fin pL k') ⟩
  --   --       _ ≡⟨⟩ cong List→FMSet2
  --   --           (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'))
  --   --                     (PunchHeadInOut≃∙ₑ≡→Fin≃ pL k')) ⟩
  --   --            _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'))
  --   --                            (invEq (PunchHeadInOut≃ k'))  ⟩
  --   --            _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p') ⟩
  --   --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻)) ⟩
  --   --            _ ≡⟨⟩ tabulate-lookup (y ∷ ys))


  --   -- -- ↔→FMSet≡2TransH : (x y z : A) (xs ys zs : List A) → (p : x ∷ xs ↔ y ∷ ys) → (q : y ∷ ys ↔ z ∷ zs)
  --   -- --                   → {!!} ≡ {!!} 
  --   -- -- ↔→FMSet≡2TransH = {!!}


  --   -- {-# TERMINATING  #-}
  --   -- ↔→FMSet≡2Trans : (a b c : List A) → (p : a ↔ b) → (q : b ↔ c)
  --   --                   → ↔→FMSet2≡ a b p ∙ ↔→FMSet2≡ b c q ≡
  --   --                     ↔→FMSet2≡ a c (isTrans↔ a b c p q)
  --   -- ↔→FMSet≡2Trans [] [] [] _ _ = sym (doubleCompPath-filler refl _ _)
  --   -- ↔→FMSet≡2Trans [] [] (_ ∷ _) _ q = ⊥.rec (¬nil↔cons q)
  --   -- ↔→FMSet≡2Trans [] (_ ∷ _) _ p _ = ⊥.rec (¬nil↔cons p)
  --   -- ↔→FMSet≡2Trans (_ ∷ _) [] _ p _ = ⊥.rec (¬cons↔nil p)
  --   -- ↔→FMSet≡2Trans (_ ∷ _) (_ ∷ _) [] _ q = ⊥.rec (¬cons↔nil q)
  --   -- ↔→FMSet≡2Trans (x ∷ xs) (y ∷ ys) (z ∷ zs) r*@(prm f q) r**@(prm g w) = 
  --   --   let r@(prm e p) = isTrans↔ (x ∷ xs) (y ∷ ys) (z ∷ zs) (prm f q) (prm g w)
  --   --       (e' , p') = unwindPermHead e
  --   --       k' = equivFun e zero
  --   --       xs' = permute xs (invEquiv e')
  --   --       (prm _ p⁻) = isSym↔ _ _ r
  --   --       pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))

  --   --       LHS0 = PunchHeadInOut//≡⁻ x xs' (subst Fin pL k')
  --   --       LHS1 =  (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'))
  --   --                     (PunchHeadInOut≃∙ₑ≡→Fin≃ pL k')) ⟩
  --   --            _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'))
  --   --                            (invEq (PunchHeadInOut≃ k'))  ⟩
  --   --            _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p') ⟩
  --   --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻)) ⟩
  --   --            _ ≡⟨⟩ tabulate-lookup (z ∷ zs))


  --   --       LHS = LHS0 ∙ cong List→FMSet2 LHS1

  --   --       (e'* , p'*) = unwindPermHead f
  --   --       k'* = equivFun f zero
  --   --       xs'* = permute xs (invEquiv e'*)
  --   --       (prm _ p⁻*) = isSym↔ _ _ r*
  --   --       pL* = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e'*)))

  --   --       LHS0* = PunchHeadInOut//≡⁻ x xs'* (subst Fin pL* k'*)
  --   --       LHS1* =  (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'*))
  --   --                     (PunchHeadInOut≃∙ₑ≡→Fin≃ pL* k'*)) ⟩
  --   --            _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'*))
  --   --                            (invEq (PunchHeadInOut≃ k'*))  ⟩
  --   --            _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p'*) ⟩
  --   --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻*)) ⟩
  --   --            _ ≡⟨⟩ tabulate-lookup (y ∷ ys))
  --   --       LHS* = LHS0* ∙ cong List→FMSet2 LHS1*



  --   --       (e'** , p'**) = unwindPermHead g
  --   --       k'** = equivFun g zero
  --   --       xs'** = permute ys (invEquiv e'**)
  --   --       (prm _ p⁻**) = isSym↔ _ _ r**
  --   --       pL** = sym (length-tabulate _ (lookup (y ∷ ys) ∘ invEq (sucPerm e'**)))

  --   --       LHS0** = PunchHeadInOut//≡⁻ y xs'** (subst Fin pL** k'**)
  --   --       LHS1** =  (_ ≡⟨ sym (congP (λ _ → permute (y ∷ xs'**))
  --   --                     (PunchHeadInOut≃∙ₑ≡→Fin≃ pL** k'**)) ⟩
  --   --            _ ≡⟨ tabulate∘ (lookup (y ∷ ys) ∘ invEq (sucPerm e'**))
  --   --                            (invEq (PunchHeadInOut≃ k'**))  ⟩
  --   --            _ ≡⟨ cong (permute (y ∷ ys) ∘ invEquiv) (sym p'**) ⟩
  --   --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻**)) ⟩
  --   --            _ ≡⟨⟩ tabulate-lookup (z ∷ zs))
  --   --       LHS** = LHS0** ∙ cong List→FMSet2 LHS1**



  --   --       pp = ↔→FMSet≡2Trans xs xs'* xs' (↔permute _ (invEquiv e'*))
  --   --                 (sym↔ (↔permute xs (invEquiv e'*)) ∙↔ ↔permute xs (invEquiv e'))


  --   --       pp' : ↔→FMSet2≡ xs xs'
  --   --                (isTrans↔ xs xs'* xs' (↔permute _ (invEquiv e'*))
  --   --                 (sym↔ (↔permute xs (invEquiv e'*)) ∙↔ ↔permute xs (invEquiv e')))
  --   --              ≡
  --   --             ↔→FMSet2≡ xs xs' (↔permute xs (invEquiv e'))
  --   --       pp' = cong (↔→FMSet2≡ xs xs')
  --   --              (cong₂ prm (equivEq {!!}) {!!})

  --   --       MHS = cong (y ∷fm2_) (↔→FMSet2≡ ys xs'** (↔permute ys (invEquiv e'**)))

  --   --       zzz : _ ≡ _
  --   --       zzz = {!!}

  --   --       vvv : _ ≡ _
  --   --       vvv = cong (y ∷fm2_)  (↔→FMSet2≡ (ys) (permute ys ((invEquiv (fst (unwindPermHead (g))))))
  --   --               (↔permute ys (invEquiv (fst (unwindPermHead g))))) ∙
  --   --             ↔→FMSet2≡ ((y ∷ permute ys ((invEquiv (fst (unwindPermHead (g)))))))
  --   --                        (x ∷ permute xs ((invEquiv (fst (unwindPermHead (f ∙ₑ g))))))
  --   --               {!!}

  --   --       LHS1= : (LHS1**) ≡
  --   --                zzz ∙ LHS1
  --   --       LHS1= = {!!}

  --   --       LHS0= : MHS ∙ LHS0**  ≡ vvv ∙ LHS0 ∙ cong List→FMSet2 (sym zzz) 
  --   --       LHS0= = {!!}

  --   --       LHS00 : LHS* ≡ cong (x ∷fm2_) (↔→FMSet2≡ xs'* xs' (sym↔ (↔permute xs (invEquiv e'*))
  --   --               ∙↔ ↔permute xs (invEquiv e'))) ∙ sym vvv
  --   --       LHS00 = {!!}


  --   --       -- qqH =  sym (cong-∙ (x ∷fm2_) _ _)
  --   --       --        ∙ (cong (cong (x ∷fm2_))
  --   --       --        (↔→FMSet≡2Trans _ _ _ (sym↔ (↔permute xs (invEquiv e'*))) ((↔permute xs (invEquiv e')))))

  --   --       qq : LHS* ∙ MHS ∙ LHS** ≡
  --   --             cong (x ∷fm2_) (↔→FMSet2≡ xs'* xs' (sym↔ (↔permute xs (invEquiv e'*))
  --   --               ∙↔ ↔permute xs (invEquiv e'))) ∙ LHS 
  --   --       qq = {!!}



  --   --       -- lemP : (↔→FMSet2≡ (permute xs (invEquiv (fst (unwindPermHead f))))
  --   --       --         (permute xs (invEquiv (fst (unwindPermHead (f ∙ₑ g)))))
  --   --       --         (sym↔ (↔permute xs (invEquiv (fst (unwindPermHead f)))) ∙↔
  --   --       --          ↔permute xs (invEquiv (fst (unwindPermHead (f ∙ₑ g))))))
  --   --       --          ∙ {!!}
  --   --       --          ≡ {!!}
  --   --       -- lemP = {!pp!}
  --   --       -- p0 : {!!}
  --   --       p0 = cong (cong (x ∷fm2_)) (pp ∙ pp')

  --   --   in (sym (assoc _ _ _) ∙
  --   --          (cong (cong (x ∷fm2_) (↔→FMSet2≡ xs xs'* (↔permute _ (invEquiv e'*))) ∙_)
  --   --             qq)
  --   --             ∙
  --   --             assoc _ _ _)         
  --   --        ∙ (cong (_∙ LHS) (sym (cong-∙ (x ∷fm2_) _ _) ∙ p0))

  --   --   -- sym (assoc _ _ _) ∙ {!!}
  --   --   -- sym (assoc _ _ _) ∙
  --   --   --    (cong ((cong List→FMSet2 (sym (tabulate-lookup (x ∷ xs)))) ∙_)
  --   --   --      (sym (assoc _ _ _)
  --   --   --         ∙  cong ((cong (List→FMSet2 ∘ tabulate _) (funExt p)) ∙_)
  --   --   --        {!!}
  --   --   --        ∙ assoc _ _ {!!}
  --   --   --       ∙ cong₂ _∙_ (sym (cong-∙ (List→FMSet2 ∘ tabulate _) (funExt p)
  --   --   --                         (cong (_∘ (equivFun e)) (funExt q))))
  --   --   --                       {!!}))





  --   -- IsoList//↔FMSet2 : Iso (List//↔ A) (FMSet2 A)
  --   -- IsoList//↔FMSet2 {A = A} = w
  --   --   where

  --   --     toFM : _
  --   --     toFM = GQ.rec isTrans↔ trunc List→FMSet2
  --   --       (λ {a} {b} → ↔→FMSet2≡ a b)
  --   --        λ {a} {b} {c} _ _ →
  --   --          compPath-filler _ _ ▷ ↔→FMSet≡2Trans a b c _ _     

  --   --     fromFM : _
  --   --     fromFM =
  --   --       FM2.Rec.f
  --   --        squash// [ [] ]// _∷//_
  --   --        (λ x y → GQ.elimSet _ (λ _ → squash// _ _)
  --   --            (λ _ → eq// headSwap↔) (λ {a} {b} r i j → h x y {a} {b} r j i) )
  --   --        (λ x y → GQ.elimProp _ (λ _ → squash// _ _ _ _)
  --   --               (hSym x y ))
  --   --        {!!}
  --   --        {!!}
  --   --        {!!}



  --   --        where

  --   --          h'' : ∀ x y → {a b : List A} (r : a ↔ b) →
  --   --                     (λ i → (y ∷// (x ∷// eq// {a = a} {b} r i)))
  --   --                   ≡ eq// (y ∷↔ (x ∷↔ r))
  --   --          h'' x y r =
  --   --               cong eq// (cong₂ prm refl 
  --   --               (funExt λ { zero → refl ; one → refl ; (suc (suc k)) → refl }))


  --   --          h' : ∀ x y → {a b : List A} (r : a ↔ b) → Path (Path (List//↔ A) _ _)
  --   --                  ((eq// (x ∷↔ (y ∷↔ r))) ∙ eq// headSwap↔)
  --   --                  (eq// headSwap↔ ∙ (eq// (y ∷↔ (x ∷↔ r))))
  --   --          h' x y r = sym (comp'// _ _ _ _) ∙∙
  --   --                      cong eq// (cong₂ prm
  --   --                        (equivEq (funExt λ { zero → refl ; one → refl ; (suc (suc k)) → refl }))
  --   --                        ( (funExt λ { zero → refl ; one → refl
  --   --                          ; (suc (suc k)) → sym (leftright refl _) })))
  --   --                     ∙∙  comp'// _ _ _ _ 

  --   --          h : ∀ x y → {a b : List A} (r : a ↔ b) →
  --   --                  Square
  --   --                  (λ i → (x ∷// (y ∷// eq// r i)))
  --   --                  (λ i → (y ∷// (x ∷// eq// r i)))
  --   --                  (eq// headSwap↔)
  --   --                  (eq// headSwap↔)
  --   --          h x y r =
  --   --               (h'' y x r) ◁ doubleCompPath-filler (sym (eq// headSwap↔)) _
  --   --                       (eq// headSwap↔)
  --   --              ▷ (doubleCompPath-elim (sym (eq// headSwap↔)) _ _ ∙ sym (assoc _ _ _) ∙ 
  --   --                (cong ((sym (eq// headSwap↔)) ∙_) (h' x y r) ∙ assoc _ _ _ ∙
  --   --                   cong (_∙ (eq// (y ∷↔ (x ∷↔ r)))) (lCancel (eq// headSwap↔)) ∙ sym (lUnit _))
  --   --                    ∙ sym (h'' x y r))


  --   --          hSym : ∀ x y → (a : List A) → 
  --   --                    eq// (headSwap↔ {x = x} {y = y} {a})
  --   --                      ≡ sym (eq// headSwap↔)
  --   --          hSym x y a = invEq (compr≡Equiv _ _ _)
  --   --                          ((sym (comp'// _ _ _ headSwap↔)
  --   --                ∙ cong eq// (cong₂ prm (equivEq (funExt (secEq swap0and1≃)))
  --   --                   (funExt λ { zero → sym compPathRefl
  --   --                             ; one → sym compPathRefl
  --   --                             ; (suc (suc x)) → sym compPathRefl }))
  --   --                ∙ ↔→FMSet2≡Refl _ )
  --   --             ∙ sym (lCancel _))


  --   --     h∷/ : ∀ x → {a b : List A} (r : a ↔ b) →
  --   --                 (λ i → ((x ∷// eq// {a = a} {b} r i)))
  --   --               ≡ eq// ((x ∷↔ r))
  --   --     h∷/ x r =
  --   --           cong eq// (cong₂ prm refl 
  --   --           (funExt λ { zero → refl ; (suc k) → refl }))



  --   --     lll : ∀ x xs → toFM (x ∷// xs) ≡ x ∷fm2 toFM xs
  --   --     lll x = GQ.elimSet
  --   --         isTrans↔
  --   --         (λ _ → trunc _ _)
  --   --         (λ _ → refl)
  --   --         λ r i j → ss r j i
  --   --       where
  --   --        ss : ∀ {a b : List A} → (r : a ↔ b) →
  --   --                    Path (Path (FMSet2 A) _ _)
  --   --                       (λ i → toFM (x ∷// (eq// r i)))
  --   --                       (λ i →  x ∷fm2 toFM (eq// r i))
  --   --        ss r = cong (cong toFM) (h∷/ x r) ∙ {!!}


  --   --     w : Iso (List//↔ A) (FMSet2 A)
  --   --     Iso.fun w = toFM
  --   --     Iso.inv w = fromFM
  --   --     Iso.rightInv w =
  --   --       FM2.ElimSet.f
  --   --         refl
  --   --         (λ x {xs} p → lll x (fromFM xs) ∙ cong (x ∷fm2_) p)
  --   --         {!!}
  --   --         {!!}
  --   --         λ _ →  trunc _ _
  --   --       -- FM.ElimProp.f (trunc _ _) refl
  --   --       --   λ a {xs} →
  --   --       --     ((SQ.elimProp {P = λ x → toFM (a ∷/ x) ≡ _ ∷fm toFM x}
  --   --       --          (λ _ → trunc _ _) (λ _ → refl) ∘ fromFM) xs ∙_) ∘ cong (_ ∷fm_)

  --   --     Iso.leftInv w =
  --   --       GQ.elimSet
  --   --         _
  --   --         (λ _ → squash// _ _)
  --   --         (ind refl (cong (_ ∷//_)))
  --   --         {!!} 
  --   --      -- SQ.elimProp (λ x → squash/ _ _) (ind refl (cong (_ ∷/_)))
