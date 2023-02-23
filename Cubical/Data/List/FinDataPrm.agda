{-# OPTIONS --safe #-}
module Cubical.Data.List.FinDataPrm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path


open import Cubical.Functions.Involution

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

open import Cubical.Data.List renaming (map to mapList)
open import Cubical.Data.FinData

open import Cubical.Data.Nat renaming (snotz to ℕsnotz ; znots to ℕznots)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.HITs.GroupoidQuotients as GQ renaming ([_] to [_]//)

open import Cubical.HITs.ListedFiniteSet.Base2 as FM2

open import Cubical.HITs.FiniteMultiset as FM
  renaming (_∷_ to _∷fm_ ; [] to []fm ; _++_ to _++fm_) hiding ([_])
open import Cubical.HITs.FreeComMonoids using (FreeComMonoid;AssocList≃FreeComMonoid)
open import Cubical.HITs.AssocList using (FMSet≃AssocList)


open import Cubical.Algebra.Group
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Generators
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Data.FinData.PermutationPrim as P

-- open import Cubical.HITs.ListedFiniteSet.Base2 as FM2


private
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

-- tabulate∘ : ∀ {n m} → (e : Fin n → A)
--                (g : Fin m → Fin n)  →
--                 tabulate m (lookup (tabulate n e)
--                   ∘ subst⁻ Fin (length-tabulate _ _) ∘ g)  ≡
--                   tabulate m (e ∘ g)
-- tabulate∘ {m = zero} _ _ = refl
-- tabulate∘ {m = suc _} e _ =
--   cong₂ _∷_
--     ( congP (λ i → lookup-tabulate _ e i)
--      (toPathP (transportTransport⁻ (cong Fin _) _)))
--     (tabulate∘ e _)

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

-- open _↔_

-- ↔permute : ∀ {n} (l : List A) → (e : Fin n ≃ Fin (length l))
--                 → l ↔ (permute l e)
-- F≃ (↔permute l e) = invEquiv e ∙ₑ ≡→Fin≃ (sym (length-permute l e))
-- l≡ (↔permute l e) k =
--         cong (lookup l) (sym (secEq e k))
--       ∙ sym (lookup-tabulateT _ (lookup l ∘ (fst e)) (invEq e k))


-- isRefl↔ : BinaryRelation.isRefl (_↔_ {A = A})
-- F≃ (isRefl↔ a) = idEquiv _
-- l≡ (isRefl↔ a) _ = refl

-- isSym↔ : BinaryRelation.isSym (_↔_ {A = A})
-- F≃ (isSym↔ _ b (prm e p)) = invEquiv e
-- l≡ (isSym↔ _ b (prm e p)) k = cong (lookup b) (sym (secEq e _)) ∙ sym (p _)

-- sym↔ : {a b : List A} → a ↔ b → b ↔ a
-- sym↔ = isSym↔ _ _

-- isTrans↔ : BinaryRelation.isTrans (_↔_ {A = A})
-- F≃ (isTrans↔ a b c (prm e p) (prm f q)) = e ∙ₑ f
-- l≡ (isTrans↔ a b c (prm e p) (prm f q)) _ = p _ ∙ q _

-- -- Some helpful notation:

-- _∙↔_ : {a b c : List A} → a ↔ b → b ↔ c → a ↔ c
-- _∙↔_ {a = a} {b} {c} = isTrans↔ a b c

-- infixr 30 _∙↔_

-- _↔⟨_⟩_ : ∀ a → {b c : List A} → a ↔ b → b ↔ c → a ↔ c
-- _↔⟨_⟩_ a {b} {c} = isTrans↔ a b c

-- _■↔ : (a : List A) → (a ↔ a)
-- _■↔ = isRefl↔

-- infixr  0 _↔⟨_⟩_
-- infix   1 _■↔


-- isEquivRel↔ : BinaryRelation.isEquivRel {ℓ = ℓ} {A = List A} _↔_
-- isEquivRel↔ = BinaryRelation.equivRel isRefl↔ isSym↔ isTrans↔

-- comp↔Refl : ∀ {a : List A} → isRefl↔ a ≡ isRefl↔ a ∙↔ isRefl↔ a
-- comp↔Refl = cong₂ prm (equivEq refl) (funExt λ _ → compPathRefl)


-- ↔→length≡ : ∀ {x y : List A} →  x ↔ y → length x ≡ length y
-- ↔→length≡ = isInjectiveFin≃ ∘ F≃

-- ¬nil↔cons : ∀ {x : A} {xs} → ¬ ([] ↔ x ∷ xs)
-- ¬nil↔cons = ℕznots ∘ ↔→length≡ {x = []}

-- ¬cons↔nil : ∀ {x : A} {xs} → ¬ (x ∷ xs ↔ [])
-- ¬cons↔nil = ℕsnotz ∘ ↔→length≡ {y = []}

-- _∷↔_ : ∀ (a : A) {xs ys} → xs ↔ ys → a ∷ xs ↔ a ∷ ys
-- a ∷↔ (prm e p) = prm (sucPerm e)  λ { zero → refl ; (suc _) → p _}

-- ≡→↔ : ∀ {xs ys : List A} → xs ≡ ys → xs ↔ ys
-- ≡→↔ {xs = xs} p = prm (≡→Fin≃ (cong length p)) λ _ → cong₂ lookup p (toPathP refl) 


-- headSwap↔ : {x y : A} → ∀ {l} → x ∷ y ∷ l ↔ y ∷ x ∷ l
-- headSwap↔ =
--   prm swap0and1≃ λ { zero → refl ; one → refl ; (suc (suc k)) → refl }

-- overSecondSwap↔ : {x y z : A} → ∀ {l} → x ∷ y ∷ z ∷  l ↔ z ∷ y ∷ x ∷ l
-- overSecondSwap↔ =
--   prm (involEquiv {f = λ { zero → two ; one → one ; two → zero
--                         ; (suc (suc (suc k))) → (suc (suc (suc k))) }}
--     λ { zero → refl ; one → refl ; two → refl ; (suc (suc (suc k))) → refl } )
--     λ { zero → refl ; one → refl ; two → refl ; (suc (suc (suc k))) → refl }


-- _∷↔∷ʳ_ : ∀ xs → (x : A) → xs ∷ʳ x ↔ x ∷ xs
-- _∷↔∷ʳ_ =
--   ind (isRefl↔ ∘ [_])
--         λ x _ → ≡→↔ (++-assoc [ _ ] _ [ _ ])
--           ∙↔ (_ ∷↔ x _)
--           ∙↔ headSwap↔

-- _↔∷ʳ_ : ∀ {xs ys} → xs ↔ ys → ∀ (a : A) → xs ∷ʳ a ↔ ys ∷ʳ a
-- r ↔∷ʳ _ = (_ ∷↔∷ʳ _) ∙↔ (_ ∷↔ r) ∙↔ sym↔ (_ ∷↔∷ʳ _)


-- _++↔_ : (x y : List A) → x ++ y ↔ y ++ x
-- x ++↔ [] = ≡→↔ (++-unit-r x)
-- [] ++↔ y@(_ ∷ _) = ≡→↔ (sym (++-unit-r y) )
-- (x ∷ xs) ++↔ (y ∷ ys) =
--        (x ∷↔ ((xs ++↔ (y ∷ ys))))
--     ∙↔ headSwap↔
--     ∙↔ (y ∷↔ (cong↔++R (sym↔ (ys ∷↔∷ʳ x)) xs)
--               ∙↔ (≡→↔ (++-assoc ys [ x ] xs)))
--   where

--   lookup-FinSumChar : ∀ {xs ys : List A} →
--           ∀ k → lookup (xs ++ ys) k ≡
--            ⊎.rec (lookup xs) (lookup ys)
--              (FinSumChar.inv (length xs) (length ys)
--                (subst Fin (length++ xs ys) k))
--   lookup-FinSumChar {xs = []} {ys} _ = cong (lookup ys) (sym (transportRefl _))
--   lookup-FinSumChar {xs = x ∷ xs} {ys} zero =
--      cong (⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘ (FinSumChar.inv _ _))
--        (transportFin-zero _)
--   lookup-FinSumChar {xs = x ∷ xs} {ys} (suc _) =
--      _ ≡⟨ lookup-FinSumChar {xs = xs} _ ⟩
--      _ ≡⟨ h (FinSumChar.inv _ _ _) ⟩
--      _ ≡⟨ cong (⊎.rec (lookup (x ∷ xs)) (lookup ys) ∘ FinSumChar.inv _ _)
--              (sym (transportFin-suc (length++ xs ys) _ _)) ⟩ _ ∎

--     where
--       h : ∀ z → ⊎.rec _ _ z ≡ ⊎.rec (lookup (x ∷ xs)) _ (FinSumChar.invSucAux _ _ z)
--       h (inl _) = refl
--       h (inr _) = refl

--   cong↔++R : {xs ys : List A} → xs ↔ ys → ∀ l → xs ++ l ↔ ys ++ l
--   cong↔++R {xs = xs} {ys} (prm e p) _ =
--    let h = ⊎-equiv e (idEquiv _)
--    in prm (≡→Fin≃ _ ∙ₑ invEquiv (FinSumChar.Equiv _ _) ∙ₑ h ∙ₑ FinSumChar.Equiv _ _  ∙ₑ ≡→Fin≃ _)
--     λ _ →
--      let k' = FinSumChar.inv _ _ _
--      in _ ≡⟨ lookup-FinSumChar {xs = xs} _ ⟩
--         _ ≡⟨ cong (λ g → ⊎.rec g _ k') (funExt p) ⟩
--         _ ≡⟨ recMap k' ⟩
--         _ ≡⟨ cong (⊎.rec _ _)
--              ( _ ≡⟨ ⊎.elim {C = (λ y → ⊎.mapl _ y ≡ equivFun h y)} (λ _ → refl) (λ _ → refl) k' ⟩
--                _ ≡⟨ sym (FinSumChar.ret _ _ _) ⟩
--                _ ≡⟨ cong (FinSumChar.inv _ _)
--                     (sym (transportTransport⁻ (cong Fin _) _)) ⟩ _ ∎ ) ⟩
--         _ ≡⟨ sym (lookup-FinSumChar {xs = ys} _) ⟩ _ ∎


-- rev↔ : (xs : List A) → xs ↔ rev xs
-- rev↔ [] = isRefl↔ []
-- rev↔ (x ∷ xs) = (x ∷↔ rev↔ xs) ∙↔ (sym↔ ((rev xs) ∷↔∷ʳ x))

-- List/↔ : (A : Type ℓ) → Type ℓ
-- List/↔ A =  List A / _↔_

-- pattern []/ = [ [] ]/

-- _∷/_ : A → List/↔ A → List/↔ A
-- _∷/_ {A = A} a = SQ.rec squash/ ([_]/ ∘ (a ∷_))
--             λ _ _ r → eq/ _ _ (prm (sucPerm (F≃ r))
--               λ { zero → refl ; (suc _) → l≡ r _})


-- List→FMSet : List A → FMSet A
-- List→FMSet {A = A} = foldr {B = FMSet A} _∷fm_ []fm


-- PunchHeadInOut/≡ : (l : List A) → ∀ k
--   → List→FMSet l ≡ List→FMSet (permute l (rot≃ k))
-- PunchHeadInOut/≡ (x ∷ l) zero =
--   cong List→FMSet (sym (tabulate-lookup (x ∷ l)))
-- PunchHeadInOut/≡ (x ∷ x₁ ∷ l) one i =
--   comm x x₁ (List→FMSet (tabulate-lookup l (~ i))) i
-- PunchHeadInOut/≡ (x ∷ x₁ ∷ l) (suc (suc k)) =
--   cong (x ∷fm_) (PunchHeadInOut/≡ (x₁ ∷ l) (suc k)) ∙ comm _ _ _


-- PunchHeadInOut/≡⁻ : ∀ (x : A) (l : List A) → ∀ k
--       → List→FMSet (x ∷ l) ≡
--          List→FMSet (permute (x ∷ l) (invEquiv (rot≃ k)))

-- PunchHeadInOut/≡⁻ x l zero = cong (List→FMSet ∘ (x ∷_))  (sym (tabulate-lookup l))
-- PunchHeadInOut/≡⁻ x (x₁ ∷ l) one i =
--   comm x x₁ (List→FMSet ((tabulate-lookup l) (~ i))) i
-- PunchHeadInOut/≡⁻ x (x₁ ∷ l) (suc (suc k)) =
--   _ ≡⟨ comm _ _ _ ⟩
--   _ ≡⟨ cong (x₁ ∷fm_) (PunchHeadInOut/≡⁻ x l (suc k)) ⟩
--   _ ≡⟨ cong ((x₁ ∷fm_) ∘ List→FMSet ∘ tabulate (suc _))
--        (funExt (lookup-swap x₁ x l ∘
--           suc ∘ equivFun (invEquiv (rot≃ (suc k))))) ⟩
--   _ ∎

-- -- ↔→FMSet≡ : (a b : List A) → a ↔ b → List→FMSet a ≡ List→FMSet b
-- -- ↔→FMSet≡ [] [] _ = refl
-- -- ↔→FMSet≡ [] (_ ∷ _) = ⊥.rec ∘ ¬nil↔cons
-- -- ↔→FMSet≡ (_ ∷ _) [] = ⊥.rec ∘ ¬cons↔nil
-- -- ↔→FMSet≡ {A = A} (x ∷ xs) (y ∷ ys) r@(prm e _) =
-- --    let (e' , p') = unwindPermHead e
-- --        k' = equivFun e zero
-- --        xs' = permute xs (invEquiv e')
-- --        (prm _ p⁻) = isSym↔ _ _ r
-- --        pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))
-- --    in
-- --       _ ≡⟨ cong (x ∷fm_) (↔→FMSet≡ xs xs' (↔permute xs (invEquiv e'))) ⟩
-- --       _ ≡⟨ PunchHeadInOut/≡⁻ x xs' (subst Fin pL k') ⟩
-- --       _ ≡⟨ cong List→FMSet
-- --           (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'))
-- --                     (rot≃∙ₑ≡→Fin≃ pL k')) ⟩
-- --            _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'))
-- --                            (invEq (rot≃ k'))  ⟩
-- --            _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p') ⟩
-- --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻)) ⟩
-- --            _ ≡⟨ tabulate-lookup _ ⟩ (y ∷ ys) ∎
-- --           ) ⟩ _ ∎


-- -- factor↔ : (a b : List A) → (r : a ↔ b) →
-- --             r ≡ ≡→↔ (sym (tabulate-lookup a) ∙ cong (tabulate (length a)) (funExt (l≡ r)))
-- --                    ∙↔ sym↔ (↔permute b (F≃ r)) 
-- -- factor↔ a b r =
-- --    cong₂ prm
-- --      (equivEq (cong ((F≃ r .fst) ∘_) (sym (funExt (isSet-subst {B = Fin} isSetℕ _))
-- --             ∙ funExt (substComposite Fin _ _))))
-- --      ({!!})

-- -- factor↔Σ : (a b : List A) → (r : a ↔ b) →
-- --             Σ[ p ∈ a ≡ permute b (F≃ r) ]
-- --               r ≡ ≡→↔ p  ∙↔ sym↔ (↔permute b (F≃ r)) 
-- -- factor↔Σ a b r = {!!}

-- -- factor↔Σ' : (a b : List A) → (r : a ↔ b) →
-- --             Σ[ p ∈ permute a (invEquiv (F≃ r)) ≡ b ]
-- --               r ≡ ↔permute a (invEquiv (F≃ r)) ∙↔ ≡→↔ p 
-- -- fst (factor↔Σ' a b r) = cong (tabulate (length b)) (funExt (l≡ r ∘ invEq (F≃ r)))
-- --                              ∙ cong ((tabulate (length b)) ∘ ((lookup b) ∘_))
-- --                               (funExt (secEq (F≃ r)) ) ∙ tabulate-lookup b
-- -- snd (factor↔Σ' a b r@(prm e p)) =
-- --    cong₂ prm
-- --      (equivEq (funExt λ x → sym (isSet-subst {B = Fin} isSetℕ _ ((fst (F≃ r) x)))
-- --        ∙ substComposite Fin _ _ (fst (F≃ r) x)))
-- --      {!!}

-- -- isEquiv∷/ : ∀ (x : A) → isEquiv' λ l → {!!}
-- -- isEquiv∷/ = {!!}

-- -- Goal: isContr (fiber fromFM [ a ∷ l ]/)
-- -- ————————————————————————————————————————————————————————————
-- -- x   : isContr (fiber fromFM [ l ]/)
-- -- l   : List A   (not in scope)
-- -- a   : A

-- IsoList/↔FMSet : Iso (List/↔ A) (FMSet A)
-- IsoList/↔FMSet = w
--   where

--     toFM = SQ.rec trunc List→FMSet ↔→FMSet≡

--     fromFM = FM.Rec.f squash/
--         []/ _∷/_
--         λ _ _ → SQ.elimProp (λ _ → squash/ _ _)
--           λ _ → eq/ _ _ (prm swap0and1≃
--              λ { zero → refl ; one → refl ; (suc (suc k)) → refl})

--     -- isEquiv'FromFM : isEquiv' fromFM
--     -- isEquiv'FromFM =
--     --   SQ.elimProp (λ _ → isPropIsContr)
--     --    (ind {!!}
--     --     λ {a} {l} x → {!!}) 

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



-- -- List//↔ : (A : Type ℓ) → Type ℓ
-- -- List//↔ A =  List A // isTrans↔

-- -- _∷//_ : A → List//↔ A → List//↔ A
-- -- _∷//_ {A = A} = GQ.Rrec.f r

-- --   where
-- --     r : GQ.Rrec.f 
-- --     r = ?

--   --   λ a → GQ.rec isTrans↔ squash// ([_]// ∘ (a ∷_))
--   --         (λ {x} {y} r → eq// (prm (sucPerm (F≃ r)) (w {x = x} {y} {r} a) ))
--   --          λ r s →
--   --            comp// (prm (sucPerm (F≃ r)) (w a)) (prm (sucPerm (F≃ s)) (w a) ) ▷
--   --                 cong eq//
--   --                   (cong₂ prm
--   --                       (equivEq (funExt (λ { zero → refl ; (suc _) → refl })))
--   --                       (funExt (λ { zero → sym compPathRefl ; (suc _) → refl })))
--   -- where
--   --   w : {x y : List A} → {r : x ↔ y } → ∀ a _ → _
--   --   w _ zero = refl
--   --   w {r = r} _ (suc _) = l≡ r _

-- -- length// : List//↔ A → ℕ
-- -- length// = GQ.RelimSet.f ?
-- --   where
-- --     r : ?
-- --     r = ?

-- -- -- isTrans↔ (λ _ → isSetℕ) length ↔→length≡


-- -- -- length//-∷// : ∀ (a : A) xs → length// (a ∷// xs) ≡ suc (length// xs)
-- -- -- length//-∷// a = GQ.elimProp isTrans↔ (λ _ → isSetℕ _ _) λ _ → refl

-- -- -- ListOfLen// : (A : Type ℓ) → ℕ → Type ℓ
-- -- -- ListOfLen// A n = Σ (List//↔ A) λ x → length// x ≡ n



-- -- -- ↔→FMSet2≡Refl : (a : List A) → Path (Path (List//↔ A) _ _)
-- -- --                                  (eq// (isRefl↔ a))
-- -- --                                  refl  
-- -- -- ↔→FMSet2≡Refl a =
-- -- --   ∙²≡id→≡refl (sym (cong eq// comp↔Refl 
-- -- --         ∙ comp'// _ isTrans↔ (isRefl↔ a) (isRefl↔ a)))


-- -- -- -- -- -- -- funExt∙ : ∀ {ℓ'} {B C : Type ℓ'} {f g h : B → A}
-- -- -- -- -- -- --             → (p : ∀ k → f k ≡ g k) → (q : ∀ k → g k ≡ h k)
-- -- -- -- -- -- --             → funExt (λ k → p k ∙ q k ) ≡ funExt p ∙ funExt q
-- -- -- -- -- -- -- funExt∙ p q = refl


-- -- -- ListOfLen :  ∀ {ℓ} (A : Type ℓ) → ℕ → Type ℓ
-- -- -- ListOfLen A n = Σ (List A) λ l → length l ≡ n

-- -- -- isOfHLevelListOfLen : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
-- -- --   → isOfHLevel (suc (suc n)) A → ∀ m → isOfHLevel (suc (suc n)) (ListOfLen A m)
-- -- -- isOfHLevelListOfLen n x m =
-- -- --   isOfHLevelΣ (suc (suc n)) (isOfHLevelList n x)
-- -- --    λ _ → isProp→isOfHLevelSuc (suc n) (isSetℕ _ _) 


-- -- module FC2M {ℓ} {A : Type ℓ} where

-- --   List→FMSet2 : List A → FMSet2 A
-- --   List→FMSet2 = foldr {B = FMSet2 A} _∷2_ []

-- --   PunchHeadInOut//≡⁻ : ∀ (x : A) (l : List A) → ∀ k
-- --         → List→FMSet2 (x ∷ l) ≡
-- --            List→FMSet2 (permute (x ∷ l) (invEquiv (rot≃ k)))
-- --   PunchHeadInOut//≡⁻ x l zero = cong (List→FMSet2 ∘ (x ∷_))  (sym (tabulate-lookup l))
-- --   PunchHeadInOut//≡⁻ x (x₁ ∷ l) one i =
-- --     comm x x₁ (List→FMSet2 ((tabulate-lookup l) (~ i))) i
-- --   PunchHeadInOut//≡⁻ x (x₁ ∷ l) (suc (suc k)) =
-- --     _ ≡⟨ comm _ _ _ ⟩
-- --     _ ≡⟨ cong (x₁ ∷2_) (PunchHeadInOut//≡⁻ x l (suc k)) ⟩
-- --     _ ≡⟨ cong ((x₁ ∷2_) ∘ List→FMSet2 ∘ tabulate (suc _))
-- --          (funExt (lookup-swap x₁ x l ∘
-- --             suc ∘ equivFun (invEquiv (rot≃ (suc k))))) ⟩
-- --     _ ∎


-- --   permute→FMSet2≡ : (xs : List A) → ∀ {n} → (e : Fin n ≃ Fin (length xs))
-- --        → List→FMSet2 xs ≡ List→FMSet2 (permute xs e)
-- --   permute→FMSet2≡ [] {zero} e = refl
-- --   permute→FMSet2≡ [] {suc n} e = ⊥.rec (¬Fin0 (fst e zero))
-- --   permute→FMSet2≡ (x ∷ xs) {zero} e = ⊥.rec (¬Fin0 (invEq e zero))
-- --   permute→FMSet2≡ (x ∷ xs) {suc n} eP =
-- --    let r@(prm e _) = ↔permute (x ∷ xs) eP       
-- --        (e' , p') = unwindPermHead e
-- --        k' = equivFun e zero
-- --        xs' = permute xs (invEquiv e')
-- --        (prm _ p⁻) = isSym↔ _ _ r
-- --        pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))

-- --    in
-- --       _ ≡⟨ cong (x ∷2_) (permute→FMSet2≡ xs (invEquiv e'))
-- --            ∙ PunchHeadInOut//≡⁻ x xs' (subst Fin pL k') ⟩
-- --       _ ≡⟨ cong List→FMSet2
-- --           (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'))
-- --                     (rot≃∙ₑ≡→Fin≃ pL k')) ⟩
-- --            _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'))
-- --                            (invEq (rot≃ k'))  ⟩
-- --            _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p') ⟩
-- --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻)) ⟩
-- --            _ ≡⟨ tabulate-lookup _ ⟩ (permute (x ∷ xs) eP) ∎
-- --           ) ⟩ _ ∎

-- --   permute→FMSet2≡Comp : (xs : List A) → ∀ {n} → (e d : Fin n ≃ Fin (length xs))
-- --        → ?
-- --   permute→FMSet2≡Comp = ?


--          -- lSqP0 : (fst (rot≃ (fst e zero))
--          --           (suc
--          --            (fst (rot≃ (fst (fst (unwindPermHead e)) zero)) zero)))
--          --           ≡ (fst (rot≃ (fst e one)) zero)
--          -- lSqP0 = {!!}


-- -- module RelΣ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') where
-- --   ≃relΣ : (A → B) → (A → B) → Type (ℓ-max ℓ ℓ') 
-- --   ≃relΣ x y = Σ (A ≃ A) λ e → x ≡ y ∘ fst e

-- --   ≃relΣ-elim : ∀ {ℓc} → (C : ∀ x y → ≃relΣ x y → Type ℓc)
-- --                 → (∀ x → C x x ((idEquiv _) , refl))
-- --                 →  ∀ x y p → C x y p
-- --   ≃relΣ-elim C z x₁ y =
-- --     uncurry (λ e p →
-- --         EquivJ (λ A₁ e → (x : A₁ → B) → (y : A → B) → (p : x ≡ y ∘ fst e) →
-- --             C ({!!}) y ({!!} , {!!}))
-- --       {!!} e x₁ y p)  


-- -- module FC2M {ℓ} {A : Type ℓ} where

 
-- --   record _↔ₙ_  {n} (x y : Fin n → A) : Type ℓ where
-- --     constructor prm
-- --     field
-- --       F≃ : (Fin n ≃ Fin n)
-- --       l≡ : x ≡ y ∘ fst F≃ 



-- --   open _↔ₙ_

  
-- --   isTrans↔ₙ : ∀ n → BinaryRelation.isTrans (_↔ₙ_ {n = n}) 
-- --   isTrans↔ₙ n a b c (prm e p) (prm f q) =
-- --     prm (e ∙ₑ f) (p ∙ cong (_∘ (fst e)) q)

-- --   isRefl↔ₙ : ∀ n → BinaryRelation.isRefl (_↔ₙ_ {n = n})
-- --   F≃ (isRefl↔ₙ _ a) = idEquiv _
-- --   l≡ (isRefl↔ₙ _ a) = refl


-- --   -- isTrans↔ₙ'' : ∀ n → (e f : List (Fin (n))) → (a b c : Fin (suc n) → A)
-- --   --    → (p : a ≡ b ∘ fst (concatG (SymData (suc n)) (mapList adjTransposition e)))
-- --   --    → (q : b ≡ c ∘ fst (concatG (SymData (suc n)) (mapList adjTransposition f)))
-- --   --    → a ↔ₙ c
-- --   -- isTrans↔ₙ'' n e f a b c p q =
-- --   --   prm
-- --   --     (concatG (SymData (suc n)) (mapList adjTransposition (e ++ f)))
-- --   --     (p ∙ cong (_∘ fst (concatG (SymData (suc n)) (mapList adjTransposition e))) q ∙
-- --   --                 cong (c ∘_) (cong fst (concatG·map (SymData (suc n)) adjTransposition e f)))

                


-- --   -- isTrans↔ₙ' : ∀ n → BinaryRelation.isTrans (_↔ₙ_ {n = n}) 
-- --   -- isTrans↔ₙ' zero a b c (prm e p) (prm f q) = prm (idEquiv _) (funExt (⊥.rec ∘ ¬Fin0))
-- --   -- isTrans↔ₙ' (suc n) a b c (prm e p) (prm f q) =
-- --   --  GeneratedElimConstr2
-- --   --   (SymData (suc n) )
-- --   --   (generatedSym n)
-- --   --   (λ e f → (a b c : _)
-- --   --     → (p : a ≡ b ∘ fst e)
-- --   --     → (q : b ≡ c ∘ fst f) → a ↔ₙ c)
-- --   --    (isTrans↔ₙ'' n)  e f a b c p q
     


-- --   Fin→//↔ : ℕ → Type ℓ
-- --   Fin→//↔ n =  (Fin n → A) // isTrans↔ₙ n

-- --   List→FMSet2 : List A → FMSet2 A
-- --   List→FMSet2 = foldr {B = FMSet2 A} _∷2_ []

-- --   tabulateFM2 : ∀ {n} → (Fin n → A) → FMSet2 A
-- --   tabulateFM2 {zero} _ = []
-- --   tabulateFM2 {suc n} f = (f zero) ∷2 tabulateFM2 (f ∘ suc)

-- --   tabulateFM2OfLen : ∀ {n} → (Fin n → A) → FMSet2OfLen A n
-- --   tabulateFM2OfLen {zero} _ = [] , refl 
-- --   tabulateFM2OfLen {suc n} f =
-- --     let (x , p) = tabulateFM2OfLen (f ∘ suc)
-- --     in (f zero) ∷2 x , cong suc p

-- --   toFM2≡Punch : ∀ {n} → (k : Fin (suc n)) → (b : Fin (suc n) → A) →
-- --                fst (tabulateFM2OfLen (b ∘ fst (rot≃ k))) ≡
-- --                 fst (tabulateFM2OfLen b)
-- --   toFM2≡Punch zero b = refl
-- --   toFM2≡Punch {suc n} (suc k) b =
-- --     comm _ _ _ ∙ cong (b zero ∷2_) (toFM2≡Punch k (b ∘ suc)) 

-- --   toFM2≡adjT : ∀ {n} → (k : Fin n) → (b : Fin (suc n) → A) →
-- --                fst (tabulateFM2OfLen (b ∘ fst (adjTransposition k))) ≡
-- --                 fst (tabulateFM2OfLen b)
-- --   toFM2≡adjT zero b = comm _ _ _
-- --   toFM2≡adjT (suc k) b = cong (b zero ∷2_) (toFM2≡adjT k (b ∘ suc))


-- --   toFM2≡U : ∀ {n} → (b : Fin n → A) →
-- --            (e : Fin n ≃ Fin n) → fst (tabulateFM2OfLen (b ∘ fst e)) ≡ fst (tabulateFM2OfLen b)
-- --   toFM2≡U {zero} b _ = refl
-- --   toFM2≡U {suc n} b e = 
-- --     let (e' , p') = unwindPermHead e
-- --         e0 = fst e zero
-- --     in (cong (λ e → fst (tabulateFM2OfLen (λ x → (b ∘ fst e) (x)))) p')
-- --        ∙ cong (b ((fst (rot≃ (fst e zero)) zero)) ∷2_)
-- --          (toFM2≡U (b ∘ fst (rot≃ e0) ∘ suc ) e')
-- --        ∙ toFM2≡Punch e0 b


-- --   toFM2≡Uid : ∀ {n} → (b : Fin n → A) → toFM2≡U b (idEquiv _) ≡ refl
-- --   toFM2≡Uid {zero} b = refl
-- --   toFM2≡Uid {suc n} b =            
-- --     let (e' , p') = unwindPermHead (idEquiv (Fin (suc n)))
-- --         pPrev = toFM2≡Uid {n} (b ∘ suc)
-- --     in subst 
-- --           (λ (e' , p') → (cong (λ e → fst (tabulateFM2OfLen (λ x → (b ∘ fst e) (x)))) p')
-- --                   ∙ cong (b ((fst (rot≃ zero) zero)) ∷2_)
-- --                     (toFM2≡U (b ∘ suc ) e')
-- --                   ∙ toFM2≡Punch zero b ≡ refl)
-- --           (Σ≡Prop 
-- --              (λ e' → isOfHLevel≃ 2 (isSetFin) (isSetFin) (idEquiv (Fin (suc n)))
-- --             (sucPerm e' ∙ₑ idEquiv _ ))
-- --             {u = (idEquiv _) , equivEq ( refl =→ refl)}
-- --             {v = unwindPermHead (idEquiv (Fin (suc n)))}
-- --                   (sym unwindPermId))
-- --                   ( cong (refl ∙_) (sym (rUnit _)) ∙ sym (lUnit _)
-- --                     ∙ λ i i₁ → b zero ∷2 pPrev i i₁)


-- --   toFM2≡U-swap0and1 : ∀ n → ∀ x y → (b : Fin (n) → A) →
-- --          toFM2≡U (cons→ y (cons→ x b)) (swap0and1≃ {n = n}) ≡
-- --                  (λ i → comm x y (fst (tabulateFM2OfLen b)) i)
-- --   toFM2≡U-swap0and1 n x y b =
-- --    let (e' , p') = unwindPermHead (swap0and1≃ {n = n})
-- --        sqH : Square { A = Fin n → Fin (suc (suc n))}
-- --                 (λ i x → fst (p' i) (suc (suc x)) )
-- --                 refl
-- --                 refl
-- --                 refl
-- --        sqH = isSet→ isSetFin _ _  _ _
-- --    in assoc _ _ _
-- --      ∙ cong′ (_∙ toFM2≡Punch one (cons→ y (cons→ x b)))
-- --           (  (cong
-- --                 (λ e → fst (tabulateFM2OfLen (λ x' → ((cons→ y (cons→ x b)) ∘ fst e) (x'))))
-- --                 p')
-- --              ∙  cong (x ∷2_)
-- --                  (toFM2≡U ((cons→ y (cons→ x b)) ∘ fst (rot≃ one) ∘ suc ) e')
-- --             ≡⟨ cong₂ _∙_
-- --               ((λ i j → (cons→ y (cons→ x b))
-- --                           (isSetFin one one  (funExt⁻ (cong fst p') zero) refl i j) ∷2
-- --                         (cons→ y (cons→ x b))
-- --                           (isSetFin zero zero  (funExt⁻ (cong fst p') one) refl i j) ∷2
-- --                 fst (tabulateFM2OfLen ((cons→ y (cons→ x b)) ∘ sqH i j)) ))
-- --               (cong (cong (x ∷2_))
-- --                (cong (toFM2≡U ((cons→ y (cons→ x b)) ∘ fst (rot≃ one) ∘ suc ))
-- --                    (equivEq {e = e'} {f = idEquiv _} (refl =→ refl))
-- --                     ∙ toFM2≡Uid (((cons→ y (cons→ x b)) ∘ fst (rot≃ one) ∘ suc )))) ⟩ 
-- --        _ ≡⟨  sym compPathRefl ⟩
-- --             refl ∎ )
-- --        ∙ sym (lUnit _) ∙ sym (rUnit _)
  

-- --   unwindPermHeadCompAdjTranspFST' : ∀ m → ∀ k → (e : Fin (suc (suc m)) ≃ Fin (suc (suc m)))
-- --          → Square
-- --             (cong ((adjTransposition (suc k)) ∙ₑ_) (snd (unwindPermHead (e))))         
-- --             (snd (unwindPermHead (adjTransposition (suc k) ∙ₑ e)))
-- --             refl
-- --             (equivEq (refl =→ refl))
-- --   unwindPermHeadCompAdjTranspFST' m k e =
-- --       isSet→isSet' (isOfHLevel≃ 2 (isSetFin) (isSetFin))
-- --         _ _ _ _ 

  

-- --   comm-over :   {xs ys : FMSet2 A}
-- --                 (p : xs ≡ ys)
-- --                 (a a' : A)
-- --                 → comm _ _ _ ∙ cong (λ x → a' ∷2 a ∷2 x) p
-- --                   ≡ cong (λ x → a ∷2 a' ∷2 x) p ∙ comm _ _ _
-- --   comm-over p a a' = homotopyNatural (λ a₁ i → comm _ _ _ i) p


-- --   toFM2≡Step0lem : ∀ {n} → ∀ (b : Fin (suc (suc n)) → A)
-- --                    → (e : Fin (suc (suc n)) ≃ Fin (suc (suc n)))
-- --                    → (eee : Σ ((Fin n ≃ Fin n) × (Fin (suc (suc n)) → Fin (suc (suc n))))
-- --                          λ (e' , e'') → fst e ≡ e'' ∘ fst (sucPerm (sucPerm  e')) )
-- --                    → fst (tabulateFM2OfLen (b ∘ fst e))
-- --                      ≡ fst (tabulateFM2OfLen (b ∘ snd (fst eee)))
-- --   toFM2≡Step0lem b e ((e' , e'') , p) =
-- --     (cong (λ e → fst (tabulateFM2OfLen (λ x → (b ∘ e) (x)))) p)
-- --        ∙
-- --       cong (λ z → b _ ∷2 (b _ ∷2 z)) (toFM2≡U (λ x → b (e'' (suc (suc x)))) e') 


-- --   lemmSq : ∀ n  → (b : Fin (suc (suc n)) → A) → (e0 e1 : Fin (suc n)) → (p : toℕ e1 < toℕ (suc e0)) →
               
-- --                Square
-- --                  ((comm _ (b (suc (rot≃ e0 .fst zero))) _
-- --                       ∙ cong (b ((fst (rot≃ (suc e0)) zero)) ∷2_)
-- --                           (toFM2≡Punch e1
-- --                            (λ x → b (fst (rot≃ (suc e0)) (suc x)))))
-- --                       ∙ toFM2≡Punch (suc e0) b)
-- --                  (cong (b ((fst (rot≃ (weakenFin e1)) zero)) ∷2_)
-- --                           (toFM2≡Punch e0
-- --                            (λ x → b (fst (rot≃ (weakenFin e1)) (suc x))))
-- --                    ∙ toFM2≡Punch (weakenFin e1) b)
-- --                  (cong (fst ∘ tabulateFM2OfLen ∘ (b ∘_))
-- --                ( unwindPermHeadCompSwap0and1'Case> e0 e1 p))
-- --                  (refl {x = fst (tabulateFM2OfLen b)})
-- --   lemmSq n b e0 zero p =
-- --      (assoc _ _ (cong (b zero ∷2_) (toFM2≡Punch e0 (b ∘ suc)))
-- --          ∙  cong (_∙ (cong (b zero ∷2_) (toFM2≡Punch e0 (b ∘ suc))))
-- --              (cong (_∙ comm _ _ _) (sym (rUnit (comm _ _ _)))
-- --               ∙ comm-invo _ _ _ ) )
-- --           ∙ sym (lUnit (cong (b zero ∷2_) (toFM2≡Punch e0 (b ∘ suc))))
-- --           ∙ rUnit (cong (b zero ∷2_) (toFM2≡Punch e0 (b ∘ suc)))
-- --   lemmSq (suc n) b zero (suc e1) p = ⊥.rec (¬-<-zero (pred-≤-pred p))
-- --   lemmSq (suc m) b (suc e0) (suc e1) p = 
-- --      let wS = lemmSq m (b ∘ suc) e0 e1 (pred-≤-pred p) 
-- --          w = unwindPermHeadCompSwap0and1'Case> e0 e1 (pred-≤-pred p)
-- --          z = cong {B = λ _ → Fin (suc (suc (suc m)))} (suc {n = suc (suc m)}) ∘ funExt⁻ w
-- --          b0 = _
-- --          b1 = _
-- --          bxs = _
-- --          Pu1 = (toFM2≡Punch (e1) (λ x → b (suc (fst (swap0and1≃ ∙ₑ sucPerm (rot≃ e0)) (suc x)))))
-- --          ppL = (cong (b ((suc (fst (swap0and1≃ ∙ₑ sucPerm (rot≃ e0)) zero))) ∷2_)
-- --                      Pu1
-- --                        ∙ toFM2≡Punch (suc e0) (b ∘ suc))
-- --          Pu0R = cong (_∷2_ (b (suc (fst (rot≃ (weakenFin e1)) zero))))
-- --                   (toFM2≡Punch e0
-- --                   (λ x → b (suc (fst (rot≃ (weakenFin e1)) (suc x)))))
-- --          Pu1R = (toFM2≡Punch (weakenFin e1) (b ∘ suc))
-- --      in ( _
-- --           ≡⟨ sym (assoc _ _ _) ∙ cong (λ x → comm b0 b1 bxs ∙ x
-- --                ∙ ((comm _ _ _) ∙ cong (b zero ∷2_) (toFM2≡Punch (suc e0) (b ∘ suc))))
-- --                (cong-∙ (b ((fst (rot≃ (suc (suc e0))) zero)) ∷2_)
-- --                  _ _) ∙ cong (comm b0 b1 bxs ∙_)
-- --                   (sym (assoc _ _ _)  ∙ (cong (cong (b1 ∷2_) (comm _ _ _) ∙_)
-- --                        (assoc _ _ _ ∙
-- --                         cong (_∙ cong (b zero ∷2_) (toFM2≡Punch (suc e0) (b ∘ suc)))
-- --                           (sym (comm-over Pu1 _ _)) ∙ sym (assoc _ _ _)
-- --                              ∙ (cong (comm _ _ _ ∙_) (sym (cong-∙ ((b zero ∷2_)) _ _)))) ∙ assoc _ _ _
-- --                            )) ∙ assoc _ _ _ ⟩ _
-- --            ≡⟨ cong (_∙ cong (b zero ∷2_) (cong (b ((suc (fst (swap0and1≃ ∙ₑ sucPerm (rot≃ e0)) zero))) ∷2_)
-- --                      (toFM2≡Punch (e1) (λ x → b (suc (fst (swap0and1≃ ∙ₑ sucPerm (rot≃ e0)) (suc x)))))
-- --                        ∙ toFM2≡Punch (suc e0) (b ∘ suc)))
-- --                         (comm-braid _ _ _ _ ∙ assoc _ _ _) ∙ sym (assoc _ _ _)
-- --               ∙ cong ((cong (b0 ∷2_) (comm _ _ _) ∙ comm _ _ _) ∙_)
-- --                  (sym (cong-∙ (b zero ∷2_) (comm _ _ _) ppL) ∙ cong (cong (b zero ∷2_)) (assoc _ _ _) ) ⟩
-- --                _
-- --            ∎ )
-- --           ◁ (λ i → (cong (b (z zero i) ∷2_) (comm _ _ _) ∙ comm _ (b zero) _)
-- --              ∙ (cong (b zero ∷2_) (wS i))) ▷
-- --           ((λ i → assoc (cong (b (z zero i1) ∷2_) (comm _ _ _))
-- --                      (comm _ _ _) (cong-∙ ((b zero ∷2_)) Pu0R (toFM2≡Punch (weakenFin e1) (b ∘ suc)) i) (~ i))
-- --             ∙ cong ((cong (b (z zero i1) ∷2_) (comm _ _ _)) ∙_)
-- --                 (assoc _ _ _ ∙ cong (_∙ cong (b zero ∷2_) Pu1R)
-- --                   (comm-over (toFM2≡Punch e0
-- --                   (λ x → b (suc (fst (rot≃ (weakenFin e1)) (suc x))))) _ _) ∙ (sym (assoc _ _ _)))
-- --                   ∙ assoc _ _ _ ∙  cong (_∙ toFM2≡Punch (weakenFin (suc e1)) b)
-- --                      (sym (cong-∙ ((b (z zero i1) ∷2_)) _ _))) 


-- --   lemmSq2 : ∀ n  → (b : Fin (suc (suc n)) → A) → (e0 e1 : Fin (suc n)) → (p : toℕ e1 < toℕ (suc e0)) →
               
-- --                Square
-- --                  ((cong (b ((fst (rot≃ (suc e0)) zero)) ∷2_)
-- --                           (toFM2≡Punch e1
-- --                            (λ x → b (fst (rot≃ (suc e0)) (suc x)))))
-- --                       ∙ toFM2≡Punch (suc e0) b)
-- --                  ((comm _ (b (fst (rot≃ (weakenFin e1)) zero)) _
-- --                       ∙ cong (b ((fst (rot≃ (weakenFin e1)) zero)) ∷2_)
-- --                           (toFM2≡Punch e0
-- --                            (λ x → b (fst (rot≃ (weakenFin e1)) (suc x)))))
-- --                    ∙ toFM2≡Punch (weakenFin e1) b)
-- --                  (cong (fst ∘ tabulateFM2OfLen ∘ (b ∘_))
-- --                ( sym ((cong (_∘ swap0and1) (sym (unwindPermHeadCompSwap0and1'Case> e0 e1 p))
-- --             ∙ cong {x = swap0and1 {n} ∘ swap0and1} {y = idfun _}
-- --                 (λ f  → fst (sucPerm (rot≃ e1) ∙ₑ swap0and1≃ ∙ₑ sucPerm (rot≃ e0)) ∘ f)
-- --                   ((cong fst (swap0and1≃²=idEquiv {n = n}))))) ))
-- --                  (refl {x = fst (tabulateFM2OfLen b)})
-- --   lemmSq2 n b e0 e1 p i j =         
-- --      let z = unwindPermHeadCompSwap0and1'Case> e0 e1 p
-- --      in hcomp
-- --       ((λ k → λ { (i = i0) →
-- --              (cong ((comm (b ((fst (rot≃ (suc e0)) zero))) _ _) ∙_)
-- --                 (sym (assoc (comm _ _ _) (cong (b ((fst (rot≃ (suc e0)) zero)) ∷2_)
-- --                           (toFM2≡Punch e1
-- --                            (λ x → b (fst (rot≃ (suc e0)) (suc x))))) (toFM2≡Punch (suc e0) b)))
-- --              ∙∙ assoc (comm _ _ _) (comm _ _ _) (_)
-- --              ∙∙ cong (_∙ ((cong (b ((fst (rot≃ (suc e0)) zero)) ∷2_)
-- --                           (toFM2≡Punch e1
-- --                            (λ x → b (fst (rot≃ (suc e0)) (suc x)))))
-- --                       ∙ toFM2≡Punch (suc e0) b)) (comm-invo _ _ _)
-- --                       ∙
-- --                       sym (lUnit _)) k j
-- --                 ; (i = i1) →
-- --                       (assoc (comm _ (b (fst (rot≃ (weakenFin e1)) zero)) _)
-- --                                  (cong (b ((fst (rot≃ (weakenFin e1)) zero)) ∷2_)
-- --                           (toFM2≡Punch e0
-- --                            (λ x → b (fst (rot≃ (weakenFin e1)) (suc x)))))
-- --                       (toFM2≡Punch (weakenFin e1) b)
-- --                       k) j
-- --                 ; (j = i0) → fst (tabulateFM2OfLen (b ∘
-- --                       isSet→isSet' (isSet→ isSetFin)
-- --                       refl
-- --                       refl
-- --                       (funExt⁻ (unwindPermHeadCompSwap0and1'Case> e0 e1 p) one
-- --                        =→ funExt⁻ (unwindPermHeadCompSwap0and1'Case> e0 e1 p) zero
-- --                        =→ cong (_∘ (λ x → suc (suc x))) (unwindPermHeadCompSwap0and1'Case> e0 e1 p))
-- --                       (( sym ((cong (_∘ swap0and1) (sym (unwindPermHeadCompSwap0and1'Case> e0 e1 p))
-- --             ∙ cong {x = swap0and1 {n} ∘ swap0and1} {y = idfun _}
-- --                 (λ f  → fst (sucPerm (rot≃ e1) ∙ₑ swap0and1≃ ∙ₑ sucPerm (rot≃ e0)) ∘ f)
-- --                   ((cong fst (swap0and1≃²=idEquiv {n = n}))))) ))
-- --                             i k))
-- --                 ; (j = i1) → fst (tabulateFM2OfLen b)
-- --                 }))
-- --        ( ((comm _ _ _) ∙ lemmSq n b e0 e1 p i) j)


-- --   lemmSq' : ∀ n → (e : Fin (suc (suc n)) ≃ Fin (suc (suc n))) →
-- --               (b : Fin (suc (suc n)) → A) →
-- --                Square
-- --                  ((comm _ _ _
-- --                       ∙ cong (b ((fst (rot≃ (fst e zero)) zero)) ∷2_)
-- --                           (toFM2≡Punch (predFin (invEq (rot≃ (fst e zero)) (fst e one)))
-- --                            (λ x → b (fst (rot≃ (fst e zero)) (suc x)))))
-- --                       ∙ toFM2≡Punch (fst e zero) b)
-- --                  (cong (b ((fst (rot≃ (fst e one)) zero)) ∷2_)
-- --                           (toFM2≡Punch (predFin (invEq (rot≃ (fst e one)) (fst e zero)))
-- --                            (λ x → b (fst (rot≃ (fst e one)) (suc x))))
-- --                    ∙ toFM2≡Punch (fst e one) b)
-- --                  (cong (fst ∘ tabulateFM2OfLen ∘ (b ∘_))
-- --                (cong fst (unwindPermHeadCompSwap0and1 e)))
-- --                  refl
-- --   lemmSq' n e b =
-- --     rotRotElimDep {A = (λ e0 e1 e0' e1' →
-- --          swap0and1≃ ∙ₑ sucPerm (rot≃ e1') ∙ₑ rot≃ e0
-- --       ≡  sucPerm (rot≃ e0') ∙ₑ rot≃ e1)}
-- --     (λ e0 e1 e0' e1' x →
-- --       Square
-- --         (((comm _ _ _
-- --                       ∙ cong (b ((fst (rot≃ e0) zero)) ∷2_)
-- --                           (toFM2≡Punch e1'
-- --                            (λ x → b (fst (rot≃ e0) (suc x)))))
-- --                       ∙ toFM2≡Punch e0 b))
-- --         (cong (b ((fst (rot≃ e1) zero)) ∷2_) (toFM2≡Punch e0' (λ x → b (fst (rot≃ e1) (suc x))))
-- --                    ∙ toFM2≡Punch e1 b)
-- --         ((cong (fst ∘ tabulateFM2OfLen ∘ (b ∘_)) (cong fst x))) refl)
-- --       (lemmSq _ b) (λ e0 e1 p → symP (lemmSq2 _ b e1 e0 p))
-- --       (fst e zero) (fst e one) ((znots ∘ invEq (congEquiv e)))


-- --   toFM2≡Step : ∀ n  → (k : Fin n) →
-- --            (e : Fin (suc n) ≃ Fin (suc n)) → (b : Fin (suc n) → A) →
-- --               Path (fst (tabulateFM2OfLen (b ∘ fst e ∘ fst (adjTransposition k)))
-- --                     ≡ fst (tabulateFM2OfLen b))
-- --                     (toFM2≡adjT k (b ∘ fst e) ∙ toFM2≡U b e)
-- --                     (toFM2≡U b (adjTransposition k ∙ₑ e) )

-- --   toFM2≡Step .(suc (suc n)) (suc {suc n} k) e b = 
-- --     let (e' , p') = unwindPermHead e
-- --         (e* , p*) = unwindPermHead ((adjTransposition (suc k) ∙ₑ e))
-- --         e0 = fst e zero
-- --         p*= = unwindPermHeadCompAdjTranspFST' _ k e
-- --         pX = _
-- --     in (cong (toFM2≡adjT (suc k) (b ∘ fst e) ∙_) (assoc _ _ _) ∙ assoc _ _ _)
-- --        ∙ cong (_∙ toFM2≡Punch e0 b)
-- --          (_
-- --           ≡⟨ assoc _ _ pX ⟩ _
-- --           ≡⟨ cong (_∙ pX) ( homotopyNatural (λ a → toFM2≡adjT (suc k) (b ∘ fst a)) p') ⟩ _
-- --           ≡⟨ sym (assoc _ _ _) ⟩ _
-- --           ≡⟨ cong ((cong (λ e → fst (tabulateFM2OfLen (λ x → (b ∘ fst e) (x))))
-- --              ((cong ((adjTransposition (suc k)) ∙ₑ_) p'))) ∙_)
-- --               (sym (cong-∙ (((b (fst (rot≃ e0) zero) ∷2_)))
-- --                  (toFM2≡adjT k (((λ x → b (fst (rot≃ (fst e zero)) (suc x)))) ∘ fst e') )
-- --                   (toFM2≡U (λ x → b (fst (rot≃ (fst e zero)) (suc x))) e'))
-- --                 ∙ cong (λ y → (cong (b (fst (rot≃ e0) zero) ∷2_) y ))
-- --                 (toFM2≡Step (suc n) k e' _ ) ) ⟩ _
-- --           ≡⟨ (λ i → (cong (λ e → fst (tabulateFM2OfLen (λ x → (b ∘ fst e) (x)))) (p*= i))
-- --                   ∙ (cong (b (fst (rot≃ e0) zero) ∷2_)
-- --                   (toFM2≡U (b ∘ fst (rot≃ e0)
-- --                         ∘ suc) (unwindPermHeadCompAdjTranspFST k e i)))) ⟩ _ ∎  )
-- --        ∙ sym (assoc _ _ _)

-- --   toFM2≡Step .(suc n) (zero {n}) e b =
-- --      let (e' , p') = unwindPermHead e
-- --          e0 = fst e zero
-- --          (e'' , p'') = unwindPermHead e'
-- --          (e'* , p'*) = unwindPermHead (adjTransposition zero ∙ₑ e)
-- --          e1 = fst e one
-- --          (e''* , p''*) = unwindPermHead e'*
-- --          e0*' = fst e'* zero
-- --          w0 = _
-- --          w1 = _
-- --          w2 = _
-- --          w3 = _
-- --          w4 = _
-- --          w5 = _
-- --          w6 = _
-- --          w7 = _
-- --          w8 = cong (λ e → fst (tabulateFM2OfLen (λ x → (b ∘ fst e ∘ swap0and1) (x)))) p'

         
-- --          w10 = cong (λ e → fst (tabulateFM2OfLen (λ x → (b ∘ (fst (rot≃ e0)) ∘ e 
-- --                     ∘ swap0and1) (x))))
-- --                    (cong (fst ∘ sucPerm) p'')
                     

-- --          w12 = cong
-- --            (λ x →
-- --               b
-- --               (fst (rot≃ (fst e zero))
-- --                (suc
-- --                 (fst (rot≃ (fst e' zero)) zero)))
-- --               ∷2 b (fst (rot≃ (fst e zero)) zero) ∷2 x)
-- --            (toFM2≡U
-- --             (λ x →
-- --                b
-- --                (fst (rot≃ (fst e zero))
-- --                 (suc
-- --                  (fst (rot≃ (fst e' zero))
-- --                   (suc x)))))
-- --             (fst (unwindPermHead (fst (unwindPermHead e)))))
-- --          w13 = comm _ _ _

-- --          qF0 = (λ e → fst (tabulateFM2OfLen
-- --                          (λ x → (b ∘ fst (rot≃ e1) ∘ suc ∘ fst e) (x))))
-- --          q0 = cong (λ e → fst (tabulateFM2OfLen (λ x → (b ∘ fst e) (x)))) p'*
-- --          qk0 = ((fst (rot≃ (fst e one)) zero))
-- --          qk1 = fst (rot≃ (fst e one))
-- --                  (suc
-- --                   (fst
-- --                    (sucPerm
-- --                     (fst
-- --                      (unwindPermHead
-- --                       (fst (unwindPermHead (adjTransposition zero ∙ₑ e)))))
-- --                     ∙ₑ
-- --                     rot≃
-- --                     (equivFun (fst (unwindPermHead (adjTransposition zero ∙ₑ e)))
-- --                      zero))
-- --                    zero))
-- --          q1 = (toFM2≡U (b ∘ fst (rot≃ e1) ∘ suc
-- --                                      ∘ fst (rot≃ e0*') ∘ suc ) e''*)

-- --          w11 = cong (b (fst (rot≃ (fst e zero)) zero) ∷2_)
-- --                    (toFM2≡Punch
-- --                    (predFin
-- --                     (snd (rot≃ (fst e zero)) .equiv-proof (e .fst one) .fst .fst))
-- --                    (λ x → b (fst (rot≃ (fst e zero)) (suc x))))
-- --          w9 = toFM2≡Punch (fst e zero) b

-- --          q4 = toFM2≡Punch e0*' (b ∘ fst (rot≃ e1) ∘ suc)
-- --          q5 = toFM2≡Punch e1 b



-- --          q0' = cong ((λ e → fst (tabulateFM2OfLen (λ x → (b ∘ e) (x)))))
-- --                    ((cong fst p'*) ∙
-- --                    (cong (λ e → fst ((sucPerm e) ∙ₑ (rot≃ e1))) p''*))
-- --          qq' : q0' ≡ q0 ∙ cong (b qk0 ∷2_) (cong qF0 p''*)
-- --          qq' = cong-∙ ((λ e → fst (tabulateFM2OfLen (λ x → (b ∘ e) (x)))))
-- --                    (cong fst p'*)
-- --                    (cong (λ e → fst ((sucPerm e) ∙ₑ (rot≃ e1))) p''*)

-- --          w8w10 = _
-- --          w8w10P : w8 ∙ w10 ≡ w8w10
-- --          w8w10P = sym (cong-∙ --{x = swap0and1≃ ∙ₑ e}
-- --                               -- {z = {!!}}
-- --                         ((λ e → fst (tabulateFM2OfLen (λ x → (b (e x))))))
-- --                    (cong (λ x → fst (swap0and1≃ ∙ₑ x)) p')
-- --                    ((cong (λ x → fst (swap0and1≃ ∙ₑ sucPerm x ∙ₑ rot≃ e0)) p'')))

-- --          lSqP : _
-- --          lSqP = 
-- --              cong (fst ∘ tabulateFM2OfLen ∘ (b ∘_))
-- --                (cong fst (unwindPermHeadCompSwap0and1 e))


-- --          lSq : Square
-- --                    (w8w10 ∙ w12)
-- --                    (q0' ∙ cong (b qk0 ∷2_) (cong (b qk1 ∷2_) q1))
-- --                    refl
-- --                     lSqP
-- --          lSq = cong (toFM2≡Step0lem b (swap0and1≃ ∙ₑ e))
-- --                  (Σ≡Prop {A = (Fin n ≃  Fin n) × (Fin (suc (suc n)) → Fin (suc (suc n)))}
-- --                     {B = λ (e' , e'') → fst (swap0and1≃ ∙ₑ e) ≡ e'' ∘ fst (sucPerm (sucPerm  e'))}
-- --                    ((λ (e' , e'') → isOfHLevelΠ 2 (λ _ → isSetFin) (fst (swap0and1≃ ∙ₑ e))
-- --                      (e'' ∘ fst (sucPerm (sucPerm  e')))))
-- --                    {(fst (unwindPermHead (fst (unwindPermHead e)))
-- --                    , fst (swap0and1≃ ∙ₑ
-- --                            sucPerm (rot≃ (predFin (invEq (rot≃ (fst e zero)) (equivFun e one))))
-- --                         ∙ₑ rot≃ (equivFun e zero)))
-- --                    , λ { i zero → ((cong (λ x → fst (swap0and1≃ ∙ₑ x)) p') ∙ 
-- --                    ((cong (λ x → fst (swap0and1≃ ∙ₑ sucPerm x ∙ₑ rot≃ e0)) p''))) i zero
-- --                       ; i one → ((cong (λ x → fst (swap0and1≃ ∙ₑ x)) p') ∙ 
-- --                    ((cong (λ x → fst (swap0and1≃ ∙ₑ sucPerm x ∙ₑ rot≃ e0)) p''))) i one
-- --                       ; i (suc (suc k)) → ((cong (λ x → fst (swap0and1≃ ∙ₑ x)) p') ∙ 
-- --                    ((cong (λ x → fst (swap0and1≃ ∙ₑ sucPerm x ∙ₑ rot≃ e0)) p''))) i (suc (suc k))
-- --                       }}
-- --                    {(fst (unwindPermHead (fst (unwindPermHead (swap0and1≃ ∙ₑ e))))
-- --                    , (fst (sucPerm (rot≃ (predFin (invEq (rot≃ (fst e one)) (equivFun e zero))))
-- --                      ∙ₑ rot≃ (equivFun e one))))
-- --                    , λ { i zero → ((cong fst p'*) ∙
-- --                    (cong (λ e → fst ((sucPerm e) ∙ₑ (rot≃ e1))) p''*)) i zero
-- --                       ; i one → ((cong fst p'*) ∙
-- --                    (cong (λ e → fst ((sucPerm e) ∙ₑ (rot≃ e1))) p''*)) i one
-- --                       ; i (suc (suc k)) → ((cong fst p'*) ∙
-- --                    (cong (λ e → fst ((sucPerm e) ∙ₑ (rot≃ e1))) p''*)) i (suc (suc k))
-- --                       }}
-- --                    (ΣPathP (unwindPermHeadCompSwap0and1FST e
-- --                            , cong fst (unwindPermHeadCompSwap0and1 e))))

-- --          rSq : Square
-- --                    (((w13 ∙ w11) ∙ w9))
-- --                    ((cong (b qk0 ∷2_) q4 ∙ q5))
                   
-- --                     lSqP
-- --                     refl
-- --          rSq = lemmSq' n e b


-- --      in assoc _ _ w0 ∙
-- --         cong (_∙ w0) (homotopyNatural (λ e → toFM2≡adjT zero (b ∘ fst e)) p')
-- --         ∙ sym (assoc w1 w3 _)
-- --         ∙ cong (w1 ∙_) (assoc _ _ w2 ∙
-- --           cong (_∙ w2) (cong (w3 ∙_)
-- --              (cong {x = (toFM2≡U (b ∘ fst (rot≃ e0) ∘ suc ) e')}
-- --              (cong (b ((fst (rot≃ (fst e zero)) zero)) ∷2_)) (assoc _ _ _)
-- --              ∙ cong-∙ (b ((fst (rot≃ (fst e zero)) zero)) ∷2_) (w5 ∙ w6) _)
-- --              ∙ (λ i → assoc w3 (cong-∙ (b ((fst (rot≃ (fst e zero)) zero)) ∷2_) w5 w6 i) w4 i)
-- --              ∙ cong (_∙ w4) (assoc _ _ _ ∙
-- --                   cong (_∙ (cong (b ((fst (rot≃ (fst e zero)) zero)) ∷2_) w6))
-- --                      (homotopyNatural ((λ ee → toFM2≡adjT zero (b ∘ fst (sucPerm ee ∙ₑ
-- --                         (((rot≃ (fst e zero)))))))) p'')
-- --                      ∙ sym (assoc w7 _ _)
-- --                      ∙ cong (w7 ∙_) (comm-over (toFM2≡U _ e'') _ _))))
-- --         ∙ ( (w8 ∙ ((w10 ∙ (w12 ∙ w13)) ∙ w11) ∙ w9)
-- --            ≡⟨ cong (λ x → (w8 ∙ x ∙ w9)) (cong (_∙ w11) (assoc _ _ _) ∙ sym (assoc _ _ _))
-- --               ∙ cong (w8 ∙_) (sym (assoc _ _ _)) ∙ assoc _ _ _ ⟩
-- --            ((w8 ∙ w10 ∙ w12) ∙ ((w13 ∙ w11) ∙ w9))
           
-- --            ≡⟨ cong (_∙ ((w13 ∙ w11) ∙ w9)) (assoc _ _ _ ∙ cong (_∙ w12) w8w10P)  ⟩
-- --              (w8w10 ∙ w12) ∙ ((w13 ∙ w11) ∙ w9)
-- --            ≡⟨ (λ i → (lSq i) ∙ (rSq i)) ⟩
-- --             (q0'
-- --               ∙ cong (b qk0 ∷2_) (cong (b qk1 ∷2_) q1)) 
-- --               ∙ (cong (b qk0 ∷2_) q4 ∙ q5)
-- --            ≡⟨ cong (_∙ (cong (b qk0 ∷2_) q4 ∙ q5))
-- --               ( cong (_∙ cong (b qk0 ∷2_) (cong (b qk1 ∷2_) q1)) qq' ∙ (sym (assoc _ _ _))) ⟩
-- --             (q0
-- --               ∙ cong (b qk0 ∷2_) (cong qF0 p''*)
-- --               ∙ cong (b qk0 ∷2_) (cong (b qk1 ∷2_) q1)) 
-- --               ∙ (cong (b qk0 ∷2_) q4 ∙ q5)
-- --            ≡⟨ (cong (_∙ (cong (b qk0 ∷2_) q4 ∙ q5))
-- --                 (cong (q0 ∙_) (sym (cong-∙ (b qk0 ∷2_)
-- --                   (cong qF0 p''*) (cong (b qk1 ∷2_) q1))))) ∙ sym (assoc _ _ _) ∙ cong (q0 ∙_)
-- --                (assoc _ _ _ ∙ cong (_∙ q5) (sym (cong-∙ (b qk0 ∷2_) (cong qF0 p''* ∙ cong (b qk1 ∷2_) q1) q4)
-- --                ∙ cong (cong (b qk0 ∷2_)) (sym (assoc _ _ _)) )) ⟩ 
-- --              q0 ∙ cong (b qk0 ∷2_)
-- --                   (cong qF0 p''* ∙ cong (b qk1 ∷2_) q1 ∙ q4)
-- --              ∙ q5
-- --             ∎ )
        

-- --   toFM2≡U∙ : ∀ n  →
-- --            (f : Fin n ≃ Fin n) → (b : Fin n → A) → (e : Fin n ≃ Fin n) → 
-- --               Path (fst (tabulateFM2OfLen (b ∘ fst f ∘ fst e)) ≡ fst (tabulateFM2OfLen b))
-- --                     (toFM2≡U (b ∘ fst f) e ∙ toFM2≡U b f)
-- --                     (toFM2≡U b (e ∙ₑ f) )
-- --   toFM2≡U∙ zero f b e = sym compPathRefl
-- --   toFM2≡U∙ (suc n) f b = 
-- --     GeneratedElimConstr'
-- --     (SymData (suc n) )
-- --     (generatedSym n)
-- --     _
-- --     (cong (_∙ toFM2≡U b f) (toFM2≡Uid (b ∘ (fst f))) ∙
-- --               (λ i → sym (lUnit (toFM2≡U b (compEquivIdEquiv f (~ i)) )) i))
-- --     λ k e P → (cong (_∙ toFM2≡U b f) (sym (toFM2≡Step n k e (b ∘ fst f))) ∙ sym (assoc _ _ _))
-- --            ∙∙  cong (toFM2≡adjT k (b ∘ fst f ∘ fst e) ∙_) (P) ∙∙
-- --           ((toFM2≡Step n k (e ∙ₑ f) b) ∙ cong (toFM2≡U b) (compEquiv-assoc _ _ _))

  


-- --   toFM2≡ : ∀ n → {a b : Fin n → A} →
-- --            a ↔ₙ b → fst (tabulateFM2OfLen a) ≡ fst (tabulateFM2OfLen b)
-- --   toFM2≡ zero {a} {b} (prm e p) = refl
-- --   toFM2≡ (suc n) {a} {b} (prm e p) = cong (fst ∘ (tabulateFM2OfLen)) p ∙ toFM2≡U b e

-- --   tab-coh : ∀ n → (a b c : Fin n → A)
-- --      → (r : a ↔ₙ b) (s : b ↔ₙ c) →
-- --               toFM2≡ n r ∙ (toFM2≡ n s) ≡
-- --               toFM2≡ n (isTrans↔ₙ n a b c r s)
-- --   tab-coh zero a b c _ _ = sym compPathRefl
-- --   tab-coh (suc n) a b c (prm e p) (prm f q) =
-- --      assoc _ _ _ ∙
-- --       cong (_∙ toFM2≡U c f)
-- --        (sym (assoc _ _ _)
-- --         ∙ cong ( (cong (fst ∘ (tabulateFM2OfLen)) p) ∙_)
-- --           ( homotopyNatural (λ x → toFM2≡U x e) q )
-- --         ∙ assoc _ _ _
-- --         ∙ cong (_∙ (toFM2≡U (c ∘ fst f) e))
-- --          (sym (cong-∙ (fst ∘ (tabulateFM2OfLen)) p (cong (_∘ fst e) q))))
-- --       ∙ sym (assoc _ _ _)
-- --      ∙ cong ((cong (fst ∘ (tabulateFM2OfLen)) (p ∙ (cong (_∘ fst e) q) )) ∙_)
-- --           (toFM2≡U∙ _ f c e)

-- --   _∙∙P_∙∙P_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
-- --                (p : w ≡ x)
-- --                (q : x ≡ y)
-- --                (r : y ≡ z)
-- --                → w ≡ z

-- --   _∙∙P_∙∙P_ {A = A} p q r i =
-- --     comp (λ _ → A) (doubleComp-faces p r i) (q i)


-- --   fixComp : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
-- --                (p : w ≡ x)
-- --                (q : x ≡ y)
-- --                (r : y ≡ z)
-- --                → (p ∙∙ q ∙∙ r) ≡ p ∙∙P q ∙∙P r 
-- --   fixComp {A = A} p q r j i =
-- --          hcomp
-- --          (doubleComp-faces (λ i₁ → transp (λ _ → A) (~ j ∨ ~ i₁) (p i₁))
-- --           (λ i₁ → transp (λ _ → A) (~ j ∨ i₁) (r i₁)) i)
-- --          (transp (λ _ → A) (~ j) (q i))



-- --   Σ≡Prop∙ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : (a : A) → Type ℓ'}
-- --           (pB : (x : A) → isProp (B x)) → {u v w : Σ A B}
-- --             → (p : u .fst ≡ v .fst) → (q : v .fst ≡ w .fst) →
-- --                Σ≡Prop pB {u} {v} p ∙ Σ≡Prop pB {u = v} {v = w} q
-- --              ≡ Σ≡Prop pB (p ∙ q)
-- --   fst (Σ≡Prop∙ pB p q i i₁) = fixComp refl p q (~ i) i₁ 
-- --   snd (Σ≡Prop∙ pB {u} {v} {w} p q i i₁) = 
-- --      isSet→SquareP (λ i i₁ → isProp→isSet (pB (fixComp refl p q (~ i) i₁)))
-- --         (cong snd (Σ≡Prop pB {u} {v} p ∙ Σ≡Prop pB {u = v} {v = w} q))
-- --         (cong snd (Σ≡Prop pB (p ∙ q)))
-- --         refl refl i i₁

-- --   -- toFM2R : ? 
-- --   -- toFM2R = ? 

-- --   toFM2r : ∀ n → GQ.Rrec (FMSet2OfLen A n)
-- --   Rrec.Bgpd (toFM2r n) = isGroupoidFMSet2OfLen n
-- --   Rrec.fb (toFM2r n) = tabulateFM2OfLen
-- --   Rrec.feq (toFM2r n) = FMSet2OfLen≡ ∘ toFM2≡ n
-- --   Rrec.fsq (toFM2r n) = λ r s → compPath-filler _ _ ▷
-- --      (Σ≡Prop∙ (λ _ → isSetℕ _ _) _ _
-- --        ∙ cong FMSet2OfLen≡ (tab-coh n _ _ _ r s))


-- --   toFM2 : ∀ n → Fin→//↔ n → FMSet2OfLen A n
-- --   toFM2 n = GQ.Rrec.f (toFM2r n)
  
-- --   module _ (x : A) where 
-- --     rAppend : ∀ n → GQ.Rrec {Rt = isTrans↔ₙ n} (Fin→//↔ (suc n))
-- --     Rrec.Bgpd (rAppend n) = squash//
-- --     (Rrec.fb (rAppend n)) f = [ cons→ x f ]//
-- --     (Rrec.feq (rAppend n)) (prm e p) = eq// (prm (sucPerm e) (refl =→ p))
-- --     (Rrec.fsq (rAppend n)) {a} {b} {c} (prm e p) (prm f q) =
-- --       comp// (prm (sucPerm e) ((refl =→ p)))
-- --                     (prm (sucPerm f) ((refl =→ q)))
-- --           ▷ cong eq// h

-- --      where
-- --       h :  _ 
-- --       h i = prm (respectsCompSucPerm e f i) (hh i)
-- --         where
-- --           hh : PathP (λ i → cons→ x a ≡ cons→ x c ∘ fst (respectsCompSucPerm e f i))
-- --                   (((refl {x = x}) =→ p) ∙
-- --                        cong {x = cons→ x b}
-- --                             {y = cons→ x c ∘ fst (sucPerm f)}
-- --                           ((_∘ fst (sucPerm (e)))) ((refl {x = x}) =→ q))
-- --                   (refl =→ (p ∙ cong (_∘ fst e) q))

-- --           hh i j zero = compPathRefl {x = x} (~ i) j
-- --           hh i j (suc x) = (p ∙ cong (_∘ (fst e)) q) j x


-- --   append→ : ∀ {n} → (x : A) →
-- --                Fin→//↔ n → Fin→//↔ (suc n)
-- --   append→ {n} x = GQ.Rrec.f (rAppend x n)
-- --     -- where


-- --   appendComm : ∀ {n} → (x y : A) → (b : Fin→//↔ n) →
-- --                  (append→ x (append→ y b)) ≡ (append→ y (append→ x b))
-- --   appendComm {n} x y = RelimSet.f r
-- --     where
-- --      r : RelimSet _
-- --      (RelimSet.truncB r) _ = squash// _ _
-- --      (RelimSet.fb r) _ = eq// (prm swap0and1≃ (refl =→ refl =→ refl))
-- --      RelimSet.fbEq r = h n
-- --        where
-- --        h' : ∀ n → {a b : Fin n → A} (r : a ↔ₙ b)
-- --              → 
-- --                  ((eq//
-- --                    (prm swap0and1≃
-- --                     ((λ _ → cons→ x (cons→ y a) zero) =→
-- --                      (λ _ → (cons→ x (cons→ y a) ∘ suc) zero) =→
-- --                      (λ _ → (cons→ x (cons→ y a) ∘ suc) ∘ suc))))
-- --                       ∙ (λ i → append→ y (append→ x (eq// r i)))) ≡ 
-- --                  ((λ i → append→ x (append→ y (eq// r i))) ∙ (eq//
-- --                    (prm swap0and1≃
-- --                     ((λ _ → cons→ x (cons→ y b) zero) =→
-- --                      (λ _ → (cons→ x (cons→ y b) ∘ suc) zero) =→
-- --                      (λ _ → (cons→ x (cons→ y b) ∘ suc) ∘ suc)))))
                 
                 
-- --        h' n {a} {b} r =
-- --          sym (comp'// _ _ _ _ )
-- --           ∙ cong eq// hh
-- --           ∙ comp'// _ _ _ _
-- --          where
-- --            hh : isTrans↔ₙ (suc (suc n)) (cons→ x (cons→ y a)) (cons→ y (cons→ x a))
-- --                   (cons→ y (cons→ x b))
-- --                   (prm swap0and1≃
-- --                    ((λ _ → cons→ x (cons→ y a) zero) =→
-- --                     (λ _ → (cons→ x (cons→ y a) ∘ suc) zero) =→
-- --                     (λ _ → (cons→ x (cons→ y a) ∘ suc) ∘ suc)))
-- --                   (prm (sucPerm (sucPerm (F≃ r)))
-- --                    ((λ _ → cons→ y (cons→ x a) zero) =→
-- --                     (λ _ → cons→ x a zero) =→ l≡ r))
-- --                   ≡
-- --                   isTrans↔ₙ (suc (suc n)) (cons→ x (cons→ y a)) (cons→ x (cons→ y b))
-- --                   (cons→ y (cons→ x b))
-- --                   (prm (sucPerm (sucPerm (F≃ r)))
-- --                    ((λ _ → cons→ x (cons→ y a) zero) =→
-- --                     (λ _ → cons→ y a zero) =→ l≡ r))
-- --                   (prm swap0and1≃
-- --                    ((λ _ → cons→ x (cons→ y b) zero) =→
-- --                     (λ _ → (cons→ x (cons→ y b) ∘ suc) zero) =→
-- --                       (λ _ → (cons→ x (cons→ y b) ∘ suc) ∘ suc)))
-- --            F≃ (hh i) = commSwap0and1SucSuc (F≃ r) i
-- --            l≡ (hh i) j zero = (refl {x = x} ∙ refl) j
-- --            l≡ (hh i) j one = (refl {x = y} ∙ refl) j
-- --            l≡ (hh i) j (suc (suc x)) = 
-- --              (sym (lUnit (λ j → l≡ r j x)) ∙ rUnit λ j → l≡ r j x) i j

-- --        h : ∀ n → {a b : Fin n → A} (r : a ↔ₙ b)
-- --              → Square
-- --                  (eq//
-- --                    (prm swap0and1≃
-- --                     ((λ _ → cons→ x (cons→ y a) zero) =→
-- --                      (λ _ → (cons→ x (cons→ y a) ∘ suc) zero) =→
-- --                      (λ _ → (cons→ x (cons→ y a) ∘ suc) ∘ suc))))
-- --                  (eq//
-- --                    (prm swap0and1≃
-- --                     ((λ _ → cons→ x (cons→ y b) zero) =→
-- --                      (λ _ → (cons→ x (cons→ y b) ∘ suc) zero) =→
-- --                      (λ _ → (cons→ x (cons→ y b) ∘ suc) ∘ suc))))
-- --                  (λ i → append→ x (append→ y (eq// r i)))
-- --                  λ i → append→ y (append→ x (eq// r i))
-- --        h n r = ∙≡∙→square _ _ _ _ (h' n r)



-- --   appendSym : ∀ n → (x y : A) (xs : Fin→//↔ n)  →
-- --       SquareP (λ i j → Fin→//↔ (2 + n))
-- --       (appendComm x y xs) (symP (appendComm y x xs)) refl refl
-- --   appendSym n x y = GQ.RelimProp.f r
-- --     where
-- --       r : GQ.RelimProp _
-- --       (RelimProp.truncB r) _ = squash// _ _ _ _
-- --       (RelimProp.fb r) a = 
-- --               rUnit (appendComm x y [ a ]//) ∙
-- --            (cong ((appendComm x y [ a ]//) ∙_) (sym (rCancel (appendComm y x [ a ]//)))
-- --              ∙  (assoc _ _ _))
-- --              ∙ cong′ (_∙ (sym (appendComm y x [ a ]//)))
-- --             (sym (comp'// _ _ _ _) ∙
-- --             (cong′ eq// λ i → prm (swap0and1≃²=idEquiv i) (zz' i)) ∙
-- --               refl≡Id _ (isRefl↔ₙ (suc (suc n)) (cons→ x (cons→ y a) ))
-- --                    λ i → prm ((equivEq {e = idEquiv _ ∙ₑ idEquiv _} {f = idEquiv _} refl) i)
-- --                       ((sym (compPathRefl {x = (cons→ x (cons→ y a))})) i)
-- --             ) ∙ sym (lUnit _) 

-- --          where
-- --            zzz : _
-- --            zzz = (isTrans↔ₙ (suc (suc n)) (cons→ x (cons→ y a))
-- --                    (cons→ y (cons→ x a)) (cons→ x (cons→ y a))
-- --                    (prm swap0and1≃
-- --                     ((λ _ → cons→ x (cons→ y a) zero) =→
-- --                      (λ _ → (cons→ x (cons→ y a) ∘ suc) zero) =→
-- --                      (λ _ → (cons→ x (cons→ y a) ∘ suc) ∘ suc)))
-- --                    (prm swap0and1≃
-- --                     ((λ _ → cons→ y (cons→ x a) zero) =→
-- --                      (λ _ → (cons→ y (cons→ x a) ∘ suc) zero) =→
-- --                      (λ _ → (cons→ y (cons→ x a) ∘ suc) ∘ suc))))

-- --            zz' : PathP
-- --              (λ i → cons→ x (cons→ y a) ≡ cons→ x (cons→ y a) ∘ fst ((swap0and1≃²=idEquiv i)) )
-- --              (_↔ₙ_.l≡ zzz)
-- --              (λ _ → cons→ x (cons→ y a))
-- --            zz' = symP (compPathRefl sq→ compPathRefl sq→ compPathRefl)



-- --   appendDiag : ∀ {n} → (x y z : A) → (b : Fin→//↔ n) →
-- --                  (append→ x (append→ y (append→ z b)))
-- --                ≡ (append→ z (append→ y (append→ x b)))
-- --   appendDiag {n} x y z = RelimSet.f r'
-- --     where
-- --      r' : RelimSet _
-- --      RelimSet.truncB r' = (λ _ → squash// _ _)
-- --      RelimSet.fb r' = (λ a → eq// (prm swap0and2≃ (refl =→ refl =→ refl =→ refl)))
-- --      (RelimSet.fbEq r') {a} {b} r =
-- --        ∙≡∙→square _ _ _ _ (sym (comp'// _ _ _ _ )
-- --           ∙ cong′ eq// (w)
-- --           ∙ comp'// _ _ _ _)

-- --         where
-- --           w : isTrans↔ₙ _
-- --                        (cons→ x (cons→ y (cons→ z a)))
-- --                        (cons→ z (cons→ y (cons→ x a)))
-- --                        (cons→ z (cons→ y (cons→ x b)))
-- --                        (prm _ (refl =→  refl =→ refl =→ refl))
-- --                        (prm _ ((λ _ → z) =→ (λ _ → y) =→ (λ _ → x) =→ l≡ r))
-- --                        ≡ _
-- --           F≃ (w i) = equivEq {e = swap0and2≃ ∙ₑ sucPerm (sucPerm (sucPerm (F≃ r)))}
-- --                                {f = sucPerm (sucPerm (sucPerm (F≃ r))) ∙ₑ swap0and2≃}
-- --                         (refl =→ refl =→ refl =→ refl) i
-- --           l≡ (w i) j zero = (refl {x = x} ∙ refl) j
-- --           l≡ (w i) j one = (refl {x = y} ∙ refl) j
-- --           l≡ (w i) j two = (refl {x = z} ∙ refl) j
-- --           l≡ (w i) j (suc (suc (suc x))) = 
-- --             (sym (lUnit (λ j → l≡ r j x)) ∙ rUnit λ j → l≡ r j x) i j
         
-- --   appendHexU : ∀ n → ∀ (x y z : A) (b : Fin→//↔ n) →
-- --       Square {A = Fin→//↔ (suc (suc (suc n)))}
-- --       (cong (append→ y) (appendComm x z b)) (appendDiag x y z b)
-- --       (appendComm y x (append→ z b)) (appendComm y z (append→ x b))
-- --   appendHexU n x y z = ∙≡∙→square _ _ _ _ ∘
-- --     GQ.RelimProp.f r

-- --     where
-- --      r : GQ.RelimProp _
-- --      (RelimProp.truncB r) _ = squash// _ _ _ _
-- --      (RelimProp.fb r) _ =
-- --         (sym (comp'// _ _ _ _) ∙∙
-- --             cong eq// (cong₂'
-- --              prm
-- --               (equivEq (refl =→ refl =→ refl =→ refl))
-- --               (refl sq→ refl sq→ refl sq→ refl  ))
-- --           ∙∙ (comp'// _ _ _ _))


-- --   appendHexL : ∀ n → ∀ (x y z : A) (b : Fin→//↔ n) →
-- --       Square (appendDiag x y z b) (appendComm x z (append→ y b))
-- --       (congP (λ _ → append→ x) (appendComm y z b))
-- --       (congP (λ _ → append→ z) (appendComm y x b))  --     Square {A = Fin→//↔ (suc (suc (suc n)))}

-- --   appendHexL n x y z = ∙≡∙→square _ _ _ _ ∘
-- --     GQ.RelimProp.f r

-- --     where
-- --      r : GQ.RelimProp _
-- --      (RelimProp.truncB r) _ = squash// _ _ _ _
-- --      (RelimProp.fb r) _ =
-- --         (sym (comp'// _ _ _ _) ∙∙
-- --             cong eq// (cong₂'
-- --              prm
-- --               (equivEq (refl =→ refl =→ refl =→ refl))
-- --               (refl sq→ refl sq→ refl sq→ refl  ))
-- --           ∙∙ (comp'// _ _ _ _))



-- --   fromFM2 : (l : FMSet2 A) → Fin→//↔ (len2 l)
-- --   fromFM2 = FM2.RElim.f rFrom

-- --     where
-- --       rFrom : FM2.RElim (λ (l : FMSet2 A) → Fin→//↔ (len2 l))
-- --       RElim.[]* rFrom = [ (λ ()) ]//
-- --       RElim._∷*_ rFrom = λ a → append→ a
-- --       RElim.comm* rFrom = λ x y {xs} b → appendComm x y b
-- --       RElim.comm-inv* rFrom = λ x y b → appendSym _  x y b
-- --       RElim.hexDiag* rFrom = λ x y z b → appendDiag x y z b
-- --       RElim.hexU* rFrom = λ x y z {xs} b → appendHexU (len2 xs) x y z b
-- --       RElim.hexL* rFrom = λ x y z {xs} b → appendHexL (len2 xs) x y z b
-- --       RElim.trunc* rFrom = λ _ → squash// 



-- -- -- -- -----------------------------------------------






-- -- -- --   -- fromFM2 : (l : FMSet2 A) → Fin→//↔ (len2 l)
-- -- -- --   -- fromFM2 =
-- -- -- --   --   (FM2.Elim.f
-- -- -- --   --    [ (λ ()) ]//
-- -- -- --   --    (λ a → append→ a)
-- -- -- --   --    (λ x y {xs} b → appendComm x y b)
-- -- -- --   --    (λ x y b → appendSym _  x y b)
-- -- -- --   --    (λ x y z b → appendDiag x y z b)
-- -- -- --   --    {!!}
-- -- -- --   --    {!!}
-- -- -- --   --     λ _ → squash// )

-- -- -- --   -- lem-toFM2from' : ∀ n → (x : A) → (xs : Fin→//↔ n) →
-- -- -- --   --     fst (toFM2 (suc n) (append→ x xs)) ≡
-- -- -- --   --       x ∷2 fst (toFM2 n xs)
-- -- -- --   -- lem-toFM2from' n x =
-- -- -- --   --   GQ.elimSet _ (λ _ → trunc _ _)
-- -- -- --   --    (λ a → refl) λ r → {!!}


-- -- -- --   -- toFM2from' : ∀ (x : FMSet2 A) → (fst (toFM2 (len2 x) (fromFM2 x))) ≡ x
-- -- -- --   -- toFM2from' = FM2.ElimSet.f
-- -- -- --   --   refl
-- -- -- --   --   (λ x {xs} x₁ →
-- -- -- --   --         (?
-- -- -- --   --           ∙ lem-toFM2from' (len2 xs) x (fromFM2 xs)) ∙ cong (x ∷2_) x₁
-- -- -- --   --     -- (fst (toFM2 (len2 (x ∷2 xs)) (fromFM2 (x ∷2 xs)))
-- -- -- --   --     --   -- ≡⟨ refl ⟩
-- -- -- --   --     --   --   fst (toFM2 (len2 (x ∷2 xs)) ((append→ {n = len2 xs} x (fromFM2 xs))))
-- -- -- --   --     --   ≡⟨ {!refl!} ⟩
-- -- -- --   --     --     fst (toFM2 (suc (len2 xs)) ((append→ {n = len2 xs} x (fromFM2 xs))))
-- -- -- --   --     --   ≡⟨ lem-toFM2from' (len2 xs) x (fromFM2 xs)  ⟩ 
-- -- -- --   --     --   x ∷2 fst (toFM2 (len2 xs) (fromFM2 xs)) ∎)
-- -- -- --   --     --  ∙ cong (x ∷2_) x₁
-- -- -- --   --      )
-- -- -- --   --   {!!}
-- -- -- --   --   {!!}
-- -- -- --   --   λ _ → trunc _ _ 



-- -- -- -- -- symP (compPathRefl sq→ compPathRefl sq→ compPathRefl) 




-- -- -- --   -- fromFM2 : (l : FMSet2 A) → Fin→//↔ (len2 l)
-- -- -- --   -- fromFM2 =
-- -- -- --   --   (FM2.Elim.f
-- -- -- --   --    [ (λ ()) ]//
-- -- -- --   --    (λ a → append→ a)
-- -- -- --   --    (λ x y {xs} b → appendComm x y b)
-- -- -- --   --    (λ x y b → appendSym _  x y b)
-- -- -- --   --    (λ x y z b → appendDiag x y z b)
-- -- -- --   --    {!!}
-- -- -- --   --    {!!}
-- -- -- --   --     λ _ → squash// )
-- -- -- --   -- fromFM2len : ∀ n → FMSet2OfLen A n → Fin→//↔ n 
-- -- -- --   -- fromFM2len n (x , p) = subst Fin→//↔ p (fromFM2 x)

-- -- -- --   -- fromFM2to : ∀ n → section (fromFM2len n) (toFM2 n)
-- -- -- --   -- fromFM2to n = GQ.elimSet _ (λ _ → squash// _ _) {!!} {!!}
  

-- -- -- -- -- -- --   -- fromFM2 : ∀ n →  FMSet2OfLen A n → Fin→//↔ n
-- -- -- -- -- -- --   -- fromFM2 n =
-- -- -- -- -- -- --   --   {!uncurry (FM2.Elim.f ? ? ? ? ? ? ? ?)!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       FM2.Rec.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        squash// [ [] ]// _∷//_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (λ x y → GQ.elimSet _ (λ _ → squash// _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (λ _ → eq// headSwap↔) (λ {a} {b} r i j → h x y {a} {b} r j i) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (λ x y → GQ.elimProp _ (λ _ → squash// _ _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (hSym x y ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}



-- -- -- -- -- -- -- -- --   -- transposeFM2 : (x : FMSet2 A) → Fin (len2 x) → singl x 
-- -- -- -- -- -- -- -- --   -- transposeFM2 = ElimSet.f
-- -- -- -- -- -- -- -- --   --    (λ _ → [] , refl)
-- -- -- -- -- -- -- -- --   --    (λ x {xs} → ElimSet.f {B = λ xs → (Fin (len2 xs) → singl xs) → Fin (suc (len2 xs))
-- -- -- -- -- -- -- -- --   --                 →  singl (x ∷2 xs)}
-- -- -- -- -- -- -- -- --   --      (λ _ _ → _ , refl)
-- -- -- -- -- -- -- -- --   --      (λ y {xs} _ g → λ {zero → (y ∷2 x ∷2 xs) , (comm x y xs)
-- -- -- -- -- -- -- -- --   --                      ; (suc k) → _ , cong (x ∷2_) (snd (g k)) })
-- -- -- -- -- -- -- -- --   --      (λ _ _ _ → isProp→PathP (λ _ → isPropΠ2 λ _ _ → isPropSingl) _ _)
-- -- -- -- -- -- -- -- --   --      (λ _ _ _ _ → isProp→PathP (λ _ → isPropΠ2 λ _ _ → isPropSingl) _ _)
-- -- -- -- -- -- -- -- --   --      (λ _ → isSetΠ2 λ _ _ → isProp→isSet (isPropSingl))
-- -- -- -- -- -- -- -- --   --      xs)
-- -- -- -- -- -- -- -- --   --   (λ _ _ _ → isProp→PathP (λ _ → isPropΠ λ _ → isPropSingl) _ _)
-- -- -- -- -- -- -- -- --   --   (λ _ _ _ _ → isProp→PathP (λ _ → isPropΠ λ _ →  isPropSingl) _ _)
-- -- -- -- -- -- -- -- --   --    λ _ → isSetΠ λ _ → isProp→isSet isPropSingl 


-- -- -- -- -- -- -- -- -- --   transposeFM2≃ : ∀ n → Fin n → singl (idEquiv (FMSet2OfLen A n))
-- -- -- -- -- -- -- -- -- --   fst (fst (transposeFM2≃ n k)) (l , p) =
-- -- -- -- -- -- -- -- -- --     let (l' , p') = transposeFM2 l (subst Fin (sym p) k)
-- -- -- -- -- -- -- -- -- --     in l' , (cong len2 (sym p')  ∙  p)
-- -- -- -- -- -- -- -- -- --   snd (fst (transposeFM2≃ n k)) = subst isEquiv
-- -- -- -- -- -- -- -- -- --     (funExt (λ (l , p) → Σ≡Prop (λ _ → isSetℕ _ _)
-- -- -- -- -- -- -- -- -- --       (snd (transposeFM2 l (subst Fin (sym p) k)))))
-- -- -- -- -- -- -- -- -- --     (idIsEquiv (FMSet2OfLen A n))

-- -- -- -- -- -- -- -- -- --   snd (transposeFM2≃ n k) = equivEq (funExt (λ (l , p) → Σ≡Prop (λ _ → isSetℕ _ _)
-- -- -- -- -- -- -- -- -- --       (snd (transposeFM2 l (subst Fin (sym p) k)))))

-- -- -- -- -- -- -- -- -- --   toFM2≡AdjTranspose :  ∀ {n} → (k : Fin n) → (a : Fin (suc n) → A)
-- -- -- -- -- -- -- -- -- --                          → fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- --                            fst (tabulateFM2OfLen (suc n) (a ∘ fst (adjTransposition k))) 
-- -- -- -- -- -- -- -- -- --   toFM2≡AdjTranspose zero a = comm _ _ _
-- -- -- -- -- -- -- -- -- --   toFM2≡AdjTranspose (suc k) a =
-- -- -- -- -- -- -- -- -- --     cong (a zero ∷2_) (toFM2≡AdjTranspose k (a ∘ suc))

-- -- -- -- -- -- -- -- -- --   toFM2≡Step : ∀ n → (k : Fin n) (e : Fin (suc n) ≃ Fin (suc n)) 
-- -- -- -- -- -- -- -- -- --        → ({a b : Fin (suc n) → A} (p : a ≡ b ∘ fst e) →
-- -- -- -- -- -- -- -- -- --                              fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- --                              fst (tabulateFM2OfLen (suc n) b))
-- -- -- -- -- -- -- -- -- --        → {a b : Fin (suc n) → A} (p : a ≡ b ∘ fst e ∘ fst (adjTransposition k)) →
-- -- -- -- -- -- -- -- -- --                              fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- --                              fst (tabulateFM2OfLen (suc n) b)
-- -- -- -- -- -- -- -- -- --   toFM2≡Step n k e x {a} {b} p =
-- -- -- -- -- -- -- -- -- --      toFM2≡AdjTranspose k a ∙ x {a ∘ (fst (adjTransposition k))} {b}
-- -- -- -- -- -- -- -- -- --           ((cong (_∘ fst (adjTransposition k)) p
-- -- -- -- -- -- -- -- -- --          ∙ cong (λ f →  b ∘ fst e ∘ fst f ) (adjTransposition²=idEquiv k)))
-- -- -- -- -- -- -- -- -- --      -- where       
-- -- -- -- -- -- -- -- -- --      --   zz : (a ∘ (fst (adjTransposition k))) ≡
-- -- -- -- -- -- -- -- -- --      --          (b ∘ (fst e ∘ (fst (idEquiv (Fin (suc n))))))
-- -- -- -- -- -- -- -- -- --      --   zz = 

-- -- -- -- -- -- -- -- -- --   -- toFM2≡ : ∀ n → {a b : Fin n → A} →
-- -- -- -- -- -- -- -- -- --   --          a ↔ₙ b → fst (tabulateFM2OfLen n a) ≡ fst (tabulateFM2OfLen n b)
-- -- -- -- -- -- -- -- -- --   -- toFM2≡ zero x = refl
-- -- -- -- -- -- -- -- -- --   -- toFM2≡ (suc n) {a} {b} (prm e p) =
-- -- -- -- -- -- -- -- -- --   --   GeneratedElimConstr'
-- -- -- -- -- -- -- -- -- --   --   (SymData (suc n) )
-- -- -- -- -- -- -- -- -- --   --   (generatedSym n)
-- -- -- -- -- -- -- -- -- --   --   (λ e → {a b : Fin (suc n) → A} (p : a ≡ b ∘ fst e) → fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- --   --                                fst (tabulateFM2OfLen (suc n) b) )
-- -- -- -- -- -- -- -- -- --   --   (cong (fst ∘ (tabulateFM2OfLen (suc n))))
-- -- -- -- -- -- -- -- -- --   --   (toFM2≡Step n) e {a} {b} p

-- -- -- -- -- -- -- -- -- --   toFM2≡L : ∀ n → (e : List (Fin n)) (a b : Fin (suc n) → A) 
-- -- -- -- -- -- -- -- -- --            (p : a ≡ b ∘ fst (concatG (SymData (suc n)) (mapList adjTransposition e)))
-- -- -- -- -- -- -- -- -- --             → fst (tabulateFM2OfLen (suc n) a) ≡ fst (tabulateFM2OfLen (suc n) b)
-- -- -- -- -- -- -- -- -- --   toFM2≡L n = ind (λ _ _ → (cong (fst ∘ (tabulateFM2OfLen (suc n)))))
-- -- -- -- -- -- -- -- -- --     λ {k} {l} x a b p →
-- -- -- -- -- -- -- -- -- --       toFM2≡Step n  k
-- -- -- -- -- -- -- -- -- --         ((concatG (SymData (suc n)) (mapList adjTransposition l)))
-- -- -- -- -- -- -- -- -- --         (λ {a} {b} → x a b) {a} {b} p 

-- -- -- -- -- -- -- -- -- --   genS : ∀ {n} → Fin (suc n) ≃ Fin (suc n) → List (Fin n)
-- -- -- -- -- -- -- -- -- --   genS = {!!}

-- -- -- -- -- -- -- -- -- --   genS= : ∀ {n} → (e : Fin (suc n) ≃ Fin (suc n)) →
-- -- -- -- -- -- -- -- -- --      (concatG (SymData (suc n)) (mapList adjTransposition (genS e))) ≡ e
-- -- -- -- -- -- -- -- -- --   genS= = {!!}


-- -- -- -- -- -- -- -- -- --   toFM2≡LCoh*' : ∀ n → (e : List (Fin n)) (a b : Fin (suc n) → A) 
-- -- -- -- -- -- -- -- -- --            (p : a ≡ b ∘ fst (concatG (SymData (suc n)) (mapList adjTransposition e)))
-- -- -- -- -- -- -- -- -- --            →
-- -- -- -- -- -- -- -- -- --               (toFM2≡L n e a b ∘ _∙ cong (b ∘_)
-- -- -- -- -- -- -- -- -- --                (cong fst (genS= ((concatG (SymData (suc n)) (mapList adjTransposition e)))))) ≡ 
-- -- -- -- -- -- -- -- -- --               ((toFM2≡L n (genS ((concatG (SymData (suc n)) (mapList adjTransposition e)))) a b))
-- -- -- -- -- -- -- -- -- --   toFM2≡LCoh*' = {!!}


-- -- -- -- -- -- -- -- -- --   toFM2≡LCoh* : ∀ n → (e : List (Fin n)) (a b : Fin (suc n) → A) 
-- -- -- -- -- -- -- -- -- --            (p : a ≡ b ∘ fst (concatG (SymData (suc n)) (mapList adjTransposition e)))
-- -- -- -- -- -- -- -- -- --            → PathP (λ i → a ≡ b ∘
-- -- -- -- -- -- -- -- -- --              (fst ((genS= ((concatG (SymData (suc n)) (mapList adjTransposition e)))) (~ i)))
-- -- -- -- -- -- -- -- -- --              → fst (tabulateFM2OfLen (suc n) a) ≡ fst (tabulateFM2OfLen (suc n) b))
-- -- -- -- -- -- -- -- -- --               (toFM2≡L n e a b)
-- -- -- -- -- -- -- -- -- --               ((toFM2≡L n (genS ((concatG (SymData (suc n)) (mapList adjTransposition e)))) a b))
-- -- -- -- -- -- -- -- -- --   toFM2≡LCoh* = {!!}
  
-- -- -- -- -- -- -- -- -- -- --   tab-cohL-refl : ∀ n → (a b c : Fin (suc n) → A)
-- -- -- -- -- -- -- -- -- -- --      → (p : a ≡ b)
-- -- -- -- -- -- -- -- -- -- --      → (q : b ≡ c)
-- -- -- -- -- -- -- -- -- -- --             →  toFM2≡L n [] a b p ∙ toFM2≡L n [] b c q ≡
-- -- -- -- -- -- -- -- -- -- --               toFM2≡L n [] a c
-- -- -- -- -- -- -- -- -- -- --                 (p ∙ q ∙ refl)
-- -- -- -- -- -- -- -- -- -- --   tab-cohL-refl n a b c p q =
-- -- -- -- -- -- -- -- -- -- --        sym (cong-∙ ((fst ∘ (tabulateFM2OfLen (suc n)))) p q)
-- -- -- -- -- -- -- -- -- -- --      ∙ cong (toFM2≡L n [] a c) (cong (p ∙_) (rUnit q))

-- -- -- -- -- -- -- -- -- -- --   tab-cohL : ∀ n → (e f : List (Fin n)) → (a b c : Fin (suc n) → A)
-- -- -- -- -- -- -- -- -- -- --      → (p : a ≡ b ∘ fst (concatG (SymData (suc n)) (mapList adjTransposition e)))
-- -- -- -- -- -- -- -- -- -- --      → (q : b ≡ c ∘ fst (concatG (SymData (suc n)) (mapList adjTransposition f)))
-- -- -- -- -- -- -- -- -- -- --             →  toFM2≡L n e a b p ∙ toFM2≡L n f b c q ≡
-- -- -- -- -- -- -- -- -- -- --               toFM2≡L n (e ++ f) a c
-- -- -- -- -- -- -- -- -- -- --                 (p ∙ cong (_∘ fst (concatG (SymData (suc n)) (mapList adjTransposition e))) q ∙
-- -- -- -- -- -- -- -- -- -- --                   cong (c ∘_) (cong fst (concatG·map (SymData (suc n)) adjTransposition e f)))
-- -- -- -- -- -- -- -- -- -- --   tab-cohL n =
-- -- -- -- -- -- -- -- -- -- --     ind (ind (tab-cohL-refl n)
-- -- -- -- -- -- -- -- -- -- --           λ {k} {l} x a b c p q →
-- -- -- -- -- -- -- -- -- -- --             let q' = _
-- -- -- -- -- -- -- -- -- -- --                 b' = _
-- -- -- -- -- -- -- -- -- -- --             in  (toFM2≡L n [] a b p) ∙ ((toFM2≡AdjTranspose k b) ∙ toFM2≡L n l b' c q')
-- -- -- -- -- -- -- -- -- -- --                ≡⟨ assoc _ _ _ ⟩ _
-- -- -- -- -- -- -- -- -- -- --                ≡⟨ cong (_∙ (toFM2≡L n l b' c q')) {!!} ⟩ {!!} ∙
-- -- -- -- -- -- -- -- -- -- --                                                            toFM2≡L n l (λ x₁ → b (fst (adjTransposition k) x₁)) c
-- -- -- -- -- -- -- -- -- -- --                                                            ((λ i x₁ → q i (fst (adjTransposition k) x₁)) ∙
-- -- -- -- -- -- -- -- -- -- --                                                             (λ i x₁ →
-- -- -- -- -- -- -- -- -- -- --                                                                c
-- -- -- -- -- -- -- -- -- -- --                                                                (fst (concatG (SymData (suc n)) (mapList adjTransposition l))
-- -- -- -- -- -- -- -- -- -- --                                                                 (fst (adjTransposition²=idEquiv k i) x₁))))
-- -- -- -- -- -- -- -- -- -- --                ≡⟨ {!!} ⟩ toFM2≡L n ([] ++ k ∷ l) a c
-- -- -- -- -- -- -- -- -- -- --                            (p ∙
-- -- -- -- -- -- -- -- -- -- --                             cong
-- -- -- -- -- -- -- -- -- -- --                             (λ section₁ →
-- -- -- -- -- -- -- -- -- -- --                                section₁ ∘
-- -- -- -- -- -- -- -- -- -- --                                fst (concatG (SymData (suc n)) (mapList adjTransposition [])))
-- -- -- -- -- -- -- -- -- -- --                             q
-- -- -- -- -- -- -- -- -- -- --                             ∙
-- -- -- -- -- -- -- -- -- -- --                             cong (_∘_ c)
-- -- -- -- -- -- -- -- -- -- --                             (cong fst
-- -- -- -- -- -- -- -- -- -- --                              (concatG·map (SymData (suc n)) adjTransposition [] (k ∷ l))))
-- -- -- -- -- -- -- -- -- -- --                 ∎
-- -- -- -- -- -- -- -- -- -- --                 --assoc _ _ _ ∙ {!!} 
-- -- -- -- -- -- -- -- -- -- --             )
-- -- -- -- -- -- -- -- -- -- --         λ {k} {l} x f a b c p q → sym (assoc _ _ _)
-- -- -- -- -- -- -- -- -- -- --            ∙ cong (toFM2≡AdjTranspose k a ∙_)
-- -- -- -- -- -- -- -- -- -- --              (x f (a ∘ (fst (adjTransposition k))) b c _ _ )
-- -- -- -- -- -- -- -- -- -- --            ∙ cong (toFM2≡AdjTranspose k a ∙_)
-- -- -- -- -- -- -- -- -- -- --               (cong (toFM2≡L n (l ++ f) (a ∘ (fst (adjTransposition k))) c)
-- -- -- -- -- -- -- -- -- -- --                ((sym (assoc _ _ _) ∙ cong ((λ i → p i ∘ (fst (adjTransposition k))) ∙_)
-- -- -- -- -- -- -- -- -- -- --                  ((
-- -- -- -- -- -- -- -- -- -- --               let lf = (fst (concatG (SymData (suc n)) (mapList adjTransposition l)))
-- -- -- -- -- -- -- -- -- -- --                   kk = (fst (adjTransposition k)) ∘ (fst (adjTransposition k))
-- -- -- -- -- -- -- -- -- -- --                   l++f = (concatG (SymData (suc n)) (mapList adjTransposition (l ++ f)))

-- -- -- -- -- -- -- -- -- -- --                   kkP = (adjTransposition²=idEquiv k)
-- -- -- -- -- -- -- -- -- -- --                   l++fP = (concatG·map (SymData (suc n)) adjTransposition l f)

-- -- -- -- -- -- -- -- -- -- --                   zzz = (cong (λ x → x ∘ lf) q) ∙ (cong (λ x → c ∘ (fst x)) l++fP)
-- -- -- -- -- -- -- -- -- -- --                   H = λ a → (cong (λ x → a ∘ fst x ) kkP) 
-- -- -- -- -- -- -- -- -- -- --               in    (  (cong (λ x → b ∘ lf ∘ fst x ) kkP) ∙ zzz

-- -- -- -- -- -- -- -- -- -- --                       ≡⟨ homotopyNatural H zzz ⟩
-- -- -- -- -- -- -- -- -- -- --                          cong (λ x → x ∘ kk) zzz ∙ (cong (λ x → c ∘ (fst l++f) ∘ fst x) kkP)
-- -- -- -- -- -- -- -- -- -- --                       ≡⟨ cong (_∙ (cong (λ x → c ∘ (fst l++f) ∘ fst x) kkP))
-- -- -- -- -- -- -- -- -- -- --                               (cong-∙ (λ x → x ∘ kk)
-- -- -- -- -- -- -- -- -- -- --                                  (cong (λ x → x ∘ lf) q)
-- -- -- -- -- -- -- -- -- -- --                                  (cong (λ x → c ∘ fst x) l++fP) ) ⟩ _
-- -- -- -- -- -- -- -- -- -- --                      ∎))

-- -- -- -- -- -- -- -- -- -- --                   ∙ (λ i → 
-- -- -- -- -- -- -- -- -- -- --                      ((cong (λ x → x ∘ fst (concatG (SymData (suc n)) (mapList adjTransposition (l))) ∘
-- -- -- -- -- -- -- -- -- -- --                             (fst (adjTransposition k)) ∘ (fst (adjTransposition k)))
-- -- -- -- -- -- -- -- -- -- --                             q) ∙
-- -- -- -- -- -- -- -- -- -- --                          (((lUnit
-- -- -- -- -- -- -- -- -- -- --                              (cong (λ x → c ∘ fst x ∘ (fst (adjTransposition k)))
-- -- -- -- -- -- -- -- -- -- --                                 (cong (adjTransposition k ∙ₑ_)
-- -- -- -- -- -- -- -- -- -- --                                   (concatG·map (SymData (suc n)) adjTransposition l f)))
-- -- -- -- -- -- -- -- -- -- --                                ) ∙ 
-- -- -- -- -- -- -- -- -- -- --                          sym (cong-∙ (λ x → c ∘ fst x ∘ (fst (adjTransposition k)))
-- -- -- -- -- -- -- -- -- -- --                                (sym (compEquiv-assoc _ _ _))
-- -- -- -- -- -- -- -- -- -- --                                (cong (adjTransposition k ∙ₑ_)
-- -- -- -- -- -- -- -- -- -- --                                   (concatG·map (SymData (suc n)) adjTransposition l f)))) i))
-- -- -- -- -- -- -- -- -- -- --                       ∙ 
-- -- -- -- -- -- -- -- -- -- --                     (cong (λ x → c ∘ (fst
-- -- -- -- -- -- -- -- -- -- --                         (concatG (SymData (suc n)) (mapList adjTransposition (l ++ f)))) ∘ fst x)
-- -- -- -- -- -- -- -- -- -- --                        (adjTransposition²=idEquiv k)))
-- -- -- -- -- -- -- -- -- -- --                        ))
-- -- -- -- -- -- -- -- -- -- --               ∙ assoc _ _ _))

-- -- -- -- -- -- -- -- -- -- --   toFM2≡' : ∀ n → {a b : Fin n → A} →
-- -- -- -- -- -- -- -- -- -- --            a ↔ₙ b → fst (tabulateFM2OfLen n a) ≡ fst (tabulateFM2OfLen n b)
-- -- -- -- -- -- -- -- -- -- --   toFM2≡' zero x = refl
-- -- -- -- -- -- -- -- -- -- --   toFM2≡' (suc n) {a} {b} (prm e p) =
-- -- -- -- -- -- -- -- -- -- --     GeneratedElimConstr
-- -- -- -- -- -- -- -- -- -- --     (SymData (suc n) )
-- -- -- -- -- -- -- -- -- -- --     (generatedSym n)
-- -- -- -- -- -- -- -- -- -- --     (λ e → (a b : Fin (suc n) → A) (p : a ≡ b ∘ fst e) → fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- -- --                                  fst (tabulateFM2OfLen (suc n) b) )
-- -- -- -- -- -- -- -- -- -- --     (λ l a b → toFM2≡L n l a b) e a b p
  
-- -- -- -- -- -- -- -- -- -- --   tab-coh : ∀ n → (a b c : Fin n → A)
-- -- -- -- -- -- -- -- -- -- --      → (r : a ↔ₙ b) (s : b ↔ₙ c) →
-- -- -- -- -- -- -- -- -- -- --               toFM2≡' n r ∙ (toFM2≡' n s) ≡
-- -- -- -- -- -- -- -- -- -- --               toFM2≡' n (isTrans↔ₙ n a b c r s)
-- -- -- -- -- -- -- -- -- -- --   tab-coh zero a b c _ _ = sym compPathRefl
-- -- -- -- -- -- -- -- -- -- --   tab-coh (suc n) a b c (prm e p) (prm f q) =
-- -- -- -- -- -- -- -- -- -- --     zzz e f a b c p q

-- -- -- -- -- -- -- -- -- -- --      where
-- -- -- -- -- -- -- -- -- -- --        zzz : _
-- -- -- -- -- -- -- -- -- -- --        zzz = GeneratedElimConstrDep2
-- -- -- -- -- -- -- -- -- -- --               (SymData (suc n) )
-- -- -- -- -- -- -- -- -- -- --             (generatedSym n)
-- -- -- -- -- -- -- -- -- -- --             (λ e → (a b : Fin (suc n) → A) (p : a ≡ b ∘ fst e) → fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- -- --                                          fst (tabulateFM2OfLen (suc n) b) )
-- -- -- -- -- -- -- -- -- -- --             (λ l a b → toFM2≡L n l a b)
-- -- -- -- -- -- -- -- -- -- --             (λ g g' x x₁ →  (a b c : Fin (suc n) → A) (p : _) (q : _) →
-- -- -- -- -- -- -- -- -- -- --               x a b p ∙ x₁ b c q ≡
-- -- -- -- -- -- -- -- -- -- --               toFM2≡' (suc n) (isTrans↔ₙ (suc n) a b c
-- -- -- -- -- -- -- -- -- -- --                  (prm g p)
-- -- -- -- -- -- -- -- -- -- --                  (prm g' q)))
-- -- -- -- -- -- -- -- -- -- --             λ l l' a b c p q →
-- -- -- -- -- -- -- -- -- -- --          let z : l ++ l' ≡ (fst
-- -- -- -- -- -- -- -- -- -- --                   (generatedSym n
-- -- -- -- -- -- -- -- -- -- --                    (concatG (SymData (suc n)) (mapList adjTransposition l) ∙ₑ
-- -- -- -- -- -- -- -- -- -- --                     concatG (SymData (suc n)) (mapList adjTransposition l'))))
-- -- -- -- -- -- -- -- -- -- --              z = {!snd
-- -- -- -- -- -- -- -- -- -- --               (generatedSym n
-- -- -- -- -- -- -- -- -- -- --               (concatG (SymData (suc n)) (mapList adjTransposition (l ++ l'))))!}
-- -- -- -- -- -- -- -- -- -- --                ∙ cong (fst ∘ generatedSym n)
-- -- -- -- -- -- -- -- -- -- --                (sym (concatG·map (SymData (suc n)) adjTransposition l l')) 
-- -- -- -- -- -- -- -- -- -- --          in  tab-cohL n l l' a b c p  q
-- -- -- -- -- -- -- -- -- -- --               ∙ {!!}
-- -- -- -- -- -- -- -- -- -- --               ∙  (funExt⁻ (funExt⁻ (funExt⁻ (GeneratedElimConstrβ (SymData (suc n) )
-- -- -- -- -- -- -- -- -- -- --             (generatedSym n)
-- -- -- -- -- -- -- -- -- -- --             (λ e → (a b : Fin (suc n) → A) (p : a ≡ b ∘ fst e) →
-- -- -- -- -- -- -- -- -- -- --                                          fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- -- --                                          fst (tabulateFM2OfLen (suc n) b) )
-- -- -- -- -- -- -- -- -- -- --             (λ l a b → toFM2≡L n l a b)
-- -- -- -- -- -- -- -- -- -- --              ((concatG (SymData (suc n)) (mapList adjTransposition l))
-- -- -- -- -- -- -- -- -- -- --                ∙ₑ
-- -- -- -- -- -- -- -- -- -- --                (concatG (SymData (suc n)) (mapList adjTransposition l')))) a) c)
-- -- -- -- -- -- -- -- -- -- --                 ((p ∙ cong (_∘ _) q)))



-- -- -- -- -- -- -- -- -- -- --     -- let gen = (generatedSym n)
-- -- -- -- -- -- -- -- -- -- --     --     (e' , eP) = gen e 
-- -- -- -- -- -- -- -- -- -- --     --     (f' , fP) = gen f

-- -- -- -- -- -- -- -- -- -- --     --     p0 : PathP (λ k → (a₁ b₁ c₁ : Fin (suc n) → A) →
-- -- -- -- -- -- -- -- -- -- --     --           a₁ ≡ (λ x → b₁ (fst (snd (generatedSym n e) k) x)) →
-- -- -- -- -- -- -- -- -- -- --     --           b₁ ≡ (λ x → c₁ (fst (snd (generatedSym n f) k) x)) →
-- -- -- -- -- -- -- -- -- -- --     --           fst (tabulateFM2OfLen (suc n) a₁) ≡
-- -- -- -- -- -- -- -- -- -- --     --           fst (tabulateFM2OfLen (suc n) c₁))
-- -- -- -- -- -- -- -- -- -- --     --            (λ a b c p q → toFM2≡L n e' a b p ∙ toFM2≡L n f' b c q)
-- -- -- -- -- -- -- -- -- -- --     --            λ a b c p q → toFM2≡' (suc n) {b = b} (prm e p) ∙ (toFM2≡' (suc n) {a = b} {b = c} (prm f q))
-- -- -- -- -- -- -- -- -- -- --     --     p0 i a b c p q = {!!} ∙ {!!} 

-- -- -- -- -- -- -- -- -- -- --     --     p1 : PathP (λ k → (a₂ b₂ c₂ : Fin (suc n) → A) →
-- -- -- -- -- -- -- -- -- -- --     --              a₂ ≡ (λ x → b₂ (fst (snd (generatedSym n e) k) x)) →
-- -- -- -- -- -- -- -- -- -- --     --              b₂ ≡ (λ x → c₂ (fst (snd (generatedSym n f) k) x)) →
-- -- -- -- -- -- -- -- -- -- --     --              fst (tabulateFM2OfLen (suc n) a₂) ≡
-- -- -- -- -- -- -- -- -- -- --     --              fst (tabulateFM2OfLen (suc n) c₂))
-- -- -- -- -- -- -- -- -- -- --     --            (λ a b c p q → toFM2≡L n (e' ++ f') a c
-- -- -- -- -- -- -- -- -- -- --     --             (p ∙ cong (_∘ fst (concatG (SymData (suc n)) (mapList adjTransposition e'))) q ∙
-- -- -- -- -- -- -- -- -- -- --     --               cong (c ∘_) (cong fst (concatG·map (SymData (suc n)) adjTransposition e' f'))))
-- -- -- -- -- -- -- -- -- -- --     --            λ a b c p q → toFM2≡' (suc n) (isTrans↔ₙ' (suc n) a b c (prm e p) (prm f q))
-- -- -- -- -- -- -- -- -- -- --     --     p1 i a b c p q = {!!}
-- -- -- -- -- -- -- -- -- -- --     -- in comp (λ k → ((a b c : Fin (suc n) → A) (p : a ≡ b ∘ fst (eP k)) (p : b ≡ c ∘ fst (fP k)) →
-- -- -- -- -- -- -- -- -- -- --     --                              fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- -- --     --                              fst (tabulateFM2OfLen (suc n) c) ))
-- -- -- -- -- -- -- -- -- -- --     --       (λ k → λ { (i = i0) → p0 k
-- -- -- -- -- -- -- -- -- -- --     --                ; (i = i1) → p1 k
-- -- -- -- -- -- -- -- -- -- --     --                })
-- -- -- -- -- -- -- -- -- -- --     --       (λ a b c p q → tab-cohL n e' f' a b c p q i) a b c p q

-- -- -- -- -- -- -- -- -- -- -- -- (subst ((λ e → {a b : Fin (suc n) → A} (p : a ≡ b ∘ fst e) → fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- -- -- --                                  fst (tabulateFM2OfLen (suc n) b) )) eP (λ {a} {b} → toFM2≡L n e' a b)) {a} {b} p
-- -- -- -- -- -- -- -- -- -- -- --         ∙ (subst ((λ e → {a b : Fin (suc n) → A} (p : a ≡ b ∘ fst e) → fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- -- -- --                                  fst (tabulateFM2OfLen (suc n) b) )) fP (λ {a} {b} → toFM2≡L n f' a b)) {b} {c} q
-- -- -- -- -- -- -- -- -- -- -- --       ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- --         transport {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- --                         ∙
-- -- -- -- -- -- -- -- -- -- -- --         transport {!!} {!!}
                         
-- -- -- -- -- -- -- -- -- -- -- --      ≡⟨ {!!} ⟩ 
-- -- -- -- -- -- -- -- -- -- -- --        {!!}

-- -- -- -- -- -- -- -- -- -- -- -- cong₂ {x = subst ((λ e → {a b : Fin (suc n) → A} (p : a ≡ b ∘ fst e) → fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- -- -- --                                  fst (tabulateFM2OfLen (suc n) b) )) eP (λ {a} {b} → toFM2≡L n e' a b) {a} {b} p}
-- -- -- -- -- -- -- -- -- -- -- --              {y = toFM2≡L n (fst (generatedSym n e)) a b {!!}}
-- -- -- -- -- -- -- -- -- -- -- --              _∙_ --(fromPathP
-- -- -- -- -- -- -- -- -- -- -- --               -- {x = subst {!(λ e → {a b : Fin (suc n) → A} (p : a ≡ b ∘ fst e) → fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- -- -- --               --                    fst (tabulateFM2OfLen (suc n) b) )!}
-- -- -- -- -- -- -- -- -- -- -- --               --   eP (toFM2≡L n) }
-- -- -- -- -- -- -- -- -- -- -- --               -- {y = toFM2≡L n (fst (generatedSym n e)) a b _} {!!})
-- -- -- -- -- -- -- -- -- -- -- --               {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- --        ∙ tab-cohL n e' f' a b c {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- --        ∙ {!!}  

-- -- -- -- -- -- -- -- -- -- -- -- transport {B = (p : a ≡ b ∘ fst e) (q : b ≡ c ∘ fst f) →
-- -- -- -- -- -- -- -- -- -- -- --               toFM2≡' (suc n) {a} {b} (prm e p) ∙ (toFM2≡' (suc n) {b} {c} (prm f q)) ≡
-- -- -- -- -- -- -- -- -- -- -- --               toFM2≡' (suc n) (isTrans↔ₙ' (suc n) a b c (prm e p) (prm f q))}
-- -- -- -- -- -- -- -- -- -- -- --           (λ i → (p : a ≡ b ∘ fst (eP i) ) (q : b ≡ c ∘ fst (fP i)) →
-- -- -- -- -- -- -- -- -- -- -- --                     transp {!!} (~ i) (toFM2≡L n e' a b {!!}) 
-- -- -- -- -- -- -- -- -- -- -- --                     ∙
-- -- -- -- -- -- -- -- -- -- -- --                     {!!}
-- -- -- -- -- -- -- -- -- -- -- --                     ≡
-- -- -- -- -- -- -- -- -- -- -- --                     {!!}
-- -- -- -- -- -- -- -- -- -- -- --                     )
-- -- -- -- -- -- -- -- -- -- -- --       (tab-cohL n e' f' a b c) p q

-- -- -- -- -- -- -- -- -- -- -- -- {!!} --zzz e f a b c p q {!!} ∙ {! !}   
-- -- -- -- -- -- -- -- -- -- --     -- GeneratedElimConstr
-- -- -- -- -- -- -- -- -- -- --     --   (SymData (suc n) )
-- -- -- -- -- -- -- -- -- -- --     --   (generatedSym n)
-- -- -- -- -- -- -- -- -- -- --     --   (λ e → ∀ f → (a b c : _)
-- -- -- -- -- -- -- -- -- -- --     --     → (p : a ≡ b ∘ fst e)
-- -- -- -- -- -- -- -- -- -- --     --     → (q : b ≡ c ∘ fst f) →
-- -- -- -- -- -- -- -- -- -- --     --           toFM2≡' (suc n) {a} {b}  (prm e p) ∙ (toFM2≡' (suc n) {b} {c} (prm f q)) ≡
-- -- -- -- -- -- -- -- -- -- --     --           toFM2≡' (suc n) (isTrans↔ₙ' (suc n) a b c (prm e p) (prm f q)))
-- -- -- -- -- -- -- -- -- -- --     --    (λ l → GeneratedElimConstr
-- -- -- -- -- -- -- -- -- -- --     --      (SymData (suc n) )
-- -- -- -- -- -- -- -- -- -- --     --      (generatedSym n)
-- -- -- -- -- -- -- -- -- -- --     --      _ λ l' a b c p q
-- -- -- -- -- -- -- -- -- -- --     --        → cong₂ _∙_ {!!} {!!} ∙ tab-cohL n l l' a b c p q ∙ {!!})
-- -- -- -- -- -- -- -- -- -- --     --        e f a b c p q

-- -- -- -- -- -- -- -- -- -- --      -- where
-- -- -- -- -- -- -- -- -- -- --      --   zzz : {!!}
-- -- -- -- -- -- -- -- -- -- --      --   zzz = GeneratedElimConstrDep++
-- -- -- -- -- -- -- -- -- -- --      --          (SymData (suc n) )
-- -- -- -- -- -- -- -- -- -- --      --        (generatedSym n)
-- -- -- -- -- -- -- -- -- -- --      --        (λ e → {a b : Fin (suc n) → A} (p : a ≡ b ∘ fst e) → fst (tabulateFM2OfLen (suc n) a) ≡
-- -- -- -- -- -- -- -- -- -- --      --                                     fst (tabulateFM2OfLen (suc n) b) )
-- -- -- -- -- -- -- -- -- -- --      --        (λ l {a} {b} → toFM2≡L n l a b)
-- -- -- -- -- -- -- -- -- -- --      --        -- (λ e f → (a b c : _)
-- -- -- -- -- -- -- -- -- -- --      --        --     → (p : a ≡ b ∘ fst e)
-- -- -- -- -- -- -- -- -- -- --      --        --     → (q : b ≡ c ∘ fst f) → a ↔ₙ c)
-- -- -- -- -- -- -- -- -- -- --      --        (λ l l' {a} {b} p → toFM2≡L n (l ++ l') a b (p ∙ {!!}) ) --(isTrans↔ₙ'' n)
-- -- -- -- -- -- -- -- -- -- --      --        -- {!!}
-- -- -- -- -- -- -- -- -- -- --      --        (λ e f eX fX efX → (a b c : _)
-- -- -- -- -- -- -- -- -- -- --      --           → (p : a ≡ b ∘ fst e)
-- -- -- -- -- -- -- -- -- -- --      --           → (q : b ≡ c ∘ fst f) →
-- -- -- -- -- -- -- -- -- -- --      --                eX {a} {b} p ∙ fX {b} {c} q ≡
-- -- -- -- -- -- -- -- -- -- --      --                  -- efX' {a} {c} (_↔ₙ_.l≡ (efX a b c p q) ∙ pp)
-- -- -- -- -- -- -- -- -- -- --      --                  efX {a} {c} {!!}
-- -- -- -- -- -- -- -- -- -- --      --                  )
-- -- -- -- -- -- -- -- -- -- --      --        {!!}
-- -- -- -- -- -- -- -- -- -- --      --        -- λ l f₂ a₂ b₂ c₂ p₂ q₂ → {!!}

          
-- -- -- -- -- -- -- -- -- -- --            -- (λ l → GeneratedElimConstr
-- -- -- -- -- -- -- -- -- -- --            --   (SymData (suc n) )
-- -- -- -- -- -- -- -- -- -- --            --   (generatedSym n)
-- -- -- -- -- -- -- -- -- -- --            --   _ λ l' a b c p q
-- -- -- -- -- -- -- -- -- -- --            --     → cong₂ _∙_ {!!} {!!} ∙ tab-cohL n l l' a b c p q ∙ {!!})
-- -- -- -- -- -- -- -- -- -- --            --     e f a b c p q




-- -- -- -- -- -- -- -- -- -- -- --   toFM2 : ∀ n → Fin→//↔ n → FMSet2OfLen A n
-- -- -- -- -- -- -- -- -- -- -- --   toFM2 n = GQ.rec
-- -- -- -- -- -- -- -- -- -- -- --     (isTrans↔ₙ' n)
-- -- -- -- -- -- -- -- -- -- -- --     (isGroupoidFMSet2OfLen n)
-- -- -- -- -- -- -- -- -- -- -- --     (tabulateFM2OfLen n) (FMSet2OfLen≡ ∘ toFM2≡' n)
-- -- -- -- -- -- -- -- -- -- -- --     {!!} --λ r s → compPath-filler _ _ ▷ tab-coh n _ _ _ r s


-- -- -- -- -- -- -- -- -- -- -- -- --   -- symFMHom : ∀ n → GroupHom (SymData n) (idEquivsG (FMSet2OfLen A n))
-- -- -- -- -- -- -- -- -- -- -- -- --   -- symFMHom zero = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --   -- symFMHom (suc n) = toConst≃fromGens {G = SymData (suc n)}
-- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ x →  PT.∣ generatedSym n x ∣₁) ((transposeFM2≃ _ ∘ suc))
  
-- -- -- -- -- -- -- -- -- -- -- -- --   -- symFM : ∀ n → (e : Fin n ≃ Fin n) →
-- -- -- -- -- -- -- -- -- -- -- -- --   --      singl
-- -- -- -- -- -- -- -- -- -- -- -- --   --        (idEquiv (FMSet2OfLen A n) )
-- -- -- -- -- -- -- -- -- -- -- -- --   -- symFM = fst ∘ symFMHom

-- -- -- -- -- -- -- -- -- -- -- -- --   -- symFM-fun : ∀ n → (e : Fin n ≃ Fin n) →
       
-- -- -- -- -- -- -- -- -- -- -- -- --   --        (FMSet2OfLen A n) → (FMSet2OfLen A n)
-- -- -- -- -- -- -- -- -- -- -- -- --   -- symFM-fun n e = equivFun (fst (symFM n e))


-- -- -- -- -- -- -- -- -- -- -- -- --   -- -- tab-symFM' : ∀ n → (b : (Fin (suc n) → A)) → 
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --               tabulateFM2OfLen (suc n) (b) ≡
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --                 equivFun (fst (symFM (suc n) (idEquiv _))) (tabulateFM2OfLen (suc n) b)
-- -- -- -- -- -- -- -- -- -- -- -- --   -- -- tab-symFM' n b = {!n!}
  
-- -- -- -- -- -- -- -- -- -- -- -- --   -- -- tab-symFM : ∀ n → (e : Fin n ≃ Fin n) → (b : (Fin n → A)) → 
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --               tabulateFM2OfLen n (b ∘ fst (e)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --                 equivFun (fst (symFM n e)) (tabulateFM2OfLen n b)
-- -- -- -- -- -- -- -- -- -- -- -- --   -- -- tab-symFM zero e b = refl
-- -- -- -- -- -- -- -- -- -- -- -- --   -- -- tab-symFM (suc n) =
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --   GeneratedElimConstr (SymData (suc n)) (generatedSym n)
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --    (λ e → (b : (Fin (suc n) → A)) → 
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --               tabulateFM2OfLen (suc n) (b ∘ fst (e)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --                 equivFun (fst (symFM (suc n) e)) (tabulateFM2OfLen (suc n) b))
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --               (ind {!!} {!!})

-- -- -- -- -- -- -- -- -- -- -- -- --   -- tab-sym : ∀ n → (e : Fin n ≃ Fin n) → (b : Fin n → A) →
-- -- -- -- -- -- -- -- -- -- -- -- --   --            tabulateFM2OfLen n b ≡ tabulateFM2OfLen n (b ∘ fst (e))
-- -- -- -- -- -- -- -- -- -- -- -- --   -- tab-sym = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- --   -- tab-symS : ∀ n → (e : Fin n ≃ Fin n) → (b : Fin n → A) →
-- -- -- -- -- -- -- -- -- -- -- -- --   --                singl (tabulateFM2OfLen n b)
-- -- -- -- -- -- -- -- -- -- -- -- --   -- tab-symS n e b = (tabulateFM2OfLen n (b ∘ fst (e))) , (tab-sym n e b)

-- -- -- -- -- -- -- -- -- -- -- -- --   -- tab-symS* : ∀ n → (e : Fin n ≃ Fin n) → (b : Fin n → A) →
-- -- -- -- -- -- -- -- -- -- -- -- --   --                singl (tabulateFM2OfLen n b)
-- -- -- -- -- -- -- -- -- -- -- -- --   -- tab-symS* n e b =
-- -- -- -- -- -- -- -- -- -- -- -- --   --   let (z , z=) = symFM n e
-- -- -- -- -- -- -- -- -- -- -- -- --   --   in (fst z (tabulateFM2OfLen n b)) , funExt⁻ (cong fst z=) (tabulateFM2OfLen n b)

-- -- -- -- -- -- -- -- -- -- -- -- --   -- -- *sq : ∀ n → (e : Fin n ≃ Fin n) → (a : Fin n → A) →
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --         Square
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --            (tab-sym n e a)
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --            (snd (tab-symS* n e a))
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --            refl
-- -- -- -- -- -- -- -- -- -- -- -- --   -- --            {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --   -- -- *sq = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --   -- toFM2≡ : ∀ n → {a b : Fin n → A} →
-- -- -- -- -- -- -- -- -- -- -- -- --   --          a ↔ₙ b → tabulateFM2OfLen n a ≡ tabulateFM2OfLen n b
-- -- -- -- -- -- -- -- -- -- -- -- --   -- toFM2≡ n {b = b} (prm e p) = cong (tabulateFM2OfLen n) p ∙ sym (tab-sym n e b)


-- -- -- -- -- -- -- -- -- -- -- -- --   -- toFM2≡S : ∀ n → {a b : Fin n → A} →
-- -- -- -- -- -- -- -- -- -- -- -- --   --          a ↔ₙ b → singl (tabulateFM2OfLen n a)
-- -- -- -- -- -- -- -- -- -- -- -- --   -- toFM2≡S n {b = b} x =
-- -- -- -- -- -- -- -- -- -- -- -- --   --   (tabulateFM2OfLen n b) , toFM2≡ n x 


-- -- -- -- -- -- -- -- -- -- -- -- --   -- tab-coh'' : ∀ n → (a : Fin n → A)
-- -- -- -- -- -- -- -- -- -- -- -- --   --    → (e f : Fin n ≃ Fin n) →
-- -- -- -- -- -- -- -- -- -- -- -- --   --      PathP (λ i → tabulateFM2OfLen n a ≡
-- -- -- -- -- -- -- -- -- -- -- -- --   --             (fst (fst (IsGroupHom.pres· (snd (symFMHom n)) e f (~ i)))
-- -- -- -- -- -- -- -- -- -- -- -- --   --               (tabulateFM2OfLen n a)))
-- -- -- -- -- -- -- -- -- -- -- -- --   --          -- (funExt⁻ (cong fst (snd (symFM n (e)))) (tabulateFM2OfLen n a)
-- -- -- -- -- -- -- -- -- -- -- -- --   --          --   ∙ funExt⁻ (cong fst (snd (symFM n (f))))
-- -- -- -- -- -- -- -- -- -- -- -- --   --          --      (fst (fst (fst (symFMHom n) e)) (tabulateFM2OfLen n a)))
-- -- -- -- -- -- -- -- -- -- -- -- --   --          (funExt⁻
-- -- -- -- -- -- -- -- -- -- -- -- --   --             ( cong₂ (λ x y → x ∘ y)
-- -- -- -- -- -- -- -- -- -- -- -- --   --                (cong fst (snd (fst (symFMHom n) f)))
-- -- -- -- -- -- -- -- -- -- -- -- --   --                  (cong fst (snd (fst (symFMHom n) e))))
-- -- -- -- -- -- -- -- -- -- -- -- --   --             (tabulateFM2OfLen n a))
-- -- -- -- -- -- -- -- -- -- -- -- --   --          (funExt⁻ (cong fst (snd (symFM n (e ∙ₑ f)))) (tabulateFM2OfLen n a))
-- -- -- -- -- -- -- -- -- -- -- -- --   -- tab-coh'' n a e f i =
-- -- -- -- -- -- -- -- -- -- -- -- --   --    funExt⁻ (cong fst (snd (IsGroupHom.pres· (snd (symFMHom n)) e f (~ i))))
-- -- -- -- -- -- -- -- -- -- -- -- --   --       (tabulateFM2OfLen n a)

-- -- -- -- -- -- -- -- -- -- -- -- --   tab-coh'S : ∀ n → (a : Fin n → A)
-- -- -- -- -- -- -- -- -- -- -- -- --      → (e f : Fin n ≃ Fin n)  →
-- -- -- -- -- -- -- -- -- -- -- -- --               Path (tabulateFM2OfLen n a ≡ tabulateFM2OfLen n (a ∘ invEq e ∘ invEq f))
-- -- -- -- -- -- -- -- -- -- -- -- --               {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --               {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --   tab-coh'S n a e f = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- --   -- tab-coh' : ∀ n → (a : Fin n → A)
-- -- -- -- -- -- -- -- -- -- -- -- --   --    → (e f : Fin n ≃ Fin n)  →
-- -- -- -- -- -- -- -- -- -- -- -- --   --             Path (tabulateFM2OfLen n a ≡ tabulateFM2OfLen n (a ∘ invEq e ∘ invEq f))
-- -- -- -- -- -- -- -- -- -- -- -- --   --             (toFM2≡ n {b = (a ∘ invEq e)} (prm e ((cong (a ∘_) (sym (funExt (retEq e))))))
-- -- -- -- -- -- -- -- -- -- -- -- --   --               ∙ (toFM2≡ n (prm f (((cong ((a ∘ invEq e) ∘_) (sym (funExt (retEq f)))))))))
-- -- -- -- -- -- -- -- -- -- -- -- --   --             (toFM2≡ n (isTrans↔ₙ n a (a ∘ invEq e) (a ∘ invEq e ∘ invEq f)
-- -- -- -- -- -- -- -- -- -- -- -- --   --                (prm e (cong (a ∘_) (sym (funExt (retEq e)))))
-- -- -- -- -- -- -- -- -- -- -- -- --   --                 (prm f ((cong ((a ∘ invEq e) ∘_) (sym (funExt (retEq f))))))))
-- -- -- -- -- -- -- -- -- -- -- -- --   -- tab-coh' n a e f i j =

-- -- -- -- -- -- -- -- -- -- -- -- --   --   hcomp (λ k → λ {
-- -- -- -- -- -- -- -- -- -- -- -- --   --            (i = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --   --           ;(i = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --   --           ;(j = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --   --           ;(j = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --   --           })
-- -- -- -- -- -- -- -- -- -- -- -- --   --     {!!}



-- -- -- -- -- -- -- -- -- -- -- -- --   tab-cohS : ∀ n → (a b c : Fin n → A)
-- -- -- -- -- -- -- -- -- -- -- -- --      → (r : a ↔ₙ b) (s : b ↔ₙ c) →
-- -- -- -- -- -- -- -- -- -- -- -- --               Path (singl (tabulateFM2OfLen n a))
-- -- -- -- -- -- -- -- -- -- -- -- --                 (tabulateFM2OfLen n c , (toFM2≡ n r ∙ toFM2≡ n s))
-- -- -- -- -- -- -- -- -- -- -- -- --                 (toFM2≡S n (isTrans↔ₙ n a b c r s))
              
-- -- -- -- -- -- -- -- -- -- -- -- --               -- toFM2≡ n r ∙ (λ i → toFM2≡ n s i) ≡
-- -- -- -- -- -- -- -- -- -- -- -- --               -- toFM2≡ n (isTrans↔ₙ n a b c r s)
-- -- -- -- -- -- -- -- -- -- -- -- --   tab-cohS n a b c (prm e p) (prm f q) = isPropSingl _ _
    

-- -- -- -- -- -- -- -- -- -- -- -- --   tab-coh : ∀ n → (a b c : Fin n → A)
-- -- -- -- -- -- -- -- -- -- -- -- --      → (r : a ↔ₙ b) (s : b ↔ₙ c) →
-- -- -- -- -- -- -- -- -- -- -- -- --               toFM2≡ n r ∙ (λ i → toFM2≡ n s i) ≡
-- -- -- -- -- -- -- -- -- -- -- -- --               toFM2≡ n (isTrans↔ₙ n a b c r s)
-- -- -- -- -- -- -- -- -- -- -- -- --   tab-coh n a b c (prm e p) (prm f q) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- let p' : a ∘ invEq e ≡ b
-- -- -- -- -- -- -- -- -- -- -- -- --     --     p' = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     --     q' : a ∘ invEq e ∘ invEq f ≡ c
-- -- -- -- -- -- -- -- -- -- -- -- --     --     q' = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     -- in {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   toFM2 : ∀ n → Fin→//↔ n → FMSet2OfLen A n
-- -- -- -- -- -- -- -- -- -- -- -- -- --   toFM2 n = GQ.rec
-- -- -- -- -- -- -- -- -- -- -- -- -- --     (isTrans↔ₙ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     (isGroupoidFMSet2OfLen n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     (tabulateFM2OfLen n) (toFM2≡ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- (λ {a} {b} (prm e p) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --     --     cong (tabulateFM2OfLen n) p ∙ sym (tab-sym n e b)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     --   )
-- -- -- -- -- -- -- -- -- -- -- -- -- --     λ r s → compPath-filler _ _ ▷ tab-coh n _ _ _ r s

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- zz _ _ _ r s


-- -- -- -- -- -- -- -- -- -- -- -- -- --   --    where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --      w : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --      w = {!!}
       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   tabS : ∀ n → (e : Fin n ≃ Fin n) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        singl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          {A = (Fin n → A) → FMSet2OfLen A n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ b → tabulateFM2OfLen n (b ∘ fst (e)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   tabS = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- fst (tabS n e) = tabulateFM2OfLen n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- snd (tabS zero e) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- snd (tabS (suc n) e) = funExt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   λ f → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     let (e' , p') = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         k' = equivFun e zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         prv = snd (tabS n e')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     in Σ≡Prop (λ _ → isSetℕ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          ({!!} ∙ cong (f zero ∷2_) (cong fst (funExt⁻  prv (f ∘ suc)) ))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   tabS' : ∀ n → (e : Fin n ≃ Fin n) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        -- singl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        --   {A = FMSet2OfLen A n ≃ FMSet2OfLen A n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        --   (λ b → b ) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   tabS' = {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- tabSCoh : ∀ n → (e : Fin n ≃ Fin n) → ∀ b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --               → tabulateFM2OfLen n (b ∘ fst e) ≡ fst (tabS n e) b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- tabSCoh = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- toFM2 : ∀ n → Fin→//↔ n → FMSet2OfLen A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- toFM2 n = GQ.rec
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (isTrans↔ₙ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (isGroupoidFMSet2OfLen A n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (tabulateFM2OfLen n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (λ {a} {b} (prm e p) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       cong (tabulateFM2OfLen n) p ∙ funExt⁻ (snd (tabS n e)) b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   λ r s → compPath-filler _ _ ▷ zz _ _ _ r s

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     zz : (a b c : Fin n → A) → (r : a ↔ₙ b) → (s : b ↔ₙ c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             → Path (tabulateFM2OfLen n a ≡ tabulateFM2OfLen n c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 (((cong (tabulateFM2OfLen n) (l≡ r)) ∙ funExt⁻ (snd (tabS n (F≃ r))) b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  ((cong (tabulateFM2OfLen n) (l≡ s)) ∙ funExt⁻ (snd (tabS n (F≃ s))) c))
                  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 ((cong (tabulateFM2OfLen n) (l≡ (isTrans↔ₙ n a b c r s))) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 funExt⁻ (snd (tabS n (F≃ (isTrans↔ₙ n a b c r s)))) c)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     zz = {!!}


  


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module FC2M where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Cubical.HITs.FiniteMultiset.Base2 as FM2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        renaming (_∷2_ to _∷fm2_ ; [] to []fm2 ; _++_ to _++fm2_) hiding ([_])

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   List→FMSet2 : List A → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   List→FMSet2 {A = A} = foldr {B = FMSet2 A} _∷fm2_ []fm2



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PunchHeadInOut//≡ : (l : List A) → ∀ k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → List→FMSet2 l ≡ List→FMSet2 (permute l (rot≃ k))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PunchHeadInOut//≡ (x ∷ l) zero =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     cong List→FMSet2 (sym (tabulate-lookup (x ∷ l)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PunchHeadInOut//≡ (x ∷ x₁ ∷ l) one i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     comm x x₁ (List→FMSet2 (tabulate-lookup l (~ i))) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PunchHeadInOut//≡ (x ∷ x₁ ∷ l) (suc (suc k)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     cong (x ∷fm2_) (PunchHeadInOut//≡ (x₁ ∷ l) (suc k)) ∙ comm _ _ _


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PunchHeadInOut//≡⁻ : ∀ (x : A) (l : List A) → ∀ k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         → List→FMSet2 (x ∷ l) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            List→FMSet2 (permute (x ∷ l) (invEquiv (rot≃ k)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PunchHeadInOut//≡⁻ x l zero = cong (List→FMSet2 ∘ (x ∷_))  (sym (tabulate-lookup l))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PunchHeadInOut//≡⁻ x (x₁ ∷ l) one i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     comm x x₁ (List→FMSet2 ((tabulate-lookup l) (~ i))) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PunchHeadInOut//≡⁻ x (x₁ ∷ l) (suc (suc k)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ ≡⟨ comm _ _ _ ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ ≡⟨ cong (x₁ ∷fm2_) (PunchHeadInOut//≡⁻ x l (suc k)) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ ≡⟨ cong ((x₁ ∷fm2_) ∘ List→FMSet2 ∘ tabulate (suc _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (funExt (lookup-swap x₁ x l ∘
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             suc ∘ equivFun (invEquiv (rot≃ (suc k))))) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _ ∎


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet2≡Refl : (a : List A) → Path (Path (List//↔ A) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                    (eq// (isRefl↔ a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                    refl  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet2≡Refl a =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ∙²≡id→≡refl (sym (cong eq// comp↔Refl 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ comp'// _ isTrans↔ (isRefl↔ a) (isRefl↔ a)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   len2 : FMSet2 A → ℕ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   len2 = RecSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isSetℕ 0 (λ _ → suc) (λ _ _ _ → refl) λ _ _ _ _ → refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   permute→FMSet2≡ : (xs : List A) → ∀ {n} → (e : Fin n ≃ Fin (length xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        → List→FMSet2 xs ≡ List→FMSet2 (permute xs e)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   permute→FMSet2≡ [] {zero} e = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   permute→FMSet2≡ [] {suc n} e = ⊥.rec (¬Fin0 (fst e zero))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   permute→FMSet2≡ (x ∷ xs) {zero} e = ⊥.rec (¬Fin0 (invEq e zero))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   permute→FMSet2≡ {A = A} (x ∷ xs) {suc n} eP =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    let r@(prm e _) = ↔permute (x ∷ xs) eP       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (e' , p') = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        k' = equivFun e zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        xs' = permute xs (invEquiv e')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (prm _ p⁻) = isSym↔ _ _ r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       _ ≡⟨ cong (x ∷fm2_) (permute→FMSet2≡ xs (invEquiv e'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∙ PunchHeadInOut//≡⁻ x xs' (subst Fin pL k') ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       _ ≡⟨ cong List→FMSet2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (rot≃∙ₑ≡→Fin≃ pL k')) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            (invEq (rot≃ k'))  ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p') ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻)) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            _ ≡⟨ tabulate-lookup _ ⟩ (permute (x ∷ xs) eP) ∎
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ) ⟩ _ ∎


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet2≡COMM : ∀ n → (a b : List A) → (p : a ≡ b) → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet2≡COMM n a b =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      J (λ b p → (r : Fin n ≃ Fin (length b)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      Σ[ r' ∈  Fin n ≃ Fin (length a) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      Σ[ p' ∈ permute a r' ≡ permute b r ] 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      cong List→FMSet2 p ∙ permute→FMSet2≡ b r ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      permute→FMSet2≡ a r' ∙ cong List→FMSet2 p')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       λ r → r , (refl , sym (lUnit _) ∙ rUnit _ )         


     

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet2≡ : (a b : List A) → a ↔ b → List→FMSet2 a ≡ List→FMSet2 b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet2≡ {A = A} xs _ r =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      let r' = factor↔Σ' _ _ r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      in permute→FMSet2≡ xs (invEquiv (F≃ r)) ∙ cong List→FMSet2 (fst r')


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet≡2Trans : (a b c : List A) → (p : a ↔ b) → (q : b ↔ c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   → ↔→FMSet2≡ a b p ∙ ↔→FMSet2≡ b c q ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     ↔→FMSet2≡ a c (isTrans↔ a b c p q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet≡2Trans a b c p q =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    let p' = factor↔Σ' _ _ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        q' = factor↔Σ' _ _ q
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        pq' = factor↔Σ' _ _ (p ∙↔ q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (r* , p* , P) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          ↔→FMSet2≡COMM (length c) (permute a (invEquiv (F≃ p))) b (fst p') (invEquiv (F≃ q))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    in sym (assoc _ _ _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        cong ((λ i → permute→FMSet2≡ a (invEquiv (F≃ p)) i) ∙_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          ((assoc _ _ _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             cong  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (_∙ (cong List→FMSet2 (fst q'))) P
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           ∙ sym (assoc _ _ _) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           assoc _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           ∙ cong₂ _∙_ refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              (sym (cong-∙ {x = permute (permute a (invEquiv (F≃ p))) r*} List→FMSet2 p* (fst q')))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           ∙ (_∙_ {y = List→FMSet2 (permute (permute a (invEquiv (F≃ p))) r*)} _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              ( _∙_ {y = List→FMSet2 (permute a ((invEquiv (F≃ p ∙ₑ F≃ q))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (λ i → permute→FMSet2≡ a (invEquiv (F≃ (isTrans↔ a b c p q))) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (cong List→FMSet2 (fst pq'))) ∎ ) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet≡2Trans : (a b c : List A) → (p : a ↔ b) → (q : b ↔ c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     → ↔→FMSet2≡ a b p ∙ ↔→FMSet2≡ b c q ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       ↔→FMSet2≡ a c (isTrans↔ a b c p q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet≡2Trans [] [] [] _ _ = cong₂ _∙_ (sym compPathRefl) (sym compPathRefl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet≡2Trans [] [] (_ ∷ _) _ q = ⊥.rec (¬nil↔cons q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet≡2Trans [] (_ ∷ _) _ p _ = ⊥.rec (¬nil↔cons p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet≡2Trans (_ ∷ _) [] _ p _ = ⊥.rec (¬cons↔nil p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet≡2Trans (_ ∷ _) (_ ∷ _) [] _ q = ⊥.rec (¬cons↔nil q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ↔→FMSet≡2Trans a@(x ∷ xs) b@(y ∷ ys) c@(z ∷ zs) r*@(prm f q) r**@(prm g w) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     cong₂ _∙_ (sym (assoc _ _ _)) (sym (assoc _ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ∙ assoc _ _ _
  


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- step : ∀ n → Iso (Σ (List//↔ A) ((n ≡_) ∘ length//))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                        (Σ (FMSet2 A) ((n ≡_) ∘ len2))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            → Iso (Σ (List//↔ A) (((suc n) ≡_) ∘ length//))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                        (Σ (FMSet2 A) (((suc n) ≡_) ∘ len2))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- step {A = A} n prv = w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   open Iso prv

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   toFM : (Σ (List//↔ A) (((suc n) ≡_) ∘ length//))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            → (Σ (FMSet2 A) (((suc n) ≡_) ∘ len2))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   toFM (x , p) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     GQ.elim {A = List A} isTrans↔ {λ x → suc n ≡ length// x → Σ (FMSet2 A) λ z → suc n ≡ len2 z} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (λ _ → isGroupoidΠ (λ _ → isOfHLevelΣ 3 trunc (λ z → isSet→isGroupoid (isProp→isSet (isSetℕ (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                      (len2 z))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (λ { [] → ⊥.rec ∘ ℕsnotz
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           ; (a ∷ xs) p → let (xs' , p') = (fun ([ xs ]// , injSuc p))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                          in (a ∷fm2 xs') , cong suc p'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                          })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (λ { {[]} {[]} r i p → ⊥.rec (ℕsnotz p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           ; {[]} {_ ∷ _} → ⊥.rec ∘ ¬nil↔cons 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           ; {_ ∷ _} {[]} → ⊥.rec ∘ ¬cons↔nil
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           ; {x ∷ xs} {y ∷ ys} r → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    -- (GQ.rec isTrans↔ trunc List→FMSet2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --  (λ {a} {b} → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --   (λ {a} {b} {c} _ _ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --     compPath-filler _ _ ▷ {!!}) x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --     , {!!}    



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   w : Iso _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   Iso.fun w = toFM
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   Iso.inv w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   Iso.rightInv w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   Iso.leftInv w = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- IsoList//↔FMSet2 : ∀ n → Iso (Σ (List//↔ A) ((n ≡_) ∘ length//))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                        (Σ (FMSet2 A) ((n ≡_) ∘ len2))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- IsoList//↔FMSet2 {A = A} n = {!!}





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet2≡ : (a b : List A) → a ↔ b → List→FMSet2 a ≡ List→FMSet2 b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet2≡ [] [] _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet2≡ [] (_ ∷ _) = ⊥.rec ∘ ¬nil↔cons
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet2≡ (_ ∷ _) [] = ⊥.rec ∘ ¬cons↔nil
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet2≡ {A = A} (x ∷ xs) (y ∷ ys) r@(prm e _) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    let (e' , p') = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        k' = equivFun e zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        xs' = permute xs (invEquiv e')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (prm _ p⁻) = isSym↔ _ _ r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       _ ≡⟨ cong (x ∷fm2_) (↔→FMSet2≡ xs xs' (↔permute xs (invEquiv e'))) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       _ ≡⟨ PunchHeadInOut//≡⁻ x xs' (subst Fin pL k') ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       _ ≡⟨⟩ cong List→FMSet2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     (rot≃∙ₑ≡→Fin≃ pL k')) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                            (invEq (rot≃ k'))  ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p') ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻)) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨⟩ tabulate-lookup (y ∷ ys))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- ↔→FMSet≡2TransH : (x y z : A) (xs ys zs : List A) → (p : x ∷ xs ↔ y ∷ ys) → (q : y ∷ ys ↔ z ∷ zs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --                   → {!!} ≡ {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- ↔→FMSet≡2TransH = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- {-# TERMINATING  #-}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet≡2Trans : (a b c : List A) → (p : a ↔ b) → (q : b ↔ c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   → ↔→FMSet2≡ a b p ∙ ↔→FMSet2≡ b c q ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     ↔→FMSet2≡ a c (isTrans↔ a b c p q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet≡2Trans [] [] [] _ _ = sym (doubleCompPath-filler refl _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet≡2Trans [] [] (_ ∷ _) _ q = ⊥.rec (¬nil↔cons q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet≡2Trans [] (_ ∷ _) _ p _ = ⊥.rec (¬nil↔cons p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet≡2Trans (_ ∷ _) [] _ p _ = ⊥.rec (¬cons↔nil p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet≡2Trans (_ ∷ _) (_ ∷ _) [] _ q = ⊥.rec (¬cons↔nil q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ↔→FMSet≡2Trans (x ∷ xs) (y ∷ ys) (z ∷ zs) r*@(prm f q) r**@(prm g w) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   let r@(prm e p) = isTrans↔ (x ∷ xs) (y ∷ ys) (z ∷ zs) (prm f q) (prm g w)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (e' , p') = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       k' = equivFun e zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       xs' = permute xs (invEquiv e')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (prm _ p⁻) = isSym↔ _ _ r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       pL = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e')))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS0 = PunchHeadInOut//≡⁻ x xs' (subst Fin pL k')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS1 =  (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     (rot≃∙ₑ≡→Fin≃ pL k')) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                            (invEq (rot≃ k'))  ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p') ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻)) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨⟩ tabulate-lookup (z ∷ zs))
                  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS = LHS0 ∙ cong List→FMSet2 LHS1

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (e'* , p'*) = unwindPermHead f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       k'* = equivFun f zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       xs'* = permute xs (invEquiv e'*)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (prm _ p⁻*) = isSym↔ _ _ r*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       pL* = sym (length-tabulate _ (lookup (x ∷ xs) ∘ invEq (sucPerm e'*)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS0* = PunchHeadInOut//≡⁻ x xs'* (subst Fin pL* k'*)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS1* =  (_ ≡⟨ sym (congP (λ _ → permute (x ∷ xs'*))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     (rot≃∙ₑ≡→Fin≃ pL* k'*)) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ tabulate∘ (lookup (x ∷ xs) ∘ invEq (sucPerm e'*))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                            (invEq (rot≃ k'*))  ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ cong (permute (x ∷ xs) ∘ invEquiv) (sym p'*) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻*)) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨⟩ tabulate-lookup (y ∷ ys))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS* = LHS0* ∙ cong List→FMSet2 LHS1*



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (e'** , p'**) = unwindPermHead g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       k'** = equivFun g zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       xs'** = permute ys (invEquiv e'**)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (prm _ p⁻**) = isSym↔ _ _ r**
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       pL** = sym (length-tabulate _ (lookup (y ∷ ys) ∘ invEq (sucPerm e'**)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS0** = PunchHeadInOut//≡⁻ y xs'** (subst Fin pL** k'**)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS1** =  (_ ≡⟨ sym (congP (λ _ → permute (y ∷ xs'**))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     (rot≃∙ₑ≡→Fin≃ pL** k'**)) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ tabulate∘ (lookup (y ∷ ys) ∘ invEq (sucPerm e'**))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                            (invEq (rot≃ k'**))  ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ cong (permute (y ∷ ys) ∘ invEquiv) (sym p'**) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨ cong (tabulate _) (sym (funExt p⁻**)) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            _ ≡⟨⟩ tabulate-lookup (z ∷ zs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS** = LHS0** ∙ cong List→FMSet2 LHS1**



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       pp = ↔→FMSet≡2Trans xs xs'* xs' (↔permute _ (invEquiv e'*))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 (sym↔ (↔permute xs (invEquiv e'*)) ∙↔ ↔permute xs (invEquiv e'))
 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       pp' : ↔→FMSet2≡ xs xs'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (isTrans↔ xs xs'* xs' (↔permute _ (invEquiv e'*))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 (sym↔ (↔permute xs (invEquiv e'*)) ∙↔ ↔permute xs (invEquiv e')))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             ↔→FMSet2≡ xs xs' (↔permute xs (invEquiv e'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       pp' = cong (↔→FMSet2≡ xs xs')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              (cong₂ prm (equivEq {!!}) {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       MHS = cong (y ∷fm2_) (↔→FMSet2≡ ys xs'** (↔permute ys (invEquiv e'**)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       zzz : _ ≡ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       zzz = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       vvv : _ ≡ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       vvv = cong (y ∷fm2_)  (↔→FMSet2≡ (ys) (permute ys ((invEquiv (fst (unwindPermHead (g))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (↔permute ys (invEquiv (fst (unwindPermHead g))))) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             ↔→FMSet2≡ ((y ∷ permute ys ((invEquiv (fst (unwindPermHead (g)))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                        (x ∷ permute xs ((invEquiv (fst (unwindPermHead (f ∙ₑ g))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS1= : (LHS1**) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                zzz ∙ LHS1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS1= = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS0= : MHS ∙ LHS0**  ≡ vvv ∙ LHS0 ∙ cong List→FMSet2 (sym zzz) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS0= = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS00 : LHS* ≡ cong (x ∷fm2_) (↔→FMSet2≡ xs'* xs' (sym↔ (↔permute xs (invEquiv e'*))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               ∙↔ ↔permute xs (invEquiv e'))) ∙ sym vvv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       LHS00 = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       -- qqH =  sym (cong-∙ (x ∷fm2_) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       --        ∙ (cong (cong (x ∷fm2_))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       --        (↔→FMSet≡2Trans _ _ _ (sym↔ (↔permute xs (invEquiv e'*))) ((↔permute xs (invEquiv e')))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       qq : LHS* ∙ MHS ∙ LHS** ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             cong (x ∷fm2_) (↔→FMSet2≡ xs'* xs' (sym↔ (↔permute xs (invEquiv e'*))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               ∙↔ ↔permute xs (invEquiv e'))) ∙ LHS 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       qq = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       -- lemP : (↔→FMSet2≡ (permute xs (invEquiv (fst (unwindPermHead f))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       --         (permute xs (invEquiv (fst (unwindPermHead (f ∙ₑ g)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       --         (sym↔ (↔permute xs (invEquiv (fst (unwindPermHead f)))) ∙↔
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       --          ↔permute xs (invEquiv (fst (unwindPermHead (f ∙ₑ g))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       --          ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       --          ≡ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       -- lemP = {!pp!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       -- p0 : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       p0 = cong (cong (x ∷fm2_)) (pp ∙ pp')

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   in (sym (assoc _ _ _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          (cong (cong (x ∷fm2_) (↔→FMSet2≡ xs xs'* (↔permute _ (invEquiv e'*))) ∙_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             qq)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             assoc _ _ _)         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        ∙ (cong (_∙ LHS) (sym (cong-∙ (x ∷fm2_) _ _) ∙ p0))
         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   -- sym (assoc _ _ _) ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   -- sym (assoc _ _ _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   --    (cong ((cong List→FMSet2 (sym (tabulate-lookup (x ∷ xs)))) ∙_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   --      (sym (assoc _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   --         ∙  cong ((cong (List→FMSet2 ∘ tabulate _) (funExt p)) ∙_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   --        ∙ assoc _ _ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   --       ∙ cong₂ _∙_ (sym (cong-∙ (List→FMSet2 ∘ tabulate _) (funExt p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   --                         (cong (_∘ (equivFun e)) (funExt q))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   --                       {!!}))
     
         


  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- IsoList//↔FMSet2 : Iso (List//↔ A) (FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- IsoList//↔FMSet2 {A = A} = w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     toFM : _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     toFM = GQ.rec isTrans↔ trunc List→FMSet2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       (λ {a} {b} → ↔→FMSet2≡ a b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        λ {a} {b} {c} _ _ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          compPath-filler _ _ ▷ ↔→FMSet≡2Trans a b c _ _     

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     fromFM : _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     fromFM =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       FM2.Rec.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        squash// [ [] ]// _∷//_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (λ x y → GQ.elimSet _ (λ _ → squash// _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (λ _ → eq// headSwap↔) (λ {a} {b} r i j → h x y {a} {b} r j i) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (λ x y → GQ.elimProp _ (λ _ → squash// _ _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (hSym x y ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        {!!}

      

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          h'' : ∀ x y → {a b : List A} (r : a ↔ b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     (λ i → (y ∷// (x ∷// eq// {a = a} {b} r i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   ≡ eq// (y ∷↔ (x ∷↔ r))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          h'' x y r =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               cong eq// (cong₂ prm refl 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (funExt λ { zero → refl ; one → refl ; (suc (suc k)) → refl }))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          h' : ∀ x y → {a b : List A} (r : a ↔ b) → Path (Path (List//↔ A) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  ((eq// (x ∷↔ (y ∷↔ r))) ∙ eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  (eq// headSwap↔ ∙ (eq// (y ∷↔ (x ∷↔ r))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          h' x y r = sym (comp'// _ _ _ _) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                      cong eq// (cong₂ prm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                        (equivEq (funExt λ { zero → refl ; one → refl ; (suc (suc k)) → refl }))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                        ( (funExt λ { zero → refl ; one → refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                          ; (suc (suc k)) → sym (leftright refl _) })))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     ∙∙  comp'// _ _ _ _ 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          h : ∀ x y → {a b : List A} (r : a ↔ b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  (λ i → (x ∷// (y ∷// eq// r i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  (λ i → (y ∷// (x ∷// eq// r i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  (eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  (eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          h x y r =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               (h'' y x r) ◁ doubleCompPath-filler (sym (eq// headSwap↔)) _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                       (eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              ▷ (doubleCompPath-elim (sym (eq// headSwap↔)) _ _ ∙ sym (assoc _ _ _) ∙ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (cong ((sym (eq// headSwap↔)) ∙_) (h' x y r) ∙ assoc _ _ _ ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   cong (_∙ (eq// (y ∷↔ (x ∷↔ r)))) (lCancel (eq// headSwap↔)) ∙ sym (lUnit _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                    ∙ sym (h'' x y r))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          hSym : ∀ x y → (a : List A) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                    eq// (headSwap↔ {x = x} {y = y} {a})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                      ≡ sym (eq// headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          hSym x y a = invEq (compr≡Equiv _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                          ((sym (comp'// _ _ _ headSwap↔)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                ∙ cong eq// (cong₂ prm (equivEq (funExt (secEq swap0and1≃)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   (funExt λ { zero → sym compPathRefl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                             ; one → sym compPathRefl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                             ; (suc (suc x)) → sym compPathRefl }))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                ∙ ↔→FMSet2≡Refl _ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             ∙ sym (lCancel _))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     h∷/ : ∀ x → {a b : List A} (r : a ↔ b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 (λ i → ((x ∷// eq// {a = a} {b} r i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               ≡ eq// ((x ∷↔ r))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     h∷/ x r =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           cong eq// (cong₂ prm refl 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           (funExt λ { zero → refl ; (suc k) → refl }))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     lll : ∀ x xs → toFM (x ∷// xs) ≡ x ∷fm2 toFM xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     lll x = GQ.elimSet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         isTrans↔
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         (λ _ → trunc _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         λ r i j → ss r j i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        ss : ∀ {a b : List A} → (r : a ↔ b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                    Path (Path (FMSet2 A) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                       (λ i → toFM (x ∷// (eq// r i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                       (λ i →  x ∷fm2 toFM (eq// r i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        ss r = cong (cong toFM) (h∷/ x r) ∙ {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w : Iso (List//↔ A) (FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     Iso.fun w = toFM
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     Iso.inv w = fromFM
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     Iso.rightInv w =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       FM2.ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         (λ x {xs} p → lll x (fromFM xs) ∙ cong (x ∷fm2_) p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         λ _ →  trunc _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       -- FM.ElimProp.f (trunc _ _) refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       --   λ a {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       --     ((SQ.elimProp {P = λ x → toFM (a ∷/ x) ≡ _ ∷fm toFM x}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       --          (λ _ → trunc _ _) (λ _ → refl) ∘ fromFM) xs ∙_) ∘ cong (_ ∷fm_)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     Iso.leftInv w =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       GQ.elimSet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         (λ _ → squash// _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         (ind refl (cong (_ ∷//_)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      -- SQ.elimProp (λ x → squash/ _ _) (ind refl (cong (_ ∷/_)))
