{-# OPTIONS --safe #-}
module Cubical.Foundations.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Reflection.StrictEquiv

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

-- Less polymorphic version of `cong`, to avoid some unresolved metas
cong′ : ∀ {B : Type ℓ'} (f : A → B) {x y : A} (p : x ≡ y)
      → Path B (f x) (f y)
cong′ f = cong f
{-# INLINE cong′ #-}

module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where
  toPathP⁻ : x ≡ transport⁻ (λ i → A i) y → PathP A x y
  toPathP⁻ p = symP (toPathP (sym p))

  fromPathP⁻ : PathP A x y → x ≡ transport⁻ (λ i → A i) y
  fromPathP⁻ p = sym (fromPathP {A = λ i → A (~ i)} (symP p))

PathP≡Path : ∀ (P : I → Type ℓ) (p : P i0) (q : P i1) →
             PathP P p q ≡ Path (P i1) (transport (λ i → P i) p) q
PathP≡Path P p q i = PathP (λ j → P (i ∨ j)) (transport-filler (λ j → P j) p i) q

PathP≡Path⁻ : ∀ (P : I → Type ℓ) (p : P i0) (q : P i1) →
             PathP P p q ≡ Path (P i0) p (transport⁻ (λ i → P i) q)
PathP≡Path⁻ P p q i = PathP (λ j → P (~ i ∧ j)) p (transport⁻-filler (λ j → P j) q i)

PathPIsoPath : ∀ (A : I → Type ℓ) (x : A i0) (y : A i1) → Iso (PathP A x y) (transport (λ i → A i) x ≡ y)
PathPIsoPath A x y .Iso.fun = fromPathP
PathPIsoPath A x y .Iso.inv = toPathP
PathPIsoPath A x y .Iso.rightInv q k i =
  hcomp
    (λ j → λ
      { (i = i0) → slide (j ∨ ~ k)
      ; (i = i1) → q j
      ; (k = i0) → transp (λ l → A (i ∨ l)) i (fromPathPFiller j)
      ; (k = i1) → ∧∨Square i j
      })
    (transp (λ l → A (i ∨ ~ k ∨ l)) (i ∨ ~ k)
      (transp (λ l → (A (i ∨ (~ k ∧ l)))) (k ∨ i)
        (transp (λ l → A (i ∧ l)) (~ i)
          x)))
  where
  fromPathPFiller : _
  fromPathPFiller =
    hfill
      (λ j → λ
        { (i = i0) → x
        ; (i = i1) → q j })
      (inS (transp (λ j → A (i ∧ j)) (~ i) x))

  slide : I → _
  slide i = transp (λ l → A (i ∨ l)) i (transp (λ l → A (i ∧ l)) (~ i) x)

  ∧∨Square : I → I → _
  ∧∨Square i j =
    hcomp
      (λ l → λ
        { (i = i0) → slide j
        ; (i = i1) → q (j ∧ l)
        ; (j = i0) → slide i
        ; (j = i1) → q (i ∧ l)
        })
      (slide (i ∨ j))
PathPIsoPath A x y .Iso.leftInv q k i =
  outS
    (hcomp-unique
      (λ j → λ
        { (i = i0) → x
        ; (i = i1) → transp (λ l → A (j ∨ l)) j (q j)
        })
      (inS (transp (λ l → A (i ∧ l)) (~ i) x))
      (λ j → inS (transp (λ l → A (i ∧ (j ∨ l))) (~ i ∨ j) (q (i ∧ j)))))
    k

PathP≃Path : (A : I → Type ℓ) (x : A i0) (y : A i1) →
             PathP A x y ≃ (transport (λ i → A i) x ≡ y)
PathP≃Path A x y = isoToEquiv (PathPIsoPath A x y)

PathP≡compPath : ∀ {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
                 → (PathP (λ i → x ≡ q i) p r) ≡ (p ∙ q ≡ r)
PathP≡compPath p q r k = PathP (λ i → p i0 ≡ q (i ∨ k)) (λ j → compPath-filler p q k j) r

-- a quick corollary for 3-constant functions
3-ConstantCompChar : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (link : 2-Constant f)
                   → (∀ x y z → link x y ∙ link y z ≡ link x z)
                   → 3-Constant f
3-Constant.link (3-ConstantCompChar f link coh₂) = link
3-Constant.coh₁ (3-ConstantCompChar f link coh₂) _ _ _ =
   transport⁻ (PathP≡compPath _ _ _) (coh₂ _ _ _)

PathP≡doubleCompPathˡ : ∀ {A : Type ℓ} {w x y z : A} (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
                        → (PathP (λ i → p i ≡ s i) q r) ≡ (p ⁻¹ ∙∙ q ∙∙ s ≡ r)
PathP≡doubleCompPathˡ p q r s k = PathP (λ i → p (i ∨ k) ≡ s (i ∨ k))
                                        (λ j → doubleCompPath-filler (p ⁻¹) q s k j) r

PathP≡doubleCompPathʳ : ∀ {A : Type ℓ} {w x y z : A} (p : w ≡ y) (q : w ≡ x) (r : y ≡ z) (s : x ≡ z)
                        → (PathP (λ i → p i ≡ s i) q r) ≡ (q ≡ p ∙∙ r ∙∙ s ⁻¹)
PathP≡doubleCompPathʳ p q r s k  = PathP (λ i → p (i ∧ (~ k)) ≡ s (i ∧ (~ k)))
                                         q (λ j → doubleCompPath-filler p r (s ⁻¹) k j)

compPathl-cancel : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → p ∙ (sym p ∙ q) ≡ q
compPathl-cancel p q = p ∙ (sym p ∙ q) ≡⟨ assoc p (sym p) q ⟩
                       (p ∙ sym p) ∙ q ≡⟨ cong (_∙ q) (rCancel p) ⟩
                              refl ∙ q ≡⟨ sym (lUnit q) ⟩
                                     q ∎

compPathr-cancel : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : z ≡ y) (q : x ≡ y) → (q ∙ sym p) ∙ p ≡ q
compPathr-cancel {x = x} p q i j =
  hcomp-equivFiller (doubleComp-faces (λ _ → x) (sym p) j) (inS (q j)) (~ i)

compPathl-isEquiv : {x y z : A} (p : x ≡ y) → isEquiv (λ (q : y ≡ z) → p ∙ q)
compPathl-isEquiv p = isoToIsEquiv (iso (p ∙_) (sym p ∙_) (compPathl-cancel p) (compPathl-cancel (sym p)))

compPathlEquiv : {x y z : A} (p : x ≡ y) → (y ≡ z) ≃ (x ≡ z)
compPathlEquiv p = (p ∙_) , compPathl-isEquiv p

compPathr-isEquiv : {x y z : A} (p : y ≡ z) → isEquiv (λ (q : x ≡ y) → q ∙ p)
compPathr-isEquiv p = isoToIsEquiv (iso (_∙ p) (_∙ sym p) (compPathr-cancel p) (compPathr-cancel (sym p)))

compPathrEquiv : {x y z : A} (p : y ≡ z) → (x ≡ y) ≃ (x ≡ z)
compPathrEquiv p = (_∙ p) , compPathr-isEquiv p

-- Variations of isProp→isSet for PathP
isProp→SquareP : ∀ {B : I → I → Type ℓ} → ((i j : I) → isProp (B i j))
             → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
             → (r : PathP (λ j → B j i0) a c) (s : PathP (λ j → B j i1) b d)
             → (t : PathP (λ j → B i0 j) a b) (u : PathP (λ j → B i1 j) c d)
             → SquareP B t u r s
isProp→SquareP {B = B} isPropB {a = a} r s t u i j =
  hcomp (λ { k (i = i0) → isPropB i0 j (base i0 j) (t j) k
           ; k (i = i1) → isPropB i1 j (base i1 j) (u j) k
           ; k (j = i0) → isPropB i i0 (base i i0) (r i) k
           ; k (j = i1) → isPropB i i1 (base i i1) (s i) k
        }) (base i j) where
    base : (i j : I) → B i j
    base i j = transport (λ k → B (i ∧ k) (j ∧ k)) a

isProp→isPropPathP : ∀ {ℓ} {B : I → Type ℓ} → ((i : I) → isProp (B i))
                   → (b0 : B i0) (b1 : B i1)
                   → isProp (PathP (λ i → B i) b0 b1)
isProp→isPropPathP {B = B} hB b0 b1 = isProp→SquareP (λ _ → hB) refl refl

isProp→isContrPathP : {A : I → Type ℓ} → (∀ i → isProp (A i))
                    → (x : A i0) (y : A i1)
                    → isContr (PathP A x y)
isProp→isContrPathP h x y = isProp→PathP h x y , isProp→isPropPathP h x y _

-- Flipping a square along its diagonal

flipSquare : {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  → Square a₀₋ a₁₋ a₋₀ a₋₁ → Square a₋₀ a₋₁ a₀₋ a₁₋
flipSquare sq i j = sq j i


flipSquareP :  {A : I → I → Type ℓ}
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
  {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀}
  {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
  → SquareP A  a₀₋ a₁₋ a₋₀ a₋₁ → SquareP (λ i j → A j i) a₋₀ a₋₁ a₀₋ a₁₋
flipSquareP sq i j = sq j i


module _ {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁} {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  where

  flipSquareEquiv : Square a₀₋ a₁₋ a₋₀ a₋₁ ≃ Square a₋₀ a₋₁ a₀₋ a₁₋
  unquoteDef flipSquareEquiv = defStrictEquiv flipSquareEquiv flipSquare flipSquare

  flipSquarePath : Square a₀₋ a₁₋ a₋₀ a₋₁ ≡ Square a₋₀ a₋₁ a₀₋ a₁₋
  flipSquarePath = ua flipSquareEquiv

module _ {a₀₀ a₁₁ : A} {a₋ : a₀₀ ≡ a₁₁}
  {a₁₀ : A} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₀ : a₀₀ ≡ a₁₀} where

  slideSquareFaces : (i j k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) A
  slideSquareFaces i j k (i = i0) = a₋ (j ∧ ~ k)
  slideSquareFaces i j k (i = i1) = a₁₋ j
  slideSquareFaces i j k (j = i0) = a₋₀ i
  slideSquareFaces i j k (j = i1) = a₋ (i ∨ ~ k)

  slideSquare : Square a₋ a₁₋ a₋₀ refl → Square refl a₁₋ a₋₀ a₋
  slideSquare sq i j = hcomp (slideSquareFaces i j) (sq i j)

  slideSquareEquiv : (Square a₋ a₁₋ a₋₀ refl) ≃ (Square refl a₁₋ a₋₀ a₋)
  slideSquareEquiv = isoToEquiv (iso slideSquare slideSquareInv fillerTo fillerFrom) where
    slideSquareInv : Square refl a₁₋ a₋₀ a₋ → Square a₋ a₁₋ a₋₀ refl
    slideSquareInv sq i j = hcomp (λ k → slideSquareFaces i j (~ k)) (sq i j)
    fillerTo : ∀ p → slideSquare (slideSquareInv p) ≡ p
    fillerTo p k i j = hcomp-equivFiller (λ k → slideSquareFaces i j (~ k)) (inS (p i j)) (~ k)
    fillerFrom : ∀ p → slideSquareInv (slideSquare p) ≡ p
    fillerFrom p k i j = hcomp-equivFiller (slideSquareFaces i j) (inS (p i j)) (~ k)

  q∙p≡r→p≡q⁻1∙r : a₋₀ ∙ a₁₋ ≡ a₋ → a₁₋ ≡ sym a₋₀ ∙ a₋ 
  q∙p≡r→p≡q⁻1∙r s i j =
     hcomp (λ k → λ {
           (i = i0) → compPath-filler a₋₀ a₁₋ j k
         ; (j = i0) → a₋₀ (k ∨ i)
         ; (j = i1) → s i k
         }) (a₋₀ (~ j ∧ i))
        

-- The type of fillers of a square is equivalent to the double composition identites
Square≃doubleComp : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
                    (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁)
                    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
                    → Square a₀₋ a₁₋ a₋₀ a₋₁ ≃ (a₋₀ ⁻¹ ∙∙ a₀₋ ∙∙ a₋₁ ≡ a₁₋)
Square≃doubleComp a₀₋ a₁₋ a₋₀ a₋₁ = pathToEquiv (PathP≡doubleCompPathˡ a₋₀ a₀₋ a₁₋ a₋₁)

-- Flipping a square in Ω²A is the same as inverting it
sym≡flipSquare : {x : A} (P : Square (refl {x = x}) refl refl refl)
  → sym P ≡ flipSquare P
sym≡flipSquare {x = x} P = sym (main refl P)
  where
  B : (q : x ≡ x) → I → Type _
  B q i = PathP (λ j → x ≡ q (i ∨ j)) (λ k → q (i ∧ k)) refl

  main : (q : x ≡ x) (p : refl ≡ q) → PathP (λ i → B q i) (λ i j → p j i) (sym p)
  main q = J (λ q p → PathP (λ i → B q i) (λ i j → p j i) (sym p)) refl

-- Inverting both interval arguments of a square in Ω²A is the same as doing nothing
sym-cong-sym≡id : {x : A} (P : Square (refl {x = x}) refl refl refl)
  → P ≡ λ i j → P (~ i) (~ j)
sym-cong-sym≡id {x = x} P = sym (main refl P)
  where
  B : (q : x ≡ x) → I → Type _
  B q i = Path (x ≡ q i) (λ j → q (i ∨ ~ j)) λ j → q (i ∧ j)

  main : (q : x ≡ x) (p : refl ≡ q) → PathP (λ i → B q i) (λ i j → p (~ i) (~ j)) p
  main q = J (λ q p → PathP (λ i → B q i) (λ i j → p (~ i) (~ j)) p) refl

-- Applying cong sym is the same as flipping a square in Ω²A
flipSquare≡cong-sym : ∀ {ℓ} {A : Type ℓ} {x : A} (P : Square (refl {x = x}) refl refl refl)
  → flipSquare P ≡ λ i j → P i (~ j)
flipSquare≡cong-sym P = sym (sym≡flipSquare P) ∙ sym (sym-cong-sym≡id (cong sym P))

-- Applying cong sym is the same as inverting a square in Ω²A
sym≡cong-sym : ∀ {ℓ} {A : Type ℓ} {x : A} (P : Square (refl {x = x}) refl refl refl)
  → sym P ≡ cong sym P
sym≡cong-sym P = sym-cong-sym≡id (sym P)

-- sym induces an equivalence on path types
symIso : {a b : A} → Iso (a ≡ b) (b ≡ a)
symIso = iso sym sym (λ _ → refl) λ _ → refl

-- Inspect

module _ {A : Type ℓ} {B : Type ℓ'} where

  record Reveal_·_is_ (f : A → B) (x : A) (y : B) : Type (ℓ-max ℓ ℓ') where
    constructor [_]ᵢ
    field path : f x ≡ y

  inspect : (f : A → B) (x : A) → Reveal f · x is f x
  inspect f x .Reveal_·_is_.path = refl

-- J is an equivalence
Jequiv : {x : A} (P : ∀ y → x ≡ y → Type ℓ') → P x refl ≃ (∀ {y} (p : x ≡ y) → P y p)
Jequiv P = isoToEquiv isom
  where
  isom : Iso _ _
  Iso.fun isom = J P
  Iso.inv isom f = f refl
  Iso.rightInv isom f =
    implicitFunExt λ {_} →
    funExt λ t →
    J (λ _ t → J P (f refl) t ≡ f t) (JRefl P (f refl)) t
  Iso.leftInv isom = JRefl P

-- Action of PathP on equivalences (without relying on univalence)

congPathIso : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : I → Type ℓ'}
  (e : ∀ i → A i ≃ B i) {a₀ : A i0} {a₁ : A i1}
  → Iso (PathP A a₀ a₁) (PathP B (e i0 .fst a₀) (e i1 .fst a₁))
congPathIso {A = A} {B} e {a₀} {a₁} .Iso.fun p i = e i .fst (p i)
congPathIso {A = A} {B} e {a₀} {a₁} .Iso.inv q i =
  hcomp
    (λ j → λ
      { (i = i0) → retEq (e i0) a₀ j
      ; (i = i1) → retEq (e i1) a₁ j
      })
    (invEq (e i) (q i))
congPathIso {A = A} {B} e {a₀} {a₁} .Iso.rightInv q k i =
  hcomp
    (λ j → λ
      { (i = i0) → commSqIsEq (e i0 .snd) a₀ j k
      ; (i = i1) → commSqIsEq (e i1 .snd) a₁ j k
      ; (k = i0) →
        e i .fst
          (hfill
            (λ j → λ
              { (i = i0) → retEq (e i0) a₀ j
              ; (i = i1) → retEq (e i1) a₁ j
              })
            (inS (invEq (e i) (q i)))
            j)
      ; (k = i1) → q i
      })
    (secEq (e i) (q i) k)
    where b = commSqIsEq
congPathIso {A = A} {B} e {a₀} {a₁} .Iso.leftInv p k i =
  hcomp
    (λ j → λ
      { (i = i0) → retEq (e i0) a₀ (j ∨ k)
      ; (i = i1) → retEq (e i1) a₁ (j ∨ k)
      ; (k = i1) → p i
      })
    (retEq (e i) (p i) k)

congPathEquiv : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : I → Type ℓ'}
  (e : ∀ i → A i ≃ B i) {a₀ : A i0} {a₁ : A i1}
  → PathP A a₀ a₁ ≃ PathP B (e i0 .fst a₀) (e i1 .fst a₁)
congPathEquiv e = isoToEquiv (congPathIso e)

congSqP : ∀ {ℓ ℓ'} {A : I → I → Type ℓ} {B : I → I → Type ℓ'}
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
  {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
  → (f : ∀ i j → A i j → B i j)
  → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
  → SquareP B (congP (f i0) a₀₋) (congP (f i1) a₁₋)
              (congP (λ i → f i i0) a₋₀) (congP (λ i → f i i1) a₋₁)
congSqP f sq i j = f i j (sq i j)
{-# INLINE congSqP #-}


congSq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} (f : A → B)
  → Square (a₀₋) (a₁₋) (a₋₀) (a₋₁)
  → Square (cong f a₀₋) (cong f a₁₋) (cong f a₋₀) (cong f a₋₁)
congSq {a₀₋ = a₀₋} {a₁₋ = a₁₋} {a₋₀ = a₋₀} {a₋₁ = a₋₁}  f sq i j = f (sq i j)
{-# INLINE congSq #-}


congSq' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  (f : ∀ a → B a)
  → (s : Square (a₀₋) (a₁₋) (a₋₀) (a₋₁))
  → SquareP (λ i j → B (s i j))  (cong f a₀₋) (cong f a₁₋) (cong f a₋₀) (cong f a₋₁)
congSq' {a₀₋ = a₀₋} {a₁₋ = a₁₋} {a₋₀ = a₋₀} {a₋₁ = a₋₁}  f sq i j = f (sq i j)
{-# INLINE congSq' #-}


-- Characterizations of dependent paths in path types

doubleCompPath-filler∙ : {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
  → PathP (λ i → p i ≡ r (~ i)) (p ∙ q ∙ r) q
doubleCompPath-filler∙ {A = A} {b = b} p q r j i =
  hcomp (λ k → λ { (i = i0) → p j
                  ; (i = i1) → side j k
                  ; (j = i1) → q (i ∧ k)})
        (p (j ∨ i))
  where
  side : I → I → A
  side i j =
    hcomp (λ k → λ { (i = i1) → q j
                    ; (j = i0) → b
                    ; (j = i1) → r (~ i ∧ k)})
          (q j)

PathP→compPathL : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
  → PathP (λ i → p i ≡ q i) r s
  → sym p ∙ r ∙ q ≡ s
PathP→compPathL {p = p} {q = q} {r = r} {s = s} P j i =
  hcomp (λ k → λ { (i = i0) → p (j ∨ k)
                 ; (i = i1) → q (j ∨ k)
                 ; (j = i0) → doubleCompPath-filler∙ (sym p) r q (~ k) i
                 ; (j = i1) → s i })
        (P j i)

PathP→compPathR : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
  → PathP (λ i → p i ≡ q i) r s
  → r ≡ p ∙ s ∙ sym q
PathP→compPathR {p = p} {q = q} {r = r} {s = s} P j i =
  hcomp (λ k → λ { (i = i0) → p (j ∧ (~ k))
                 ; (i = i1) → q (j ∧ (~ k))
                 ; (j = i0) → r i
                 ; (j = i1) → doubleCompPath-filler∙ p s (sym q) (~ k) i})
        (P j i)


PathP→compPathR' : {a b c d : A} {p p' : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
  → (p ≡ p')
  → PathP (λ i → p i ≡ q i) r s
  → Square q s
           (sym r ∙∙ refl ∙∙ p')
           refl
PathP→compPathR' {p = p} {q = q} {r = r} {s = s} p=p' P j i =
  
  hcomp (λ k → λ { (i = i0) →
                    hcomp (λ k' → λ {
                              (j = i0) → r (k' ∧ k)
                            ; (j = i1) → p=p' k k'
                            ; (k = i0) → p (k' ∧ j)}
                            )
                          (r i0) 
                 ; (i = i1) → q (j ∨ k) 
                 ; (j = i0) → invSides-filler q (sym r) (~ i) k
                 ; (j = i1) → s i})
        (P j i)


-- Other direction

compPathL→PathP : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
  → sym p ∙ r ∙ q ≡ s
  → PathP (λ i → p i ≡ q i) r s
compPathL→PathP {p = p} {q = q} {r = r} {s = s} P j i =
  hcomp (λ k → λ { (i = i0) → p (~ k ∨ j)
                 ; (i = i1) → q (~ k ∨ j)
                 ; (j = i0) → doubleCompPath-filler∙ (sym p) r q k i
                 ; (j = i1) → s i})
        (P j i)

compPathR→PathP : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
  → r ≡ p ∙ s ∙ sym q
  → PathP (λ i → p i ≡ q i) r s
compPathR→PathP {p = p} {q = q} {r = r} {s = s} P j i =
  hcomp (λ k → λ { (i = i0) → p (k ∧ j)
                 ; (i = i1) → q (k ∧ j)
                 ; (j = i0) → r i
                 ; (j = i1) → doubleCompPath-filler∙  p s (sym q) k i})
        (P j i)

PathP∙∙→compPathR : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}  
  → PathP (λ i → p i ≡ q i) r s
  → r ≡ p ∙∙ s ∙∙ sym q
PathP∙∙→compPathR {p = p} {q = q} {r = r} {s = s} P j i =
    hcomp (λ k → λ { (i = i0) → p (~ k ∧ j)
                   ; (i = i1) → q (~ k ∧ j)
                   ; (j = i0) → r i
                   ; (j = i1) → doubleCompPath-filler  p s (sym q) (k) i})
          (P j i)

PathP∙∙→compPathR' : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}  
  → PathP (λ i → p i ≡ q i) r s
  → Square refl refl r (p ∙∙ s ∙∙ sym q)
PathP∙∙→compPathR' {p = p} {q = q} {r = r} {s = s} P i j =
    hcomp (λ k → λ { (i = i0) → p (~ k ∧ j)
                   ; (i = i1) → q (~ k ∧ j)
                   ; (j = i0) → r i
                   ; (j = i1) → doubleCompPath-filler  p s (sym q) (k) i})
          (P j i)


compPathR→PathP∙∙ : {a b c d : A} {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d}
  → r ≡ p ∙∙ s ∙∙ sym q
  → PathP (λ i → p i ≡ q i) r s
compPathR→PathP∙∙ {p = p} {q = q} {r = r} {s = s} P j i =
    hcomp (λ k → λ { (i = i0) → p (k ∧ j)
                   ; (i = i1) → q (k ∧ j)
                   ; (j = i0) → r i
                   ; (j = i1) → doubleCompPath-filler  p s (sym q) (~ k) i})
          (P j i)


module _ {a b c d : A}  {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d} where

 comm↔PathP-sides : ∀ i j →  I → Partial _ A
 comm↔PathP-sides i j k = λ
       { (i = i0) → r (j ∧ k)
       ; (i = i1) → s (j ∨ ~ k)
       ; (j = i0) → compPath-filler p s (~ k) i
       ; (j = i1) → compPath-filler' r q (~ k) i }

 comm→PathP : 
     p ∙ s ≡ r ∙ q
   → PathP (λ i → p i ≡ q i) r s
 comm→PathP P i j =
   hcomp (comm↔PathP-sides i j)
     (P j i)

 PathP→comm : 
     PathP (λ i → p i ≡ q i) r s
   → p ∙ s ≡ r ∙ q
 PathP→comm P j i =
   hcomp
     (λ k → comm↔PathP-sides i j (~ k))
     (P i j)

 PathP→comm-Iso : Iso
   (p ∙ s ≡ r ∙ q)
   (Square p q r s) --(PathP (λ i → p i ≡ q i) r s)
 Iso.fun PathP→comm-Iso = flipSquare ∘ comm→PathP
 Iso.inv PathP→comm-Iso = PathP→comm ∘ flipSquare
 Iso.rightInv PathP→comm-Iso s k i j =
   hcomp-equivFiller (λ k → comm↔PathP-sides j i (~ k)) (inS (s i j)) (~ k) 
 Iso.leftInv PathP→comm-Iso s k i j =
   hcomp-equivFiller (comm↔PathP-sides j i) (inS (s i j)) (~ k)

module whiskSq (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
  {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
  {a₀₀' : A i0 i0} {a₀₁' : A i0 i1} {a₀₋' : PathP (λ j → A i0 j) a₀₀' a₀₁'}
  {a₁₀' : A i1 i0} {a₁₁' : A i1 i1} {a₁₋' : PathP (λ j → A i1 j) a₁₀' a₁₁'}
  {a₋₀' : PathP (λ i → A i i0) a₀₀' a₁₀'} {a₋₁' : PathP (λ i → A i i1) a₀₁' a₁₁'}
  (sq : SquareP A a₀₋ a₁₋ a₋₀ a₋₁)
  {p₀₀ : a₀₀ ≡ a₀₀'} {p₀₁ : a₀₁ ≡ a₀₁'} (p₀₋ : PathP (λ j → a₀₋ j ≡ a₀₋' j) p₀₀ p₀₁)
  {p₁₀ : a₁₀ ≡ a₁₀'} {p₁₁ : a₁₁ ≡ a₁₁'} (p₁₋ : PathP (λ j → a₁₋ j ≡ a₁₋' j) p₁₀ p₁₁)
  (p₋₀ : PathP (λ i → a₋₀ i ≡ a₋₀' i) p₀₀ p₁₀) (p₋₁ : PathP (λ i → a₋₁ i ≡ a₋₁' i) p₀₁ p₁₁)
    where


 sq' : SquareP A a₀₋' a₁₋' a₋₀' a₋₁'
 sq' i j =
   hcomp (λ l →
      λ { (i = i0) → p₀₋ j l
        ; (i = i1) → p₁₋ j l
        ; (j = i0) → p₋₀ i l
        ; (j = i1) → p₋₁ i l
        })
     (sq i j)
