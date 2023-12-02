{- Basic theory about transport:

- transport is invertible
- transport is an equivalence ([pathToEquiv])

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Transport where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv as Equiv hiding (transpEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function using (_∘_)

import Agda.Builtin.Cubical.HCompU as HCompU

-- Direct definition of transport filler, note that we have to
-- explicitly tell Agda that the type is constant (like in CHM)
transpFill : ∀ {ℓ} {A : Type ℓ}
             (φ : I)
             (A : (i : I) → Type ℓ [ φ ↦ (λ _ → A) ])
             (u0 : outS (A i0))
           → --------------------------------------
             PathP (λ i → outS (A i)) u0 (transp (λ i → outS (A i)) φ u0)
transpFill φ A u0 i = transp (λ j → outS (A (i ∧ j))) (~ i ∨ φ) u0

transport⁻ : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → B → A
transport⁻ p = transport (λ i → p (~ i))

subst⁻ : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (B : A → Type ℓ') (p : x ≡ y) → B y → B x
subst⁻ B p pa = transport⁻ (λ i → B (p i)) pa

subst⁻-filler : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (B : A → Type ℓ') (p : x ≡ y) (b : B y)
  → PathP (λ i → B (p (~ i))) b (subst⁻ B p b)
subst⁻-filler B p = subst-filler B (sym p)

transport-fillerExt : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                    → PathP (λ i → A → p i) (λ x → x) (transport p)
transport-fillerExt p i x = transport-filler p x i

transport⁻-fillerExt : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                     → PathP (λ i → p i → A) (λ x → x) (transport⁻ p)
transport⁻-fillerExt p i x = transp (λ j → p (i ∧ ~ j)) (~ i) x

transport-fillerExt⁻ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                    → PathP (λ i → p i → B) (transport p) (λ x → x)
transport-fillerExt⁻ p = symP (transport⁻-fillerExt (sym p))

transport⁻-fillerExt⁻ : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                     → PathP (λ i → B → p i) (transport⁻ p) (λ x → x)
transport⁻-fillerExt⁻ p = symP (transport-fillerExt (sym p))

transport⁻-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : B)
                   → PathP (λ i → p (~ i)) x (transport⁻ p x)
transport⁻-filler p x = transport-filler (λ i → p (~ i)) x

transport⁻Transport : ∀ {ℓ} {A B : Type ℓ} → (p : A ≡ B) → (a : A) →
                          transport⁻ p (transport p a) ≡ a
transport⁻Transport p a j = transport⁻-fillerExt p (~ j) (transport-fillerExt p (~ j) a)

transportTransport⁻ : ∀ {ℓ} {A B : Type ℓ} → (p : A ≡ B) → (b : B) →
                        transport p (transport⁻ p b) ≡ b
transportTransport⁻ p b j = transport-fillerExt⁻ p j (transport⁻-fillerExt⁻ p j b)

subst⁻Subst : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (B : A → Type ℓ') (p : x ≡ y)
              → (u : B x) → subst⁻ B p (subst B p u) ≡ u
subst⁻Subst {x = x} {y = y} B p u = transport⁻Transport {A = B x} {B = B y} (cong B p) u

substSubst⁻ : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (B : A → Type ℓ') (p : x ≡ y)
              → (v : B y) → subst B p (subst⁻ B p v) ≡ v
substSubst⁻ {x = x} {y = y} B p v = transportTransport⁻ {A = B x} {B = B y} (cong B p) v

substEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {a a' : A} (P : A → Type ℓ') (p : a ≡ a') → P a ≃ P a'
substEquiv P p = (subst P p , isEquivTransport (λ i → P (p i)))

liftEquiv : ∀ {ℓ ℓ'} {A B : Type ℓ} (P : Type ℓ → Type ℓ') (e : A ≃ B) → P A ≃ P B
liftEquiv P e = substEquiv P (ua e)

transpEquiv : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → ∀ i → p i ≃ B
transpEquiv p = Equiv.transpEquiv (λ i → p i)
{-# WARNING_ON_USAGE transpEquiv "Deprecated: Use the more general `transpEquiv` from `Cubical.Foundations.Equiv` instead" #-}

uaTransportη : ∀ {ℓ} {A B : Type ℓ} (P : A ≡ B) → ua (pathToEquiv P) ≡ P
uaTransportη = uaη
{-# WARNING_ON_USAGE uaTransportη "Deprecated: Use `uaη` from `Cubical.Foundations.Univalence` instead of `uaTransportη`" #-}

pathToIso : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → Iso A B
Iso.fun (pathToIso x) = transport x
Iso.inv (pathToIso x) = transport⁻ x
Iso.rightInv (pathToIso x) = transportTransport⁻ x
Iso.leftInv (pathToIso x) = transport⁻Transport x

substIso : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') {x y : A} (p : x ≡ y) → Iso (B x) (B y)
substIso B p = pathToIso (cong B p)

-- Redefining substEquiv in terms of substIso gives an explicit inverse
substEquiv' : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') {x y : A} (p : x ≡ y) → B x ≃ B y
substEquiv' B p = isoToEquiv (substIso B p)

isInjectiveTransport : ∀ {ℓ : Level} {A B : Type ℓ} {p q : A ≡ B}
  → transport p ≡ transport q → p ≡ q
isInjectiveTransport {p = p} {q} α i =
  hcomp
    (λ j → λ
      { (i = i0) → retEq univalence p j
      ; (i = i1) → retEq univalence q j
      })
    (invEq univalence ((λ a → α i a) , t i))
  where
  t : PathP (λ i → isEquiv (λ a → α i a)) (pathToEquiv p .snd) (pathToEquiv q .snd)
  t = isProp→PathP (λ i → isPropIsEquiv (λ a → α i a)) _ _

transportUaInv : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → transport (ua (invEquiv e)) ≡ transport (sym (ua e))
transportUaInv e = cong transport (uaInvEquiv e)
-- notice that transport (ua e) would reduce, thus an alternative definition using EquivJ can give
-- refl for the case of idEquiv:
-- transportUaInv e = EquivJ (λ _ e → transport (ua (invEquiv e)) ≡ transport (sym (ua e))) refl e

isSet-subst : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
                → (isSet-A : isSet A)
                → ∀ {a : A}
                → (p : a ≡ a) → (x : B a) → subst B p x ≡ x
isSet-subst {B = B} isSet-A p x = subst (λ p′ → subst B p′ x ≡ x) (isSet-A _ _ refl p) (substRefl {B = B} x)

-- substituting along a composite path is equivalent to substituting twice
substComposite : ∀ {ℓ ℓ'} {A : Type ℓ} → (B : A → Type ℓ')
                 → {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x)
                 → subst B (p ∙ q) u ≡ subst B q (subst B p u)
substComposite B p q Bx i =
  transport (cong B (compPath-filler' p q (~ i))) (transport-fillerExt (cong B p) i Bx)

-- transporting along a composite path is equivalent to transporting twice
transportComposite : ∀ {ℓ} {A B C : Type ℓ} (p : A ≡ B) (q : B ≡ C) (x : A)
                 → transport (p ∙ q) x ≡ transport q (transport p x)
transportComposite = substComposite (λ D → D)

-- substitution commutes with morphisms in slices
substCommSlice : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}
                   → (B : A → Type ℓ') (C : A → Type ℓ'')
                   → (F : ∀ a → B a → C a)
                   → {x y : A} (p : x ≡ y) (u : B x)
                   → subst C p (F x u) ≡ F y (subst B p u)
substCommSlice B C F p Bx a =
  transport-fillerExt⁻ (cong C p) a (F _ (transport-fillerExt (cong B p) a Bx))

constSubstCommSlice : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}
                   → (B : A → Type ℓ')
                   → (C : Type ℓ'')
                   → (F : ∀ a → B a → C)
                   → {x y : A} (p : x ≡ y) (u : B x)
                   →  (F x u) ≡ F y (subst B p u)
constSubstCommSlice B C F p Bx = (sym (transportRefl (F _ Bx)) ∙ substCommSlice B (λ _ → C) F p Bx)

-- transporting over (λ i → B (p i) → C (p i)) divides the transport into
-- transports over (λ i → C (p i)) and (λ i → B (p (~ i)))
funTypeTransp : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} (B : A → Type ℓ') (C : A → Type ℓ'') {x y : A} (p : x ≡ y) (f : B x → C x)
         → PathP (λ i → B (p i) → C (p i)) f (subst C p ∘ f ∘ subst B (sym p))
funTypeTransp B C {x = x} p f i b =
  transp (λ j → C (p (j ∧ i))) (~ i) (f (transp (λ j → B (p (i ∧ ~ j))) (~ i) b))


-- transports between loop spaces preserve path composition
overPathFunct : ∀ {ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ x) (P : x ≡ y)
           → transport (λ i → P i ≡ P i) (p ∙ q)
            ≡ transport (λ i → P i ≡ P i) p ∙ transport (λ i → P i ≡ P i) q
overPathFunct p q =
  J (λ y P → transport (λ i → P i ≡ P i) (p ∙ q) ≡ transport (λ i → P i ≡ P i) p ∙ transport (λ i → P i ≡ P i) q)
    (transportRefl (p ∙ q) ∙ cong₂ _∙_ (sym (transportRefl p)) (sym (transportRefl q)))


-- substition over families of paths
-- theorem 2.11.3 in The Book
substInPaths : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}  {a a' : A}
                 → (f g : A → B) → (p : a ≡ a') (q : f a ≡ g a)
                 → subst (λ x → f x ≡ g x) p q ≡ sym (cong f p) ∙ q ∙ cong g p
substInPaths {a = a} f g p q =
  J (λ x p' → (subst (λ y → f y ≡ g y) p' q) ≡ (sym (cong f p') ∙ q ∙ cong g p'))
    p=refl p
    where
    p=refl : subst (λ y → f y ≡ g y) refl q
           ≡ refl ∙ q ∙ refl
    p=refl = subst (λ y → f y ≡ g y) refl q
           ≡⟨ substRefl {B = (λ y → f y ≡ g y)} q ⟩ q
           ≡⟨ (rUnit q) ∙ lUnit (q ∙ refl) ⟩ refl ∙ q ∙ refl ∎

flipTransport : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
  → x ≡ transport⁻ (λ i → A i) y
  → transport (λ i → A i) x ≡ y
flipTransport {A = A} {y = y} p =
  cong (transport (λ i → A i)) p ∙ transportTransport⁻ (λ i → A i) y

-- special cases of substInPaths from lemma 2.11.2 in The Book
module _ {ℓ : Level} {A : Type ℓ} {a x1 x2 : A} (p : x1 ≡ x2) where
  substInPathsL : (q : a ≡ x1) → subst (λ x → a ≡ x) p q ≡ q ∙ p
  substInPathsL q = subst (λ x → a ≡ x) p q
    ≡⟨ substInPaths (λ _ → a) (λ x → x) p q ⟩
      sym (cong (λ _ → a) p) ∙ q ∙ cong (λ x → x) p
    ≡⟨ assoc (λ _ → a) q p ⟩
      (refl ∙ q) ∙ p
    ≡⟨ cong (_∙ p) (sym (lUnit q)) ⟩ q ∙ p ∎

  substInPathsR : (q : x1 ≡ a) → subst (λ x → x ≡ a) p q ≡ sym p ∙ q
  substInPathsR q = subst (λ x → x ≡ a) p q
    ≡⟨ substInPaths (λ x → x) (λ _ → a) p q ⟩
      sym (cong (λ x → x) p) ∙ q ∙ cong (λ _ → a) p
    ≡⟨ assoc (sym p) q refl ⟩
      (sym p ∙ q) ∙ refl
    ≡⟨ sym (rUnit (sym p ∙ q))⟩ sym p ∙ q ∎




private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : A → Type ℓ
    x y z w : A


doubleCompPathP' : {B : A → Type ℓ'} {w' : B w} {x' : B x} {y' : B y} {z' : B z} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z}
             (P : PathP (λ i → B (p i)) w' x') (Q : PathP (λ i → B (q i)) x' y') (R : PathP (λ i → B (r i)) y' z')
          → PathP (λ i → B ((p ∙∙ q ∙∙ r) i)) w' z'
doubleCompPathP' {B = B} {x' = x'} {p = p} {q = q} {r = r} P Q R i =
  comp (λ j → B (doubleCompPath-filler p q r j i))
       (λ j → λ { (i = i0) → P (~ j)  ;
                  (i = i1) → R j })
  (Q i)


doubleCompPathP'-filler : {B : A → Type ℓ'} {w' : B w} {x' : B x} {y' : B y} {z' : B z} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z}
             (P : PathP (λ i → B (p i)) w' x') (Q : PathP (λ i → B (q i)) x' y') (R : PathP (λ i → B (r i)) y' z')
  → PathP (λ j → PathP (λ i → B (doubleCompPath-filler p q r j i)) (P (~ j)) (R j)) Q (doubleCompPathP' {B = B} P Q R)
doubleCompPathP'-filler {B = B} {x' = x'} {p = p} {q = q} {r = r} P Q R j i =
  fill (λ j → B (doubleCompPath-filler p q r j i))
       (λ j → λ { (i = i0) → P (~ j)  ;
                  (i = i1) → R j })
       (inS (Q i))
       j



module _ {ℓ} {A B C D : Type ℓ} (A≡B : A ≡ B) (B≡C : B ≡ C) (C≡D : C ≡ D) where




    prim^unglueU-Sq0 : SquareP (λ i j → doubleCompPath-filler A≡B B≡C C≡D i j → B≡C j)
                            (λ j → transp (λ i → B≡C j) i0)
                            (λ j → HCompU.prim^unglueU
                                                 {φ = j ∨ ~ j}
                                                 {T = doubleComp-faces A≡B C≡D j}
                                                 {A = inS (B≡C j)})
                            (λ i → transp (λ i₁ → A≡B (i₁ ∨ ~ i)) i0)
                            (λ i → transp (λ i₁ → C≡D (~ i₁ ∧ i)) i0)
    prim^unglueU-Sq0 i j = HCompU.prim^unglueU
                                                 {φ = j ∨ ~ j ∨ ~ i}
                                                 {T = λ k →
                                                     λ { (j = i0) → A≡B (~ k ∨ (~ i))
                                                        ; (j = i1) → C≡D (~ (~ k ∨ (~ i))) 
                                                        ; (i = i0) → B≡C j
                                                         }}
                                                 {A = inS (B≡C j)}


    transport-fillerExt⁻-∙∙ : (transport-fillerExt⁻ (A≡B ∙∙ B≡C ∙∙ C≡D)) 
                                 ≡
                                 (doubleCompPathP' {B = λ X → X → D} 
                               (congP (λ _ → (transport C≡D ∘ transport B≡C) ∘_) (transport-fillerExt⁻ A≡B))
                               (congP (λ _ → transport C≡D ∘_)                   (transport-fillerExt⁻ B≡C))
                                                                                 (transport-fillerExt⁻ C≡D))
    transport-fillerExt⁻-∙∙ i j =  
       hcomp 
         (λ k →
           λ { (j = i0) → sqJ0 k
             ; (j = i1) → sqJ1 k
             ; (i = i1) → fill2 i1 j
          }) (fill3 j i1)
                                    
       where

         fill2 :  ∀ i j → doubleCompPath-filler A≡B B≡C C≡D i j → D
         fill2 i j = doubleCompPathP'-filler {B = λ X → X → D}
               (λ i₁ → transport C≡D ∘ transport B≡C ∘ (transport-fillerExt⁻ A≡B i₁))
               (λ i₁ → transport C≡D ∘ (transport-fillerExt⁻ B≡C i₁))
               (transport-fillerExt⁻ C≡D)
               i j

         fill4 : ∀ j → I → doubleCompPath-filler A≡B B≡C C≡D (~ i) j → C≡D i
         fill4 j =
            hfill
             (λ l → λ { (i = i0) → transp (λ i' → B≡C (j ∨ i')) (j ∧ ~ l) ∘ prim^unglueU-Sq0 i1 j                                                 
                      ; (i = i1) → transport C≡D ∘ transport-fillerExt⁻ B≡C j ∘ (transp (λ _ → B≡C j) l)})
             (inS (transport-fillerExt C≡D i ∘ transport-fillerExt⁻ B≡C j ∘ prim^unglueU-Sq0 (~ i) j))

         fill3 : ∀ j l  → _
         fill3 j = fill (λ l → doubleCompPath-filler A≡B B≡C C≡D (~ i ∨  l) j → C≡D (l ∨ i))
                       (λ l → λ { (i = i0) → transp (λ i' → C≡D (i' ∧ l)) (~ l) ∘
                                               hfill (λ k → λ { (j = i0) → transport B≡C ∘ transport A≡B
                                                              ; (j = i1) → transp (λ _ → C) k ∘ transport λ i' → C≡D (~ i') })
                                                                   (inS (transport (λ i' → B≡C (j ∨ i')) ∘ prim^unglueU-Sq0 i1 j)) l
                                ; (i = i1) → fill2 l j })
                                   (inS (fill4 j i1))

         sqJ0 : I → A → D
         sqJ0 k =
           comp (λ l → A≡B (~ l ∧ (i ∧ ~ k)) → C≡D ((k ∨ i) ∨ l))
             (λ l →
               λ { (i = i0) → transp (λ i' → C≡D ((i' ∧ l) ∨ k)) (k ∨ (~ l))
                             ∘ transp (λ i' → C≡D (i' ∧ k)) (~ k) ∘ transport B≡C ∘ transport A≡B
                 ; (i = i1) → transport C≡D ∘ transport B≡C ∘ transport-fillerExt⁻ A≡B (~ l ∧ ~ k)
                 ; (k = i0) → fill3 i0 l
                 ; (k = i1) → transport C≡D ∘ transport B≡C ∘ transport A≡B
                  })
                  (hcomp
                      (λ l →
                       λ { (i = i0) → transport-fillerExt C≡D k ∘ transport B≡C ∘  transport A≡B 
                         ; (i = i1) → transport C≡D ∘ transport B≡C ∘ transp (λ i' → A≡B (i' ∨ ~ k)) (l ∧ ~ k)
                         ; (k = i0) → fill4 i0 l
                         ; (k = i1) → transport C≡D ∘ transport B≡C ∘ transport A≡B
                          }) ( transp (λ i' → C≡D ((k ∨ i) ∧ i')) (~ (i ∨ k))
                             ∘ transport B≡C ∘ transport (λ i' → A≡B (i' ∨ (i ∧ ~ k)))))

         sqJ1 : I → D → D
         sqJ1 k =
           comp (λ l → C≡D (l ∨ (~ i ∨ k)) → C≡D (l ∨ (k ∨ i)))
             (λ l →  
               λ { (i = i0) → transp (λ i' → C≡D ((i' ∧ l) ∨ k)) (k ∨ (~ l)) ∘ transp (λ _ → C≡D k) l ∘ transport⁻-fillerExt⁻ C≡D k                                
                 ; (i = i1) → transport-fillerExt⁻ C≡D (l ∨ k)
                 ; (k = i0) → fill3 i1 l
                 ; (k = i1) → transp (λ _ → D) (i ∨ l) 
                  }) (hcomp
                      (λ l →
                       λ { (i = i0) → transp (λ _ → C≡D k) (~ l) ∘ transport⁻-fillerExt⁻ C≡D k 
                         ; (i = i1) → transport-fillerExt⁻ C≡D k ∘ transp (λ _ → C≡D k) l
                         ; (k = i0) → fill4 i1 l
                         ; (k = i1) → transp (λ _ → C≡D k) (~ l ∨ i) ∘  transp (λ _ → C≡D k) (l ∨ (~ i))
                          }) (transp (λ i' → C≡D ((i' ∧ i) ∨ k)) (k ∨ ~ i)
                            ∘ transp (λ i' → C≡D ((~ i' ∧ ~ i) ∨ k)) (k ∧ ~ i)))



-- transport-filler-ua'' : ∀ {ℓ} (A : Type ℓ) →
--                      ∀ x →
--                         Square
--                (λ i → ua-unglue (_ , isEquivTransport (refl {x = A})) i
--                  (transport-filler (ua ((_ , isEquivTransport (refl {x = A})))) x i))
--                (sym (transportRefl _))
--                refl
--                refl
                                
-- transport-filler-ua'' A x i j  =
--           {!!}


-- transport-filler-ua' : ∀ {ℓ} (A B : Type ℓ) (p : A ≡ B) →
--                      ∀ x →
--                         Square
--                (λ i → ua-unglue (_ , isEquivTransport p) i
--                  (transport-filler (ua ((_ , isEquivTransport p))) x i))
--                (sym (transportRefl _))
--                refl
--                refl
                                
-- transport-filler-ua' A B e x =
--           {!!}

