{-

A couple of general facts about equivalences:

- if f is an equivalence then (cong f) is an equivalence ([equivCong])
- if f is an equivalence then pre- and postcomposition with f are equivalences ([preCompEquiv], [postCompEquiv])
- if f is an equivalence then (Σ[ g ] section f g) and (Σ[ g ] retract f g) are contractible ([isContr-section], [isContr-retract])

- isHAEquiv is a proposition [isPropIsHAEquiv]
(these are not in 'Equiv.agda' because they need Univalence.agda (which imports Equiv.agda))
-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Equiv.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels

import Agda.Builtin.Cubical.HCompU as HCompU


open import Cubical.Functions.FunExtEquiv

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ

isEquivInvEquiv : isEquiv (λ (e : A ≃ B) → invEquiv e)
isEquivInvEquiv = isoToIsEquiv goal where
  open Iso
  goal : Iso (A ≃ B) (B ≃ A)
  goal .fun = invEquiv
  goal .inv = invEquiv
  goal .rightInv g = equivEq refl
  goal .leftInv f = equivEq refl

invEquivEquiv : (A ≃ B) ≃ (B ≃ A)
invEquivEquiv = _ , isEquivInvEquiv

isEquivCong : {x y : A} (e : A ≃ B) → isEquiv (λ (p : x ≡ y) → cong (equivFun e) p)
isEquivCong e = isoToIsEquiv (congIso (equivToIso e))

congEquiv : {x y : A} (e : A ≃ B) → (x ≡ y) ≃ (equivFun e x ≡ equivFun e y)
congEquiv e = isoToEquiv (congIso (equivToIso e))

equivAdjointEquiv : (e : A ≃ B) → ∀ {a b} → (a ≡ invEq e b) ≃ (equivFun e a ≡ b)
equivAdjointEquiv e = compEquiv (congEquiv e) (compPathrEquiv (secEq e _))

invEq≡→equivFun≡ : (e : A ≃ B) → ∀ {a b} → invEq e b ≡ a → equivFun e a ≡ b
invEq≡→equivFun≡ e = equivFun (equivAdjointEquiv e) ∘ sym

isEquivPreComp : (e : A ≃ B) → isEquiv (λ (φ : B → C) → φ ∘ equivFun e)
isEquivPreComp e = snd (equiv→ (invEquiv e) (idEquiv _))

preCompEquiv : (e : A ≃ B) → (B → C) ≃ (A → C)
preCompEquiv e = (λ φ → φ ∘ fst e) , isEquivPreComp e

isEquivPostComp : (e : A ≃ B) → isEquiv (λ (φ : C → A) → e .fst ∘ φ)
isEquivPostComp e = snd (equivΠCod (λ _ → e))

postCompEquiv : (e : A ≃ B) → (C → A) ≃ (C → B)
postCompEquiv e = _ , isEquivPostComp e

-- see also: equivΠCod for a dependent version of postCompEquiv

hasSection : (A → B) → Type _
hasSection {A = A} {B = B} f = Σ[ g ∈ (B → A) ] section f g

hasRetract : (A → B) → Type _
hasRetract {A = A} {B = B} f = Σ[ g ∈ (B → A) ] retract f g

isEquiv→isContrHasSection : {f : A → B} → isEquiv f → isContr (hasSection f)
fst (isEquiv→isContrHasSection isEq) = invIsEq isEq , secIsEq isEq
snd (isEquiv→isContrHasSection isEq) (f , ε) i = (λ b → fst (p b i)) , (λ b → snd (p b i))
  where p : ∀ b → (invIsEq isEq b , secIsEq isEq b) ≡ (f b , ε b)
        p b = isEq .equiv-proof b .snd (f b , ε b)

isEquiv→hasSection : {f : A → B} → isEquiv f → hasSection f
isEquiv→hasSection = fst ∘ isEquiv→isContrHasSection

isContr-hasSection : (e : A ≃ B) → isContr (hasSection (fst e))
isContr-hasSection e = isEquiv→isContrHasSection (snd e)

isEquiv→isContrHasRetract : {f : A → B} → isEquiv f → isContr (hasRetract f)
fst (isEquiv→isContrHasRetract isEq) = invIsEq isEq , retIsEq isEq
snd (isEquiv→isContrHasRetract {f = f} isEq) (g , η) =
    λ i → (λ b → p b i) , (λ a →  q a i)
  where p : ∀ b → invIsEq isEq b ≡ g b
        p b = sym (η (invIsEq isEq b)) ∙' cong g (secIsEq isEq b)
        -- one square from the definition of invIsEq
        ieSq : ∀ a → Square (cong g (secIsEq isEq (f a)))
                            refl
                            (cong (g ∘ f) (retIsEq isEq a))
                            refl
        ieSq a k j = g (commSqIsEq isEq a k j)
        -- one square from η
        ηSq : ∀ a → Square (η (invIsEq isEq (f a)))
                           (η a)
                           (cong (g ∘ f) (retIsEq isEq a))
                           (retIsEq isEq a)
        ηSq a i j = η (retIsEq isEq a i) j
        -- and one last square from the definition of p
        pSq : ∀ b → Square (η (invIsEq isEq b))
                           refl
                           (cong g (secIsEq isEq b))
                           (p b)
        pSq b i j = compPath'-filler (sym (η (invIsEq isEq b))) (cong g (secIsEq isEq b)) j i
        q : ∀ a → Square (retIsEq isEq a) (η a) (p (f a)) refl
        q a i j = hcomp (λ k → λ { (i = i0) → ηSq a j k
                                 ; (i = i1) → η a (j ∧ k)
                                 ; (j = i0) → pSq (f a) i k
                                 ; (j = i1) → η a k
                                 })
                        (ieSq a j i)

isEquiv→hasRetract : {f : A → B} → isEquiv f → hasRetract f
isEquiv→hasRetract = fst ∘ isEquiv→isContrHasRetract

isContr-hasRetract : (e : A ≃ B) → isContr (hasRetract (fst e))
isContr-hasRetract e = isEquiv→isContrHasRetract (snd e)

isEquiv→retractIsEquiv : {f : A → B} {g : B → A} → isEquiv f → retract f g → isEquiv g
isEquiv→retractIsEquiv {f = f} {g = g} isEquiv-f retract-g = subst isEquiv f⁻¹≡g (snd f⁻¹)
  where f⁻¹ = invEquiv (f , isEquiv-f)

        retract-f⁻¹ : retract f (fst f⁻¹)
        retract-f⁻¹ = snd (isEquiv→hasRetract isEquiv-f)

        f⁻¹≡g : fst f⁻¹ ≡ g
        f⁻¹≡g =
          cong fst
               (isContr→isProp (isEquiv→isContrHasRetract isEquiv-f)
                               (fst f⁻¹ , retract-f⁻¹)
                               (g , retract-g))


isEquiv→sectionIsEquiv : {f : A → B} {g : B → A} → isEquiv f → section f g → isEquiv g
isEquiv→sectionIsEquiv {f = f} {g = g} isEquiv-f section-g = subst isEquiv f⁻¹≡g (snd f⁻¹)
  where f⁻¹ = invEquiv (f , isEquiv-f)

        section-f⁻¹ : section f (fst f⁻¹)
        section-f⁻¹ = snd (isEquiv→hasSection isEquiv-f)

        f⁻¹≡g : fst f⁻¹ ≡ g
        f⁻¹≡g =
          cong fst
               (isContr→isProp (isEquiv→isContrHasSection isEquiv-f)
                               (fst f⁻¹ , section-f⁻¹)
                               (g , section-g))

cong≃ : (F : Type ℓ → Type ℓ') → (A ≃ B) → F A ≃ F B
cong≃ F e = pathToEquiv (cong F (ua e))

cong≃-char : (F : Type ℓ → Type ℓ') {A B : Type ℓ} (e : A ≃ B) → ua (cong≃ F e) ≡ cong F (ua e)
cong≃-char F e = ua-pathToEquiv (cong F (ua e))

cong≃-idEquiv : (F : Type ℓ → Type ℓ') (A : Type ℓ) → cong≃ F (idEquiv A) ≡ idEquiv (F A)
cong≃-idEquiv F A = cong≃ F (idEquiv A) ≡⟨ cong (λ p → pathToEquiv (cong F p)) uaIdEquiv  ⟩
                    pathToEquiv refl    ≡⟨ pathToEquivRefl ⟩
                    idEquiv (F A)       ∎

isPropIsHAEquiv : {f : A → B} → isProp (isHAEquiv f)
isPropIsHAEquiv {f = f} ishaef = goal ishaef where
  equivF : isEquiv f
  equivF = isHAEquiv→isEquiv ishaef

  rCoh1 : (sec : hasSection f) → Type _
  rCoh1 (g , ε) = Σ[ η ∈ retract f g ] ∀ x → cong f (η x) ≡ ε (f x)

  rCoh2 : (sec : hasSection f) → Type _
  rCoh2 (g , ε) = Σ[ η ∈ retract f g ] ∀ x → Square (ε (f x)) refl (cong f (η x)) refl

  rCoh3 : (sec : hasSection f) → Type _
  rCoh3 (g , ε) = ∀ x → Σ[ ηx ∈ g (f x) ≡ x ] Square (ε (f x)) refl (cong f ηx) refl

  rCoh4 : (sec : hasSection f) → Type _
  rCoh4 (g , ε) = ∀ x → Path (fiber f (f x)) (g (f x) , ε (f x)) (x , refl)

  characterization : isHAEquiv f ≃ Σ _ rCoh4
  characterization =
    isHAEquiv f
      -- first convert between Σ and record
      ≃⟨ isoToEquiv (iso (λ e → (e .g , e .rinv) , (e .linv , e .com))
                         (λ e → record { g = e .fst .fst ; rinv = e .fst .snd
                                       ; linv = e .snd .fst ; com = e .snd .snd })
                         (λ _ → refl) λ _ → refl) ⟩
    Σ _ rCoh1
      -- secondly, convert the path into a dependent path for later convenience
      ≃⟨  Σ-cong-equiv-snd (λ s → Σ-cong-equiv-snd
                             λ η → equivΠCod
                               λ x → compEquiv (flipSquareEquiv {a₀₀ = f x}) (invEquiv slideSquareEquiv)) ⟩
    Σ _ rCoh2
      ≃⟨ Σ-cong-equiv-snd (λ s → invEquiv Σ-Π-≃) ⟩
    Σ _ rCoh3
      ≃⟨ Σ-cong-equiv-snd (λ s → equivΠCod λ x → ΣPath≃PathΣ) ⟩
    Σ _ rCoh4
      ■
    where open isHAEquiv

  goal : isProp (isHAEquiv f)
  goal = subst isProp (sym (ua characterization))
    (isPropΣ (isContr→isProp (isEquiv→isContrHasSection equivF))
             λ s → isPropΠ λ x → isProp→isSet (isContr→isProp (equivF .equiv-proof (f x))) _ _)

-- loop spaces connected by a path are equivalent
conjugatePathEquiv : {A : Type ℓ} {a b : A} (p : a ≡ b) → (a ≡ a) ≃ (b ≡ b)
conjugatePathEquiv p = compEquiv (compPathrEquiv p) (compPathlEquiv (sym p))

-- composition on the right induces an equivalence of path types
compr≡Equiv : {A : Type ℓ} {a b c : A} (p q : a ≡ b) (r : b ≡ c) → (p ≡ q) ≃ (p ∙ r ≡ q ∙ r)
compr≡Equiv p q r = congEquiv ((λ s → s ∙ r) , compPathr-isEquiv r)

-- composition on the left induces an equivalence of path types
compl≡Equiv : {A : Type ℓ} {a b c : A} (p : a ≡ b) (q r : b ≡ c) → (q ≡ r) ≃ (p ∙ q ≡ p ∙ r)
compl≡Equiv p q r = congEquiv ((λ s → p ∙ s) , (compPathl-isEquiv p))

isEquivFromIsContr : {A : Type ℓ} {B : Type ℓ'}
                   → (f : A → B) → isContr A → isContr B
                   → isEquiv f
isEquivFromIsContr f isContrA isContrB =
  subst isEquiv (λ i x → isContr→isProp isContrB (fst B≃A x) (f x) i) (snd B≃A)
  where B≃A = isContr→Equiv isContrA isContrB

isEquiv[f∘equivFunA≃B]→isEquiv[f] : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
                 → (f : B → C) (A≃B : A ≃ B)
                 → isEquiv (f ∘ equivFun A≃B)
                 → isEquiv f
isEquiv[f∘equivFunA≃B]→isEquiv[f] f (g , gIsEquiv) f∘gIsEquiv  =
  precomposesToId→Equiv f _ w w'
    where
      w : f ∘ g ∘ equivFun (invEquiv (_ , f∘gIsEquiv)) ≡ idfun _
      w = (cong fst (invEquiv-is-linv (_ , f∘gIsEquiv)))

      w' : isEquiv (g ∘ equivFun (invEquiv (_ , f∘gIsEquiv)))
      w' = (snd (compEquiv (invEquiv (_ , f∘gIsEquiv) ) (_ , gIsEquiv)))

isEquiv[equivFunA≃B∘f]→isEquiv[f] : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
                 → (f : C → A) (A≃B : A ≃ B)
                 → isEquiv (equivFun A≃B ∘ f)
                 → isEquiv f
isEquiv[equivFunA≃B∘f]→isEquiv[f] f (g , gIsEquiv) g∘fIsEquiv  =
  composesToId→Equiv _ f w w'
    where
      w : equivFun (invEquiv (_ , g∘fIsEquiv)) ∘ g ∘ f ≡ idfun _
      w = (cong fst (invEquiv-is-rinv (_ , g∘fIsEquiv)))

      w' : isEquiv (equivFun (invEquiv (_ , g∘fIsEquiv)) ∘ g)
      w' = snd (compEquiv (_ , gIsEquiv) (invEquiv (_ , g∘fIsEquiv)))

isPointedTarget→isEquiv→isEquiv : {A B : Type ℓ} (f : A → B)
    → (B → isEquiv f) → isEquiv f
equiv-proof (isPointedTarget→isEquiv→isEquiv f hf) =
  λ y → equiv-proof (hf y) y

transportΠ : ∀ {ℓ} {ℓ'} {A : Type ℓ}
               (B : A → Type ℓ') → (f : ∀ a → B a) → 
                ∀ a → f (transport refl a) ≡
                   subst B (sym (transportRefl _)) (f a) 
transportΠ {A = A} B f a =   
   sym (fst (equivAdjointEquiv (_ , isEquivTransport (λ i → B (transp (λ _ → A) (~ i) a)))) ((λ i → transp (λ j → B (transp (λ _ → A) (j ∨ ~ i) a)) (~ i)
         (f (transp (λ i₁ → A) (~ i) a))) ∙ sym (transportRefl _) ))



_∙∙P_∙∙P_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
             (p : w ≡ x)
             (q : x ≡ y)
             (r : y ≡ z)
             → w ≡ z

_∙∙P_∙∙P_ {A = A} p q r i =
  comp (λ _ → A) (doubleComp-faces p r i) (q i)


fixComp : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
             (p : w ≡ x)
             (q : x ≡ y)
             (r : y ≡ z)
             → (p ∙∙ q ∙∙ r) ≡ p ∙∙P q ∙∙P r 
fixComp {A = A} p q r j i =
       hcomp
       (doubleComp-faces (λ i₁ → transp (λ _ → A) (~ j ∨ ~ i₁) (p i₁))
        (λ i₁ → transp (λ _ → A) (~ j ∨ i₁) (r i₁)) i)
       (transp (λ _ → A) (~ j) (q i))

module ua-fill-EquivJ {ℓ} (A : Type ℓ) (x : A)  where


 hnt : ∀ (x : A) → refl ≡ cong (transport refl) (sym (transportRefl _)) ∙ transportRefl _
 hnt x = sym (rCancel _) ∙ homotopyNatural transportRefl (sym (transportRefl x))

 hnt' : refl ≡ cong₂ _∘_ (λ i x₁ → transp (λ j → A) (~ i) x₁) (transport-fillerExt⁻ (refl {x = A}))
 hnt' = cong funExt (funExt λ x → cong sym (hnt x) ∙ sym (leftright _ _))
   ∙ sym (cong₂Funct (λ f g → f ∘ g)
       (λ i x₁ → transp (λ j → A) (~ i) x₁) (transport-fillerExt⁻ (refl {x = A}))) 




 tft :  refl ≡ (cong transport (uaIdEquiv {A = A}))
 tft = cong funExt (funExt λ x₁ →
            ((cong (cong (transport refl)) (lUnit _)) ∙
              cong-∙∙ (transport refl) refl refl refl) ∙∙
               congS (refl ∙∙_∙∙ refl) (lUnit _ ∙
               cong (refl ∙_) λ i j → hnt' i (~ j) x₁)
              ∙∙ fixComp refl _ refl
              )

 tff : SquareP (λ j i → uaIdEquiv {A = A} (~ i) j)
          (λ _ → transport refl x)
          (λ i → transp (λ _ → A) i x)
          (λ _ → transport refl x)
          λ j → transport-filler (ua (idEquiv A)) x (~ j)

          
 tff =  ((λ i j → tft i (~ j) x)) ◁
         λ j i → transp
                   (λ k → Glue A {φ = ~ k ∨ j ∨ ~ i ∨ (k ∧ ~ j)}
                       λ _ → A , idEquiv A) (i ∧ j) x 



 tffSq : SquareP (λ j i → ua (idEquiv A) i)
             (λ i → transport-filler (ua (idEquiv A)) x (~ i))
             (λ i → ua-glue ( (idEquiv A)) i (λ _ → x) (inS x))
             (transportRefl _)
             refl
           
 tffSq j i = comp (λ k → uaIdEquiv {A = A} (~ k) i)
   (λ k →
         λ { (i = i0) → transp (λ _ → A) j x
           ; (i = i1) → transp (λ _ → A) (k ∨  j) x
           ; (j = i0) → tff i k
           ; (j = i1) →  (glue (λ {(i = i0) → x 
                                ;(i = i1) → x
                                ;(k = i0) → x })
                                 x)
           }) (transp (λ _ → A) j x)


 tffSq' : SquareP (λ j i → ua (idEquiv A) i)
             (λ i → transport-filler (ua (idEquiv A)) x i)
             (ua-gluePath (idEquiv A) (sym (transportRefl _)))
             refl
             refl
           
 tffSq' j i = let x' = (transp (λ _ → A) (~ i ∧ j) x) in
  comp (λ k → uaIdEquiv {A = A} (~ k) i) (λ k → 
    λ { (i = i0) → transp (λ _ → A) (k ∨ j) x
      ; (i = i1) → tft (~ j) (~ k) x
      ; (j = i0) → transp
                   (λ k' → Glue A {φ = ~ k' ∨ ~ i ∨ ~ k ∨ (k' ∧ i)}
                       λ _ → A , idEquiv A) (k ∧ (~ i)) x
      ; (j = i1) → glue {φ = i ∨ ~ i ∨ ~ k} (λ _ → x') x'
      }) x'




module _ {ℓ} {A B : Type ℓ} (e : A ≃ B) (x : A) where
 -- transport-filler-ua :  Square
 --                            (λ i → ua-unglue e i (transport-filler (ua e) x i))
 --                            (sym (transportRefl (fst e x)))
 --                            refl
 --                            refl
 -- transport-filler-ua = {!!}

 -- transport-filler-ua-fill : Path
 --                                (PathP (λ i → ua e i) x (transport (ua e) x))
 --                              (transport-filler (ua e) x)
 --                              (ua-gluePath e (sym (transportRefl (fst e x))))
 -- transport-filler-ua-fill = {!!}

 -- transport-filler-ua-fill' : Path
 --                                (PathP (λ i → ua e i) x (transport (ua e) x))
 --                              (transport-filler (ua e) x)
 --                              (ua-gluePath e (sym (transportRefl (fst e x))))
 -- transport-filler-ua-fill' = {!!}

 transport-filler-ua' :
    SquareP (λ _ i → ua e i)
                              (transport-filler (ua e) x)
                              (ua-gluePath e refl)
                              refl
                              (transportRefl (fst e x))
 transport-filler-ua' =
    EquivJ (λ A e → ∀ x → SquareP (λ _ i → ua e i)
                              (transport-filler (ua e) x)
                              (ua-gluePath e refl)
                              refl
                              (transportRefl (fst e x)))
     (λ x i j → ua-fill-EquivJ.tffSq B x i (~ j)) e x

 transport-filler-ua-∙ : (transport-filler (ua e) x)
                              ≡ 
                              ((ua-gluePath e refl) ▷ sym (transportRefl _))

 transport-filler-ua-∙ i j =
   hcomp (λ k → λ {(i = i0) → transport-filler-ua' i j
                   ;(j = i0) → transport-filler-ua' i j
                   ;(j = i1) → transp (λ _ → B) (i ∧ ~ k) (fst e x)
                   })
         (transport-filler-ua' i j)

 transport-filler-ua : (transport-filler (ua e) x)
                              ≡
                              ua-gluePath e (sym (transportRefl _)) 
 transport-filler-ua =
   EquivJ (λ A e → ∀ x → (transport-filler (ua e) x)
                              ≡
                              ua-gluePath e (sym (transportRefl _)))
   (ua-fill-EquivJ.tffSq' _) _ _
