{-# OPTIONS --lossy-unification #-}

module Cubical.HITs.CauchyReals.Lipschitz where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv hiding (_■)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv

import Cubical.Functions.Logic as L

open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Bool.Base using () renaming (Bool to 𝟚 ; true to 1̂ ; false to 0̂)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
open import Cubical.Data.Nat.Order.Recursive as OR
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit
open import Cubical.Data.Int as ℤ
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sigma hiding (Path)
open import Cubical.Data.List as L
open import Cubical.Data.List using () renaming (List to ⟦_⟧)
open import Cubical.Foundations.Interpolate
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _//_)

open import Cubical.Data.Rationals using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)

import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Data.NatPlusOne
open import Cubical.Foundations.Path
open import Cubical.Foundations.CartesianKanOps


open import Cubical.Data.Rationals.Order.Properties as ℚ

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness

sΣℚ< : ∀ {u v ε ε'} → fst ε ≡ ε' → (u ∼[ ε ] v) →
         Σ (0< ε') (λ z → u ∼[ ε' , z ] v)
sΣℚ< {u} {v} {ε} p x =
   subst (λ ε' → Σ (0< ε') (λ z → u ∼[ ε' , z ] v)) p (snd ε , x)

sΣℚ<' : ∀ {u v ε ε'} → fst ε ≡ ε' → (u ∼'[ ε ] v) →
         Σ (0< ε') (λ z → u ∼'[ ε' , z ] v)
sΣℚ<' {u} {v} {ε} p x =
   subst (λ ε' → Σ (0< ε') (λ z → u ∼'[ ε' , z ] v)) p (snd ε , x)


-- 11.3.36
𝕣-lim : ∀ r y ε δ p →
          r ∼[ ε ] ( y δ )
        → r ∼[ ε ℚ₊+ δ  ] (lim y p )
𝕣-lim = Elimℝ-Prop.go w

 where
 w : Elimℝ-Prop _
 w .Elimℝ-Prop.ratA x y ε δ p x₁ =
   rat-lim x y (ε ℚ₊+ δ) δ p (subst 0<_ ((lem--034 {fst ε} {fst δ})) (snd ε))
    (subst∼ (lem--034 {fst ε} {fst δ}) x₁)
 w .Elimℝ-Prop.limA x p R y ε δ p₁ = PT.rec (isProp∼ _ _ _)
     (uncurry λ θ → PT.rec (isProp∼ _ _ _) (uncurry $ λ vv →
        uncurry (lim-lim _ _ _ (/4₊ θ) δ _ _) ∘
                  (sΣℚ< ((λ i → (fst (/4₊+/4₊≡/2₊ θ (~ i)) ℚ.+ fst (/4₊ θ))
                             ℚ.+ (fst ε ℚ.-
                                (sym (ε/2+ε/2≡ε (fst θ))
                                      ∙ cong₂ ℚ._+_ (cong fst $
                                          sym (/4₊+/4₊≡/2₊ θ))
                                         (cong fst $ sym (/4₊+/4₊≡/2₊ θ))) i ))
                         ∙ lem--044 {fst (/4₊ θ)} {fst ε} {fst δ}) ∘
                    (triangle∼ (R (/4₊ θ) x (/2₊ θ)
                      (/4₊ θ) p (refl∼ _ _)))))) ∘ fst (rounded∼ _ _ _)


 w .Elimℝ-Prop.isPropA _ = isPropΠ5 λ _ _ _ _ _ → isProp∼ _ _ _


-- 11.3.37
𝕣-lim-self : ∀ x y δ ε → x δ ∼[ δ ℚ₊+ ε ] lim x y
𝕣-lim-self x y δ ε =
 subst∼ (sym (ℚ.+Assoc _ _ _) ∙ cong (fst δ ℚ.+_) (ε/2+ε/2≡ε (fst ε))) $ 𝕣-lim (x δ) x (δ ℚ₊+ /2₊ ε) ((/2₊ ε)) y
  (y δ _)

-- 11.3.36
𝕣-lim' : ∀ r y ε δ p v →
          r ∼[ fst ε ℚ.- fst δ , v ] ( y δ )
        → r ∼[ ε ] (lim y p )
𝕣-lim' r y ε δ p v₁ x =
   subst∼ (sym (lem--035 {fst ε} {fst δ}))
     $ 𝕣-lim r y (fst ε ℚ.- fst δ , v₁) δ p x


-- HoTT Lemma (11.3.10)
lim-surj : ∀ r → ∃[ x ∈ _ ] (r ≡ (uncurry lim x) )
lim-surj = PT.map (map-snd (eqℝ _ _)) ∘ (Elimℝ-Prop.go w)
 where
 w : Elimℝ-Prop _
 w .Elimℝ-Prop.ratA x = ∣ ((λ _ → rat x) , (λ _ _ → refl∼ _ _)) ,
   (λ ε → rat-lim x (λ v → rat x) ε
    (/2₊ ε) (λ v v₁ → refl∼ (rat x) (v ℚ₊+ v₁))
     (subst 0<_ (lem--034 {fst (/2₊ ε)} {fst (/2₊ ε)} ∙ cong (λ e → e ℚ.- fst (/2₊ ε)) (ε/2+ε/2≡ε (fst ε)) ) (snd (/2₊ ε)))

    (refl∼ (rat x) _)) ∣₁


 w .Elimℝ-Prop.limA x p _ = ∣ (x , p) , refl∼ _ ∣₁
 w .Elimℝ-Prop.isPropA _ = squash₁


-- TODO : (Lemma 11.3.11)


Lipschitz-ℚ→ℚ : ℚ₊ → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚ L f =
  (∀ q r → (ε : ℚ₊) →
    ℚ.abs (q ℚ.- r) ℚ.< (fst ε) → ℚ.abs (f q ℚ.- f r) ℚ.< fst (L ℚ₊· ε  ))


Lipschitz-ℚ→ℚ' : ℚ₊ → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚ' L f =
  ∀ q r →
    ℚ.abs (f q ℚ.- f r) ℚ.≤ fst L ℚ.· ℚ.abs (q ℚ.- r)

Lipschitz-ℚ→ℚ'→Lipschitz-ℚ→ℚ : ∀ L f →
 Lipschitz-ℚ→ℚ' L f → Lipschitz-ℚ→ℚ L f
Lipschitz-ℚ→ℚ'→Lipschitz-ℚ→ℚ L f P q r ε <ε =
  ℚ.isTrans≤< _ _ _ (P q r)
    (ℚ.<-o· (ℚ.abs (q ℚ.- r)) (fst ε) _ (ℚ.0<ℚ₊ L) <ε)

Lipschitz-ℚ→ℚ-restr : ℚ₊ → ℚ₊ → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚ-restr Δ L f =
  (∀ q r → ℚ.abs q ℚ.< fst Δ → ℚ.abs r ℚ.< fst Δ → (ε : ℚ₊) →
    ℚ.abs (q ℚ.- r) ℚ.< (fst ε) → ℚ.abs (f q ℚ.- f r) ℚ.< fst (L ℚ₊· ε  ))

Lipschitz-ℚ→ℚ-restr' : ℚ₊ → ℚ₊ → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚ-restr' Δ L f =
  (∀ q r → fst Δ ℚ.< ℚ.abs q → fst Δ  ℚ.< ℚ.abs r → (ε : ℚ₊) →
    ℚ.abs (q ℚ.- r) ℚ.< (fst ε) → ℚ.abs (f q ℚ.- f r) ℚ.< fst (L ℚ₊· ε  ))


Lipschitz-ℚ→ℚ-extend : ∀ Δ L f (δ : ℚ₊) → fst δ ℚ.< fst Δ
 → Lipschitz-ℚ→ℚ-restr Δ L f
 → Lipschitz-ℚ→ℚ L (f ∘ ℚ.clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ))
Lipschitz-ℚ→ℚ-extend Δ L f δ δ<Δ x q r ε v =
 let z : ∀ u → ℚ.abs (ℚ.clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) u)
                  ℚ.< fst Δ
     z u = ℚ.absFrom<×< (fst Δ)
              (ℚ.clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) u)
               (ℚ.isTrans<≤ (ℚ.- (fst Δ)) (ℚ.- (fst Δ ℚ.- fst δ)) _
                 (subst2 (ℚ._<_)
                     (ℚ.+IdR _) (ℚ.+Comm _ _
                      ∙ (sym $ ℚ.-[x-y]≡y-x (fst Δ) (fst δ)))
                     ((ℚ.<-o+ 0 (fst δ) (ℚ.- (fst Δ)) (ℚ.0<ℚ₊ δ))))
                 ((≤clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) u
                    (( ℚ.pos[-x≤x] (ℚ.<→ℚ₊ (fst δ) (fst Δ) δ<Δ))))) )
               (ℚ.isTrans≤< _ _ _ (clamp≤ _ _ _)
                (ℚ.<-ℚ₊' (fst Δ) (fst Δ) δ (ℚ.isRefl≤ (fst Δ)) ))

 in x (ℚ.clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) q)
            (ℚ.clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) r)
            (z q) (z r) ε
             (ℚ.isTrans≤< _ _ _
               (clampDist (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) r q)
               v)


-- HoTT Definition (11.3.14)
Lipschitz-ℚ→ℝ : ℚ₊ → (ℚ → ℝ) → Type
Lipschitz-ℚ→ℝ L f =
  (∀ q r → (ε : ℚ₊) →
    (ℚ.- (fst ε)) ℚ.< (q ℚ.- r)
     → q ℚ.- r ℚ.< (fst ε) → f q ∼[ L ℚ₊· ε  ] f r)

Lipschitz-rat∘ : ∀ l f → Lipschitz-ℚ→ℚ l f → Lipschitz-ℚ→ℝ l (rat ∘ f)
Lipschitz-rat∘ l f x =
  λ q r ε x₁ x₂ →
    rat-rat-fromAbs _ _ _
       $ x q r ε (ℚ.absFrom<×< (fst ε) (q ℚ.- r) x₁ x₂)

Lipschitz-ℝ→ℝ : ℚ₊ → (ℝ → ℝ) → Type
Lipschitz-ℝ→ℝ L f =
  (∀ u v → (ε : ℚ₊) →
    u ∼[ ε  ] v → f u ∼[ L ℚ₊· ε  ] f v)

isPropLipschitz-ℝ→ℝ : ∀ q f → isProp (Lipschitz-ℝ→ℝ q f)
isPropLipschitz-ℝ→ℝ q f = isPropΠ4 λ _ _ _ _ → isProp∼ _ _ _

·- : ∀ x y → x ℚ.· (ℚ.- y) ≡ ℚ.- (x ℚ.· y)
·- x y = ℚ.·Assoc x (-1) y
         ∙∙ cong (ℚ._· y) (ℚ.·Comm x (-1))
         ∙∙ sym (ℚ.·Assoc (-1) x y)


-- HoTT Lemma (11.3.15)
fromLipschitz : ∀ L → Σ _ (Lipschitz-ℚ→ℝ L) → Σ _ (Lipschitz-ℝ→ℝ L)
fromLipschitz L (f , fL) = f' ,
  λ u v ε x → Elimℝ.go∼ w x
 where

 rl : _
 rl q y ε δ p v r v' u' z =
  𝕣-lim' (f q) (v' ∘ (invℚ₊ L) ℚ₊·_)
            (L ℚ₊· ε) (L ℚ₊· δ)
          (λ δ₁ ε₁ →
          subst (λ q₁ → v' (invℚ₊ L ℚ₊· δ₁) ∼[ q₁ ] v' (invℚ₊ L ℚ₊· ε₁))
          (ℚ.ℚ₊≡
           ((λ i →
               fst L ℚ.· ℚ.·DistL+ (fst (invℚ₊ L)) (fst δ₁) (fst ε₁) (~ i))
            ∙∙ ℚ.·Assoc (fst L) (fst (invℚ₊ L)) (fst δ₁ ℚ.+ fst ε₁) ∙∙
            ((λ i → x·invℚ₊[x] L i ℚ.· fst (δ₁ ℚ₊+ ε₁)) ∙
             ℚ.·IdL (fst (δ₁ ℚ₊+ ε₁)))))
          (u' (invℚ₊ L ℚ₊· δ₁) (invℚ₊ L ℚ₊· ε₁)))
          (subst {x = fst L ℚ.· (fst ε ℚ.+ (ℚ.- fst δ))}
                 {fst L ℚ.· fst ε ℚ.+ (ℚ.- fst (L ℚ₊· δ))}
                0<_ ( lem--046 )
            (ℚ.·0< (fst L) (fst ε ℚ.- fst δ) (snd L) v) )
              (subst2 (f q ∼[_]_) (ℚ₊≡ lem--046)
                 (cong v' (ℚ₊≡ (sym $ [y·x]/y L (fst δ)))) z)

 w : Elimℝ (λ _ → ℝ) λ u v ε _ → u ∼[ L ℚ₊· ε  ] v
 w .Elimℝ.ratA = f
 w .Elimℝ.limA x p a v = lim (a ∘ (invℚ₊ L) ℚ₊·_)
   λ δ ε →
    let v' = v ((invℚ₊ L ℚ₊· δ)) ((invℚ₊ L ℚ₊· ε))
    in subst (λ q → a (invℚ₊ L ℚ₊· δ) ∼[ q ] a (invℚ₊ L ℚ₊· ε))
        (ℚ₊≡ (cong ((fst L) ℚ.·_)
                (sym (ℚ.·DistL+ (fst (invℚ₊ L)) (fst δ) (fst ε)))
                 ∙∙ ℚ.·Assoc (fst L) (fst (invℚ₊ L))
                      ((fst δ) ℚ.+ (fst ε)) ∙∙
                       (cong (ℚ._· fst (δ ℚ₊+ ε))
                        (x·invℚ₊[x] L) ∙ ℚ.·IdL (fst (δ ℚ₊+ ε)))))

          v'
 w .Elimℝ.eqA p a a' x y =
   eqℝ a a' λ ε →
     subst (λ q → a ∼[ q ] a')
        (ℚ₊≡ $
          ℚ.·Assoc (fst L) (fst (invℚ₊ L)) (fst ε) ∙
            (cong (ℚ._· fst (ε))
                        (x·invℚ₊[x] L) ∙ ℚ.·IdL (fst (ε))))
                        (y (invℚ₊ L ℚ₊· ε))
 w .Elimℝ.rat-rat-B q r ε x x₁ = fL q r ε x x₁
 w .Elimℝ.rat-lim-B = rl
 w .Elimℝ.lim-rat-B x r ε δ p v₁ u v' u' x₁ = sym∼ _ _ _ $
  rl r x ε δ p v₁ (sym∼ _ _ _ u) v' u' (sym∼ _ _ _ x₁)
 w .Elimℝ.lim-lim-B x y ε δ η p p' v₁ r v' u' v'' u'' x₁ =
  let e = lem--047
  in lim-lim _ _ _ (L ℚ₊· δ) (L ℚ₊· η) _ _
       (subst (0<_) e
         $ ℚ.·0< (fst L) (fst ε ℚ.- (fst δ ℚ.+ fst η))
              (snd L) v₁)

        ((cong v' (ℚ₊≡ $ sym ([y·x]/y L (fst δ)))
          subst∼[ ℚ₊≡ e ]
           cong v'' (ℚ₊≡ $ sym ([y·x]/y L (fst η)))) x₁)
 w .Elimℝ.isPropB _ _ _ _ = isProp∼ _ _ _



 f' : ℝ → ℝ
 f' = Elimℝ.go w


∼-monotone< : ∀ {u v ε ε'} → fst ε ℚ.< fst ε' → u ∼[ ε ] v → u ∼[ ε' ] v
∼-monotone< {u} {v} {ε} {ε'} x x₁ =
  subst∼ (lem--05 {fst ε} {fst ε'})
   (triangle∼ x₁ (refl∼ v (<→ℚ₊ (fst ε) (fst ε') x)))

∼-monotone≤ : ∀ {u v ε ε'} → fst ε ℚ.≤ fst ε' → u ∼[ ε ] v → u ∼[ ε' ] v
∼-monotone≤ {u} {v} {ε} {ε'} x x₁ =
   ⊎.rec (flip subst∼ x₁ )
         (flip ∼-monotone< x₁ )
     $ ≤→<⊎≡ (fst ε) (fst ε') x


lipschConstIrrel : ∀ L₁ L₂ (x : ℚ₊ → ℝ) → ∀  p₁ p₂ →
         lim (λ q → x (L₁ ℚ₊· q)) p₁
       ≡ lim (λ q → x (L₂ ℚ₊· q)) p₂
lipschConstIrrel L₁ L₂ =
   ⊎.rec (w L₁ L₂) (λ x x₁ p₁ p₂ →
     sym (w L₂ L₁ x x₁ p₂ p₁)) (getPosRatio L₁ L₂)


 where
 w : ∀ L₁ L₂ → (fst ((invℚ₊ L₁) ℚ₊·  L₂)) ℚ.≤ [ pos 1 / 1+ 0 ] →
      (x : ℚ₊ → ℝ)
      (p₁ : (δ ε : ℚ₊) → x (L₁ ℚ₊· δ) ∼[ δ ℚ₊+ ε ] x (L₁ ℚ₊· ε))
      (p₂ : (δ ε : ℚ₊) → x (L₂ ℚ₊· δ) ∼[ δ ℚ₊+ ε ] x (L₂ ℚ₊· ε)) →
      lim (λ q → x (L₁ ℚ₊· q)) p₁ ≡ lim (λ q → x (L₂ ℚ₊· q)) p₂
 w L₁ L₂ L₂/L₁≤1 x p₁ p₂ = eqℝ _ _ $ λ ε →

    (
      (uncurry (lim-lim _ _ ε (/4₊ ε) (/4₊ ε) p₁ p₂)
         (sΣℚ< ((((cong (fst (/4₊ ε) ℚ.+_) (ℚ.·IdL _)) ∙
                  cong fst (/4₊+/4₊≡/2₊ ε)  ) ∙ lem--034 ∙
               cong₂ (ℚ._-_)
                  (ε/2+ε/2≡ε (fst ε)) (cong fst $ sym (/4₊+/4₊≡/2₊ ε) ))) (( refl subst∼[ refl ] cong x
               (ℚ₊≡ (ℚ.·Assoc _ _ _ ∙
                cong (ℚ._· (fst (/4₊ ε)))
                  (ℚ.·Assoc _ _ _ ∙
                   cong (ℚ._· (fst L₂))
                     (x·invℚ₊[x] L₁) ∙ ℚ.·IdL (fst (L₂))) ))) $
            (∼-monotone≤ {ε' = (/4₊ ε) ℚ₊+ (1 ℚ₊· (/4₊ ε))}
               (ℚ.≤-o+ _ (1 ℚ.· (fst (/4₊ ε))) (fst (/4₊ ε))
                 (ℚ.≤-·o (fst (invℚ₊ L₁ ℚ₊· L₂)) 1 (fst (/4₊ ε))
                  (ℚ.0≤ℚ₊ (/4₊ ε)) L₂/L₁≤1)
                   ) $ p₁ (/4₊ ε) ((invℚ₊ L₁ ℚ₊· L₂) ℚ₊· /4₊ ε))))
                   ) )


NonExpandingℚₚ : (ℚ → ℚ) → hProp ℓ-zero
fst (NonExpandingℚₚ f) = ∀ q r → ℚ.abs (f q ℚ.- f r) ℚ.≤ ℚ.abs (q ℚ.- r)
snd (NonExpandingℚₚ f) = isPropΠ2 λ _ _ → ℚ.isProp≤ _ _

NonExpandingₚ : (ℝ → ℝ) → hProp ℓ-zero
fst (NonExpandingₚ f) = ∀ u v ε →  u ∼[ ε ] v → f u ∼[ ε ] f v
snd (NonExpandingₚ f) = isPropΠ4 λ _ _ _ _ → isProp∼ _ _ _

NonExpandingₚ∘ : ∀ f g → ⟨ NonExpandingₚ f ⟩ → ⟨ NonExpandingₚ g ⟩ →
                    ⟨ NonExpandingₚ (f ∘ g) ⟩
NonExpandingₚ∘ _ _ x y _ _ _ = x _ _ _ ∘ (y _ _ _)


congLim : ∀ x y x' y' → (∀ q → x q ≡ x' q) → lim x y ≡ lim x' y'
congLim x y x' y' p =
  congS (uncurry lim)
          (Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isProp∼ _ _ _)
           (funExt p))


congLim' : ∀ x y x' → (p : ∀ q → x q ≡ x' q) →
 lim x y ≡ lim x' (subst (λ x' → (δ ε : ℚ₊) → x' δ ∼[ δ ℚ₊+ ε ] x' ε)
                      (funExt p) y)
congLim' x y x' p =
   congLim x y x' _ p

-- HoTT Lemma (11.3.40)
record NonExpanding₂ (g : ℚ → ℚ → ℚ ) : Type where
 no-eta-equality
 field

  cL : ∀ q r s →
       ℚ.abs (g q s ℚ.- g r s) ℚ.≤ ℚ.abs (q ℚ.- r)

  cR : ∀ q r s →
      (ℚ.abs (g q r ℚ.- g q s) ℚ.≤ ℚ.abs (r ℚ.- s))




 zz : (q : ℚ) → Σ (ℝ → ℝ) (Lipschitz-ℝ→ℝ (1 , tt))
 zz q = fromLipschitz (1 , tt) (rat ∘ g q ,
    λ q₁ r₁ ε x₀ x →
      let zz : ℚ.abs (g q q₁ ℚ.- g q r₁) ℚ.≤ ℚ.abs (q₁ ℚ.- r₁)
          zz = cR q q₁ r₁
      in rat-rat-fromAbs _ _ _
           (ℚ.isTrans≤<
             (ℚ.abs (g q q₁ ℚ.- g q r₁)) (ℚ.abs (q₁ ℚ.- r₁))
             _ zz
               (subst (ℚ.abs (q₁ ℚ.- r₁) ℚ.<_) (sym (ℚ.·IdL (fst ε)))
                 (ℚ.absFrom<×< (fst ε) (q₁ ℚ.- r₁) x₀ x)))

      )


 w : Elimℝ
       _ λ h h' ε v → ∀ u → (fst h u) ∼[ ε ] fst h' u
 w .Elimℝ.ratA x .fst = fst (zz x)

 w .Elimℝ.ratA x .snd = λ ε u v →
    subst (fst (zz x) u ∼[_] fst (zz x) v)
     (ℚ₊≡ $ ℚ.·IdL (fst ε)) ∘S snd (zz x) u v ε
 w .Elimℝ.limA x p a x₁ .fst u =
   lim (λ q → fst (a q) u) λ δ ε → x₁ δ ε u
 w .Elimℝ.limA x p a x₁ .snd ε u v =
   PT.rec (isProp∼ _ _ _)
     (uncurry λ q → PT.rec (isProp∼ _ _ _)
       λ (xx , xx') →
        let q/2 = /2₊ q
            z = snd (a q/2) _ _ _ xx'
        in lim-lim _ _ _ q/2 q/2 _ _
             (subst 0<_ ((cong (λ d → fst ε ℚ.- d) (sym $ ε/2+ε/2≡ε (fst q)) ))
                xx)
             (subst∼ (cong (λ d → fst ε ℚ.- d) (sym $ ε/2+ε/2≡ε (fst q)) ) z))
     ∘S fst (rounded∼ _ _ _)

 w .Elimℝ.eqA p a a' x x₁ = Σ≡Prop
   (λ _ → isPropΠ4 λ _ _ _ _ → isProp∼ _ _ _)
   (funExt λ rr →
     eqℝ _ _ λ ε → x₁ ε rr)
 w .Elimℝ.rat-rat-B q r ε x x₁ u =
    Elimℝ-Prop.go rr u ε x x₁

  where
  rr :  Elimℝ-Prop λ u → (ε : ℚ₊) (x : (ℚ.- fst ε) ℚ.< (q ℚ.- r))
         (x₁ : (q ℚ.- r) ℚ.< fst ε) →
               fst (zz q) u ∼[ ε ] fst (zz r) u
  rr .Elimℝ-Prop.ratA qq ε x₁ x₂ =
    rat-rat-fromAbs _ _ _
      (ℚ.isTrans≤<
        (ℚ.abs (g q qq ℚ.- g r qq))
        (ℚ.abs (q ℚ.- r))
        _
        (cL q r qq) (ℚ.absFrom<×< (fst ε) (q ℚ.- r) x₁ x₂))

  rr .Elimℝ-Prop.limA x p x₁ ε x₂ x₃ =
    let ((θ , θ<) , (x₂' , x₃'))  = getθ ε ((q ℚ.- r)) (x₂ , x₃)
        θ/2 = /2₊ (θ , θ<)
        zzz : fst (zz q) (x θ/2) ∼[ (fst ε ℚ.- θ) , x₂' ]
               fst (zz r) (x θ/2)
        zzz = x₁ θ/2  ((fst ε ℚ.- θ) , x₂') (fst x₃') (snd x₃')
    in lim-lim _ _ _ θ/2 θ/2
                _ _ (subst 0<_ (cong (λ θ → fst ε ℚ.- θ)
                              (sym (ε/2+ε/2≡ε θ))) x₂') (
                 (subst2 (λ xx yy → fst (zz q) (x xx) ∼[ yy ]
                     fst (zz r) (x xx))
                       (ℚ₊≡ $ sym (ℚ.·IdL (fst θ/2)))
                       (ℚ₊≡ (cong (λ θ → fst ε ℚ.- θ)
                              (sym (ε/2+ε/2≡ε θ)))) zzz))
  rr .Elimℝ-Prop.isPropA _ = isPropΠ3 λ _ _ _ → isProp∼ _ _ _

 w .Elimℝ.rat-lim-B _ _ ε δ _ _ _ _ _ x _ =
       subst∼ (sym $ lem--035 {fst ε} {fst δ}) $ 𝕣-lim _ _ _ _ _ (x _)
 w .Elimℝ.lim-rat-B _ _ ε δ _ _ _ _ _ x₁ _ =
   subst∼ (sym $ lem--035 {fst ε} {fst δ})
    $ sym∼ _ _ _ (𝕣-lim _ _ _ _ _ (sym∼ _ _ _ $ x₁ _))
 w .Elimℝ.lim-lim-B _ _ _ _ _ _ _ _ _ _ _ _ _ x₁ _ =
   lim-lim _ _ _ _ _ _ _ _ (x₁ _)
 w .Elimℝ.isPropB a a' ε _ = isPropΠ λ _ → isProp∼ _ _ _

 preF : ℝ → Σ (ℝ → ℝ) λ h → ∀ ε u v → u ∼[ ε ] v → h u ∼[ ε ] h v
 preF = Elimℝ.go w


 go : ℝ → ℝ → ℝ
 go x = fst (preF x)

 go∼R : ∀ x u v ε → u ∼[ ε ] v → go x u ∼[ ε ] go x v
 go∼R x u v ε = snd (preF x) ε u v

 go∼L : ∀ x u v ε → u ∼[ ε ] v → go u x ∼[ ε ] go v x
 go∼L x u v ε y = Elimℝ.go∼ w {u} {v} {ε} y x


 go∼₂ : ∀ δ η {u v u' v'} → u ∼[ δ  ] v → u' ∼[ η ] v'
             → go u u' ∼[ δ ℚ₊+ η ] go v v'
 go∼₂ δ η {u} {v} {u'} {v'} x x' =
   (triangle∼ (go∼L u' u v _ x) (go∼R v u' v' _ x'))


 β-rat-lim : ∀ r x y y' → go (rat r) (lim x y) ≡
                         lim (λ q → go (rat r) (x q))
                          y'
 β-rat-lim r x y y' = congLim _ _ _ _
   λ q → cong (go (rat r) ∘ x)
     (ℚ₊≡ (ℚ.·IdL (fst q)))


 β-rat-lim' : ∀ r x y → Σ _
            λ y' → (go (rat r) (lim x y) ≡
                         lim (λ q → go (rat r) (x q)) y')
 β-rat-lim' r x y = _ , congLim' _ _ _
   λ q → cong (go (rat r) ∘ x)
     (ℚ₊≡ (ℚ.·IdL (fst q)))


 β-lim-lim/2 : ∀ x y x' y' → Σ _ (λ yy' → go (lim x y) (lim x' y') ≡
                         lim (λ q → go (x (/2₊ q)) (x' (/2₊ q)))
                          yy')
 β-lim-lim/2 x y x' y' =
   let
       zz : lim (λ q → fst (Elimℝ.go w (x q)) (lim x' y'))
              (λ δ ε → Elimℝ.go∼ w (y δ ε) (lim x' y')) ≡
            lim (λ q → fst (Elimℝ.go w (x (/2₊ q))) (x' (/2₊ q)))
                   λ δ ε →
                     subst∼ (lem--045 ∙ cong₂ ℚ._+_ (ε/2+ε/2≡ε (fst δ))
                              (ε/2+ε/2≡ε (fst ε))) $
                       triangle∼
                        (go∼R (x (/2₊ δ))  (x' (/2₊ δ)) (x' (/2₊ ε))
                         (/2₊ δ ℚ₊+ /2₊ ε)
                          (y' _ _))
                         (go∼L (x' (/2₊ ε))
                          (x (/2₊ δ)) (x (/2₊ ε)) _ (y _ _))
       zz = eqℝ _ _ (λ ε →
               let ε/4 = /4₊ ε
                   v = subst {x = fst ε ℚ.· ℚ.[ 3 / 8 ]} (0 ℚ.<_)
                       (distℚ! (fst ε)
                        ·[ ge[ ℚ.[ 3 / 8 ] ] ≡
                          (ge1 +ge
                        (neg-ge
                        ((ge[ ℚ.[ pos 1 / 1+ 3 ] ]
                          ·ge ge[ ℚ.[ pos 1 / 1+ 1 ] ])
                           +ge ge[ ℚ.[ pos 1 / 1+ 3 ] ])))
                           +ge
                        (neg-ge ((ge[ ℚ.[ pos 1 / 4 ] ]
                          ·ge ge[ ℚ.[ pos 1 / 2 ] ])
                               +ge
                               (ge[ ℚ.[ pos 1 / 4 ] ]
                          ·ge ge[ ℚ.[ pos 1 / 2 ] ]))) ])
                        (ℚ.0<ℚ₊ (ε ℚ₊· (ℚ.[ 3 / 8 ] , _)))
               in (lim-lim _ (λ q' → go (x (/2₊ q')) (x' (/2₊ q'))) ε
                        (/2₊ ε/4) ε/4 _ _) (subst
                         {y = fst ε ℚ.- (fst (/2₊ ε/4) ℚ.+ (fst ε/4))} (ℚ.0<_)
                                   distℚ! (fst ε) ·[ ge[ ℚ.[ pos 5 / 8 ] ]
                                     ≡ (ge1 +ge
                        (neg-ge
                        ((ge[ ℚ.[ pos 1 / 4 ] ]
                          ·ge ge[ ℚ.[ pos 1 / 2 ] ])
                           +ge ge[ ℚ.[ pos 1 / 4 ] ]))) ]
                                    ((snd (ε ℚ₊· (ℚ.[ 5 / 8 ] , _)))))
                        ((go∼R ( x (/2₊ ε/4)) (lim x' y')
                          (x' (/2₊ ε/4)) _
                          ((∼-monotone< {ε = /2₊ ε/4 ℚ₊+ /2₊ ε/4}
                               {(fst ε ℚ.- ((((fst ε) ℚ.· [ 1 / 4 ])
                                  ℚ.· ℚ.[ 1 / 2 ]) ℚ.+ fst ε/4))
                                , _} (((-<⁻¹ _ _ v)))
                                   $ sym∼ _ _ _ (𝕣-lim-self x' y'
                             (/2₊ ε/4) (/2₊ ε/4)))))))
   in _ , zz


NonExpanding₂-flip : ∀ g → NonExpanding₂ g → NonExpanding₂ (flip g)
NonExpanding₂-flip g ne .NonExpanding₂.cL q r s =
   NonExpanding₂.cR ne s q r
NonExpanding₂-flip g ne .NonExpanding₂.cR q r s =
   NonExpanding₂.cL ne r s q



isPropNonExpanding₂ : ∀ g → isProp (NonExpanding₂ g)
isPropNonExpanding₂ g x y i .NonExpanding₂.cL =
  isPropΠ3 (λ q r s →
   ℚ.isProp≤ (ℚ.abs (g q s ℚ.- g r s)) (ℚ.abs (q ℚ.- r)))
     (λ q r s → x .NonExpanding₂.cL q r s)
    (λ q r s → y .NonExpanding₂.cL q r s) i
isPropNonExpanding₂ g x y i .NonExpanding₂.cR =
   isPropΠ3 (λ q r s →
   ℚ.isProp≤ (ℚ.abs (g q r ℚ.- g q s)) (ℚ.abs (r ℚ.- s)))
     (λ q r s → x .NonExpanding₂.cR q r s)
    (λ q r s → y .NonExpanding₂.cR q r s) i

nonExpanding₂Ext : (g g' : _)
   → (ne : NonExpanding₂ g) (ne' : NonExpanding₂ g')
   → (∀ x y → g x y ≡ g' x y)
   → ∀ x y → NonExpanding₂.go ne x y  ≡ NonExpanding₂.go ne' x y
nonExpanding₂Ext g g' ne ne' p x y =
  congS (λ x₁ → NonExpanding₂.go (snd x₁) x y)
   (Σ≡Prop isPropNonExpanding₂ {_ , ne} {_ , ne'}
    λ i x₁ x₂ → p x₁ x₂ i)


NonExpanding₂-flip-go : ∀ g → (ne : NonExpanding₂ g)
                              (flip-ne : NonExpanding₂ (flip g)) → ∀ x y →
     (NonExpanding₂.go {g = flip g} flip-ne x y)
   ≡ (NonExpanding₂.go {g = g} ne y x)
NonExpanding₂-flip-go g ne flip-ne = Elimℝ-Prop2.go w
 where
 w : Elimℝ-Prop2
          λ z z₁ → NonExpanding₂.go flip-ne z z₁ ≡ NonExpanding₂.go ne z₁ z

 w .Elimℝ-Prop2.rat-ratA _ _ = refl
 w .Elimℝ-Prop2.rat-limA r x y x₁ =
   congLim _ _ _ _
     λ q → congS (NonExpanding₂.go flip-ne (rat r) ∘S x)
       ((ℚ₊≡ $ (ℚ.·IdL (fst q)) )) ∙ x₁ q

 w .Elimℝ-Prop2.lim-ratA x y r x₁ =
    congLim _ _ _ _
     λ q → x₁ q ∙ congS (NonExpanding₂.go ne (rat r) ∘S x)
      (ℚ₊≡ $ sym (ℚ.·IdL (fst q)) )

 w .Elimℝ-Prop2.lim-limA x y x' y' x₁ =
      snd (NonExpanding₂.β-lim-lim/2 flip-ne
        x y x' y') ∙∙
         cong (uncurry lim)
          (Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isProp∼ _ _ _)
           (funExt λ q → x₁ (/2₊ q) (/2₊ q)))
         ∙∙
       sym (snd (NonExpanding₂.β-lim-lim/2 ne
        x' y' x y))
 w .Elimℝ-Prop2.isPropA _ _ = isSetℝ _ _

module NonExpanding₂-Lemmas
        (g : ℚ → ℚ → ℚ)
        (ne : NonExpanding₂ g) where

 module NE = NonExpanding₂ ne

 module _ (gComm : ∀ x y → NE.go x y ≡ NE.go y x)
          (gAssoc : ∀ p q r → g p (g q r) ≡ g (g p q) r)  where
  pp : ∀ ε → fst (/2₊ ε) ≡ (fst ε ℚ.- (fst (/4₊ ε) ℚ.+ fst (/4₊ ε)))
  pp ε = (distℚ! (fst ε) ·[ ge[ ℚ.[ 1 / 2 ] ]
            ≡ ge1 +ge (neg-ge (ge[ ℚ.[ 1 / 4 ] ]
               +ge ge[ ℚ.[ 1 / 4 ] ]))  ])

  gAssoc∼ : ∀ x y z → ∀ ε → NE.go x (NE.go y z) ∼[ ε ] NE.go (NE.go x y) z
  gAssoc∼ = Elimℝ-Prop.go w
    where
    w : Elimℝ-Prop _
    w .Elimℝ-Prop.ratA q y z ε =
       subst2 (_∼[ ε ]_)
         (gComm (NE.go y z) (rat q))
         (λ i → NE.go (gComm y (rat q) i) z)
         (hh y z ε)
     where
     hh : (y z : ℝ) (ε : ℚ₊) →
            NE.go (NE.go y z) (rat q) ∼[ ε ] NE.go (NE.go y (rat q)) z
     hh = Elimℝ-Prop.go w'
       where
       w' : Elimℝ-Prop _
       w' .Elimℝ-Prop.ratA p = Elimℝ-Prop.go w''
         where
         w'' : Elimℝ-Prop _
         w'' .Elimℝ-Prop.ratA r ε = ≡→∼ (
          gComm _ _ ∙∙ cong rat (gAssoc q p r)
           ∙∙ λ i → NE.go (gComm (rat q) (rat p) i) (rat r))
         w'' .Elimℝ-Prop.limA x x' R ε =
           subst2 (_∼[ ε ]_)
             (λ i → NE.go (gComm (lim x x')  (rat p)  i) (rat q))
             (sym (gComm (NE.go (rat p) (rat q)) (lim x x')))
            (hhh ε)
          where
          hhh : ∀ ε → NE.go (NE.go (lim x x') (rat p)) (rat q) ∼[ ε ]
                 NE.go (lim x x') (NE.go (rat p) (rat q))
          hhh ε =
           let zzz = R (/4₊ ε) (/2₊ ε)
           in uncurry (lim-lim _ _ ε (/4₊ ε)
               (/4₊ ε) _ _)
                (sΣℚ< (pp ε)
                  ( (λ i → NE.go (gComm (rat p) (x (/4₊ ε)) i) (rat q))
                      subst∼[ refl ] gComm (NE.go (rat p) (rat q))
                                          (x (/4₊ ε))
                     $ zzz  ))

         w'' .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → isProp∼ _ _ _
       w' .Elimℝ-Prop.limA x x' R z ε =
        uncurry (lim-lim _ _ ε (/4₊ ε)
        (/4₊ ε) _ _)
         (sΣℚ< (pp ε) (R (/4₊ ε) z (/2₊ ε) ))
       w' .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → isProp∼ _ _ _

    w .Elimℝ-Prop.limA x x' R y z ε =
     uncurry (lim-lim _ _ ε (/4₊ ε)
        (/4₊ ε) _ _)
         (sΣℚ< (pp ε)
          (R (/4₊ ε) y z (/2₊ ε)))
    w .Elimℝ-Prop.isPropA _ = isPropΠ3 λ _ _ _ → isProp∼ _ _ _


fromLipshitzNEβ : ∀ f (fl : Lipschitz-ℚ→ℝ 1 f) x y →
  fst (fromLipschitz 1 (f , fl)) (lim x y) ≡
    lim (λ x₁ → Elimℝ.go _ (x x₁))
     _
fromLipshitzNEβ f fl x y = congLim' _ _ _
 λ q → cong (Elimℝ.go _ ∘ x) (ℚ₊≡ $ ℚ.·IdL _)
