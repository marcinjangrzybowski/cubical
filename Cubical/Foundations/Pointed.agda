{-

I picked rather fancy convention for naming, and i am open for diferetn ideashow to name those things
-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Foundations.Pointed where

open import Cubical.Core.Glue

open import Cubical.Foundations.Everything

open import Cubical.Data.Sigma

Type* : ∀ ℓ → Type (ℓ-suc ℓ)
Type* ℓ = Σ[ A ∈ Type ℓ ]  A

pt : ∀ {ℓ} → (A : Type* ℓ) → fst A
pt = snd

_→*_ : ∀ {ℓₛ ℓₜ} → (A : Type* ℓₛ) → (B : Type* ℓₜ) → Type* (ℓ-max ℓₛ ℓₜ)
A →* B = (Σ[ f ∈ (fst A → fst B) ] (f (pt A) ≡ pt B) ) , const (pt B) , refl 

0* :  ∀ {ℓₛ ℓₜ} → {A : Type* ℓₛ} → {B : Type* ℓₜ} → (fst (A →* B))
0* {A = A} {B = B} = pt (A →* B)

id* : ∀ {ℓ} → {A : Type* ℓ} → fst (A →* A)
id* = idfun _ , refl


_∘*_ : ∀ {ℓₛ ℓₘ ℓₜ} → {A : Type* ℓₛ} → {B : Type* ℓₘ} → {C : Type* ℓₜ}
         → fst (B →* C) → fst (A →* B) → fst (A →* C)
g ∘* f = (fst g) ∘ (fst f) , (cong (fst g) (snd f)) ∙ snd g


-- pointed dependent map
PDM : ∀ {ℓₛ ℓ} → (A : Type* ℓₛ) → (B : fst A → Type ℓ) → (b₀ : (B (pt A)))
        → Type (ℓ-max ℓₛ ℓ)
PDM A B b₀ = (Σ[ f ∈ (( a : fst A ) → (B a)) ] (f (pt A) ≡ b₀) )

PDM* : ∀ {ℓₛ ℓ} → (A : Type* ℓₛ) → (B : fst A → Type* ℓ) 
        → Type* (ℓ-max ℓₛ ℓ)
PDM* A B = (PDM A (λ a → fst (B a)) (pt (B (pt A)))) , (λ a → pt (B a)) , refl


-- pointed homotopy
_~*_ : ∀ {ℓₛ ℓ} → {A : Type* ℓₛ} → {B : fst A → Type ℓ} → ∀ {b₀}
         → (f g : PDM A B b₀) → Set (ℓ-max ℓₛ ℓ)
f ~* g = PDM _ (λ a → (fst f) a ≡ (fst g) a) (snd f ∙ (sym (snd g)))



cong-sym : ∀ {ℓ} → {A : Type ℓ} → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
             → sym (p ∙ q) ≡ (sym q) ∙ (sym p)
cong-sym p = J (λ y₁ q′ → sym (p ∙ q′) ≡ sym q′ ∙ sym p)
              (J (λ _ p′ → (λ i → (p′ ∙ refl) (~ i)) ≡
              (λ i → refl (~ i)) ∙ (λ i → p′ (~ i))) refl p)

cong-∘ :  ∀ {ℓ ℓ′} → {A : Type ℓ} → {B : Type ℓ′} → (f : A → B)  → {x y z : A} → (p : x ≡ y) → (q : y ≡ z)
             → cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)
cong-∘ f p = J (λ _ q → cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)) (J (λ _ p → cong f (p ∙ refl) ≡ (cong f p) ∙ (cong f refl)) (cong (cong f)
           (sym (lUnit _)) ∙ (rUnit _)) p)


app*-l : ∀ {ℓₛ ℓₘ ℓₜ} → {A : Type* ℓₛ} → {B : Type* ℓₘ} → {C : Type* ℓₜ}
         → (f : fst (B →* C)) → {g g′ : fst (A →* B)} → g ~* g′
         → (f ∘* g) ~* (f ∘* g′)
app*-l {A = A} {B = B} {C = C} f {g = g} {g′ = g′} g~ =
  (λ a → cong (fst f) (fst g~ a))
  ,
  (cong (cong (fst f)) (snd g~)
  ∙ cong-∘ (fst f) (snd g) (sym (snd g′)))
  ∙ cong ((cong (fst f) (snd g)) ∙_) (lUnit _ ∙ cong (_∙ (λ i → fst f (snd g′ (~ i)))) (sym (rCancel _)) ∙ (sym (assoc (snd f) _ _))) 
  ∙ (assoc _ _ _)
  ∙ cong ((snd (f ∘* g)) ∙_) (sym (cong-sym (cong (fst f) (snd g′)) _))


app*-r : ∀ {ℓₛ ℓₘ ℓₜ} → {A : Type* ℓₛ} → {B : Type* ℓₘ} → {C : Type* ℓₜ}
         → {g g′ : fst (B →* C)} → g ~* g′
         → (f : fst (A →* B))
         → (g ∘* f) ~* (g′ ∘* f)
app*-r {A = A} {B = B} {C = C} {g = g} {g′ = g′} g~ f =
  (λ a → fst g~ ((fst f) a))
  ,
  {!!}


law1 : ∀ {ℓₛ ℓₘ ℓₜ} → {A : Type* ℓₛ} → {B : Type* ℓₘ} → {C : Type* ℓₜ}
         → {f : fst (B →* C)}
         → (f ∘* (0* {A = A})) ~* 0*
law1 {f = f} = (λ a → snd f) , (rUnit _ ∙ (lUnit _)) ∙ (assoc _ _ _) 

law2 : ∀ {ℓₛ ℓₜ} → {A : Type* ℓₛ} → {B : Type* ℓₜ}
         → {f : fst (A →* B)}
         → (f ∘* id*) ~* f
law2 {A = A} {B = B} {f = f} =
  (λ a → refl)
  ,
   rUnit _
   ∙ cong (((λ i → fst f (snd (id* {A = A})  i))) ∙_) (sym (rCancel (snd f)))  ∙ (assoc _ _ _)  

∘*-assoc* : {!!}
∘*-assoc* = {!!}

--pointed equivalence

record IsEquiv* {ℓₛ ℓₜ} {A : Type* ℓₛ} {B : Type* ℓₜ} (e : fst (A →* B)) : Type (ℓ-max ℓₛ ℓₜ) where
  constructor isEquiv*

  field
    l r : fst (B →* A)
    hl : (l ∘* e) ~* id*  
    hr : (e ∘* r) ~* id*


  to≃ : (fst A) ≃ (fst B) 
  to≃ = biInvEquiv→Equiv-right (biInvEquiv (fst e) (fst r) (fst hr) (fst l) (fst hl)) 

_≃*_ : ∀ {ℓₛ ℓₜ} → (A : Type* ℓₛ) → (B : Type* ℓₜ) → Set (ℓ-max ℓₛ ℓₜ)
A ≃* B = Σ _ (IsEquiv* {A = A} {B = B})



≃*id : ∀ {ℓ} → (A : Type* ℓ) → A ≃* A
≃*id A = id* , isEquiv* id* id* law2 law2

compEquiv* : ∀ {ℓₛ ℓₘ ℓₜ} → {A : Type* ℓₛ} → {B : Type* ℓₘ} → {C : Type* ℓₜ}
         → (A ≃* B) → (B ≃* C) → (A ≃* C)
compEquiv* f g =
  ((fst g) ∘* (fst f))
  ,
  isEquiv*
    ((l (snd f)) ∘* (l (snd g)))
    (((r (snd f)) ∘* (r (snd g))))
    {! (hl (snd g))!}
    {!!}
  where open IsEquiv*


lem-i : ∀ {ℓₛ ℓₜ} → {A : Type* ℓₛ} → {B : Type* ℓₜ}
        → (f : fst (A →* B)) → IsEquiv* f ≃ isEquiv (fst f)
lem-i {A = A} {B} f =
  (λ x → snd (IsEquiv*.to≃ x))
  ,
  record { equiv-proof = λ y → (isEquiv* ( (invEq (_ , y) , {!!})) {!!} {!!} {!!} , {!!}) , {!!} }

lem-ii : ∀ {ℓ} → {A B : Type* ℓ} → isEquiv {A = (fst A) ≃ (fst B)} {B = A ≃* B} {!!}
lem-ii = {!!}
