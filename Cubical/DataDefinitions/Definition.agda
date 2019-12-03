{-# OPTIONS --cubical --safe #-}

module Cubical.DataDefinitions.Definition where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Logic

open import Cubical.Data.Sum

open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary


open import Cubical.Data.Universe

open import Cubical.HITs.SetQuotients


Iso≡ : ∀ {ℓ} → (A : Type ℓ) → (iso1 iso2 : (Iso A A))
         → (fun= : Iso.fun iso1 ≡ Iso.fun iso2)
         → (inv= : Iso.inv iso1 ≡ Iso.inv iso2)
         → (sec= : ( transport (λ i₁ → (b : A) → fun= i₁ (inv= i₁ b) ≡ b) (Iso.rightInv iso1)) ≡ (Iso.rightInv iso2))
         → (ret= : ( transport (λ i₁ → (b : A) → inv= i₁ (fun= i₁ b) ≡ b) (Iso.leftInv iso1)) ≡ (Iso.leftInv iso2))
         → iso1 ≡ iso2 
Iso.fun (Iso≡ A iso1 iso2 fun= inv= _ _ i) = fun= i
Iso.inv (Iso≡ A iso1 iso2 fun= inv= _ _ i) = inv= i
Iso.rightInv (Iso≡ A iso1 iso2 fun= inv= sec= ret= i) = toPathP {A = λ i₁ → (section (fun= i₁) (inv= i₁))} {x = Iso.rightInv iso1} {y = Iso.rightInv iso2}
                   ( sec=) i   
Iso.leftInv (Iso≡ A iso1 iso2 fun= inv= sec= ret= i) = toPathP {A = λ i₁ → (retract (fun= i₁) (inv= i₁))} {x = Iso.leftInv iso1} {y = Iso.leftInv iso2}
                   ( ret=) i


Iso≡-Set : ∀ {ℓ} → (A : Type ℓ) → isSet A → (iso1 iso2 : (Iso A A))
         → (fun= : Iso.fun iso1 ≡ Iso.fun iso2)
         → (inv= : Iso.inv iso1 ≡ Iso.inv iso2)
         → iso1 ≡ iso2 
Iso.fun (Iso≡-Set A x iso1 iso2 fun= inv= i) = fun= i
Iso.inv (Iso≡-Set A x iso1 iso2 fun= inv= i) = inv= i
Iso.rightInv (Iso≡-Set A x iso1 iso2 fun= inv= i) b = x _ _ (coe0→i (λ x₁ →  fun= x₁ (inv= x₁ b) ≡ b) i (Iso.rightInv iso1 b))
                                                           ((coe1→i (λ x₁ →  fun= x₁ (inv= x₁ b) ≡ b) i (Iso.rightInv iso2 b))) i
Iso.leftInv (Iso≡-Set A x iso1 iso2 fun= inv= i) b = x _ _ (coe0→i (λ x₁ → inv= x₁ (fun= x₁ b) ≡ b) i (Iso.leftInv iso1 b))
                                                           ((coe1→i (λ x₁ → inv= x₁ (fun= x₁ b) ≡ b) i (Iso.leftInv iso2 b))) i


isSet-Iso-≡ : ∀ {ℓ} → (A : Type ℓ) → isSet A → Iso (Iso A A) (A ≡ A) 
isSet-Iso-≡ A isSet-A = iso (isoToPath) pathToIso h-sec h-ret
  where
    h-sec : (b : A ≡ A) → isoToPath (pathToIso b) ≡ b
    h-sec b = isInjectiveTransport (funExt λ x → transportRefl _)

    h-ret : (a : Iso A A) → pathToIso (isoToPath a) ≡ a
    h-ret a =  Iso≡-Set A isSet-A (pathToIso (isoToPath a)) a
                     (funExt λ x → transportRefl _)
                     (funExt λ x → cong (Iso.inv a) (transportRefl _))




record IsDefiningProperty (B : Type₀ → Type₁) : Type₁ where
  constructor isDefinition

  field
    ww1 : ∀ A₁ A₂ → B A₁ → B A₂ → A₁ → A₂
    ww-law : ∀ A → ∀ ba → ∀ x → ww1 A A ba ba x ≡ x
  
    ww3 : ∀ A₁ A₂ A₃ → ∀ ba₁ → ∀ ba₂ → ∀ ba₃ → ∀ x →  ((ww1 A₂ A₃ ba₂ ba₃) ∘ (ww1 A₁ A₂ ba₁ ba₂)) x ≡ (ww1 A₁ A₃ ba₁ ba₃) x
    ww-Set : ∀ A → B A → isSet A
    

  ww2 : ∀ A₁ A₂ → ∀ x → ∀ xx → section (ww1 A₂ A₁ x xx) (ww1 A₁ A₂ xx x)
  ww2 A₁ A₂ x xx b = (ww3 A₁ A₂ A₁ xx x xx b) ∙ (ww-law _ _ b) 

  defToIso : ∀ {A₁ A₂} → B A₂ → B A₁ → Iso A₂ A₁
  defToIso {A₁} {A₂} x xx = (iso (ww1 A₂ A₁ x xx) (ww1 A₁ A₂ xx x) (ww2 A₁ A₂ x xx) ((ww2 A₂ A₁ xx x)))  

  defToPath : ∀ {A₁ A₂} → B A₂ → B A₁ → A₂ ≡ A₁
  defToPath {A₁} {A₂} x xx = isoToPath (defToIso x xx)  

  defToPath-Refl : ∀ {A} → ∀ ba → defToPath ba ba ≡ refl
  defToPath-Refl {A} ba = isInjectiveTransport (funExt λ x → cong (transp (λ i → A) i0) (ww-law _ _ x))

  defToPath-consistent : ∀ {A₁ A₂} → (ba : B A₁) →  (b : A₁ ≡ A₂) → defToPath ba (subst B b ba) ≡ b
  defToPath-consistent ba b =
    J {x = _} (λ y x → defToPath {y} {_} ba ((subst B x ba)) ≡ x) ((cong (defToPath ba ) (transportRefl _) ∙ defToPath-Refl ba)) b
  
  xxx : {𝓘 : Type₀} {𝓐 : 𝓘 → Type₀} (B𝓐 : ∀ 𝓲 → B (𝓐 𝓲 )) → Type₀
  xxx {𝓘} {𝓐} B𝓐 = (Σ 𝓘 𝓐) / λ x x₁ → ww1 _ _ (B𝓐 (fst x)) (B𝓐 (fst x₁)) (snd x) ≡ (snd x₁)

  xxx≡ : {𝓘 : Type₀} {𝓐 : 𝓘 → Type₀} (B𝓐 : ∀ 𝓲 → B (𝓐 𝓲 )) → ∀ 𝓲 → 𝓐 𝓲 ≡  (xxx B𝓐)
  xxx≡ {_} {𝓐} B𝓐 𝓲 = isoToPath (iso
    (λ x → _/_.[ 𝓲 , x ])
    ( elimSetQuotients (λ x → ww-Set (𝓐 𝓲) (B𝓐 𝓲)) (λ a → ww1 _ _ (B𝓐 (fst a)) (B𝓐 𝓲) (snd a) )
      λ a b r →
      let ww =  (cong (ww1 (𝓐 (fst b)) (𝓐 𝓲) (B𝓐 (fst b)) (B𝓐 𝓲)) r)
      in  sym ( (ww3 _ _ _ _ _ _ (snd a))) ∙ ww
       
     )
    ( elimSetQuotientsProp (λ x → squash/ _ x) (λ a → eq/ _ a (ww2 _ _ _ _ _)))
    λ a → ww-law _ _ a
   )

  B-xxx : {𝓘 : Type₀} {𝓐 : 𝓘 → Type₀} (B𝓐 : ∀ 𝓲 → B (𝓐 𝓲 )) → 𝓘 → B (xxx B𝓐)
  B-xxx B𝓐 x = subst B (xxx≡ (B𝓐) x) (B𝓐 x)



record Definition : Type (ℓ-suc (ℓ-suc ℓ-zero)) where
  constructor definition
  field
    𝑰def : Type₀
    defs : 𝑰def → Type₀ → Type₁
    areDefs : ∀ {𝒊} → (IsDefiningProperty (defs 𝒊)) 
    defs→ : ∀ {𝒊₁} {𝒊₂} → ∀ {A} → defs 𝒊₁ A → defs 𝒊₂ A
    defs-id : ∀ {𝒊} → ∀ {A} → (d : defs 𝒊 A) → defs→ d ≡ d
    defs-∘ : ∀ {𝒊₁ 𝒊₂ 𝒊₃} → ∀ {A} →
               (x : defs _ A) → ((defs→ {𝒊₂} {𝒊₃}) ∘ (defs→ {𝒊₁} {𝒊₂})) x ≡ (defs→ {𝒊₁} {𝒊₃}) x  




record DataType : Type (ℓ-suc (ℓ-suc ℓ-zero)) where

  constructor dataType

  field
    def : Definition

  open Definition def

  open IsDefiningProperty

  field
    𝑰 : Type₀
    impl-dp : 𝑰 → 𝑰def
    impl : 𝑰 → Type₀
    impl-ok : ∀ 𝒊 → defs (impl-dp 𝒊) (impl 𝒊)

  impl→ : ∀ {𝒊₁ 𝒊₂} → impl 𝒊₁ → impl 𝒊₂ 
  impl→ {𝒊₁} {𝒊₂} x =  ww1 {B = defs (impl-dp 𝒊₂)} areDefs (impl 𝒊₁) (impl 𝒊₂) (defs→ ((impl-ok 𝒊₁))) (impl-ok 𝒊₂) x

  -- data DT : Type₀ where
  --   dt : ∀ 𝒊 → impl 𝒊 → DT
  --   dt= : ∀ 𝒊₁ 𝒊₂ → ∀ a → dt 𝒊₁ a ≡ dt 𝒊₂ (impl→ a)

  

  DT : Type₀ 
  DT = Σ _ impl / λ a b → impl→ (snd a) ≡ snd b

  DT≡ : ∀ 𝒊 → impl 𝒊 ≡ DT
  DT≡ 𝒊 = isoToPath (iso
    (λ x → _/_.[ _ , x ])
    (elimSetQuotients (λ x → ww-Set (areDefs {impl-dp 𝒊}) (impl 𝒊) (impl-ok _))
      (λ a → impl→ (snd a))
      λ a b r →
       {!!})
    (( elimSetQuotientsProp (λ x → squash/ _ x) (λ a → eq/ _ a {!!})))
    {!!}
    )

  B-DT : ∀ 𝒊 → defs 𝒊 DT
  B-DT = {!!}

-- IsDef≡ : (A : Type₀) → IsDefinition λ x → A ≡ x
-- IsDef≡ A = isDefinition
--   (λ A₁ A₂ x x₁ → transport ((sym x) ∙ x₁))
--   (λ A₁ ba x → transportTransport⁻ ba _ ∙ transportRefl _)
--   λ A₁ A₂ x xx b →
--     let q = J (λ (A′ : Type₀) (x₁ : A₂ ≡ A′) → ∀ y → (transport x₁ (transport (sym x₁) y)) ≡ y )
--             (λ y → transportRefl _ ∙ transportRefl y)
--             (((sym x) ∙ xx)) --J {!!} {!!} xx 
--     in  (cong (transport ((sym x) ∙ xx)) (cong (transp (λ i → x i) i0) (cong (transp (λ i → xx (~ i)) i0) (transportRefl b)) ∙ (sym (transportRefl _))))
--         ∙ q b


-- -- data xxx {B : _} (isd : IsDefinition B) {𝓘 : Type₀} (𝓐Σ : 𝓘 → Σ Type₀ B) : Type₀ where
-- --   xx : (𝓲 : 𝓘) → fst (𝓐Σ 𝓲) → xxx isd 𝓐Σ



-- record IsFamilyDefinition {B₀} {isd : IsDefinition B₀} (B : ∀ {A₀} → B₀ A₀ → (A₀ → Type₀) → Type₁) : Type₁ where
--   constructor isFamilyDefinition
--   field
--     wf1 : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀} → ∀ A₁ A₂
--             → (B b₀a₀ A₁) → (B b₀a₀ A₂) → ∀ a₀ → A₁ a₀ → A₂ a₀
--     wf-law : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀} → ∀ A → ∀ ba → (a₀ : A₀) → (x : A a₀) → wf1 {b₀a₀ = b₀a₀} A A ba ba a₀ x ≡ x
--     wf2 : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀} → ∀ A₁ A₂
--             → (ba₁ : B b₀a₀ A₁) → (ba₂ : B b₀a₀ A₂) → ∀ a₀
--             → section (wf1 {A₀} {b₀a₀} A₂ A₁ ba₂ ba₁ a₀) (wf1 {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ a₀)


--   defToIso : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀} → ∀ A₁ A₂
--                → (ba₁ : B b₀a₀ A₁) → (ba₂ : B b₀a₀ A₂) → ∀ a₀ → Iso (A₁ a₀) (A₂ a₀)
--   defToIso {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ a₀ =
--     iso
--     (wf1 {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ a₀)
--     (wf1 {A₀} {b₀a₀} A₂ A₁ ba₂ ba₁ a₀)
--     (wf2 {A₀} {b₀a₀} A₂ A₁ ba₂ ba₁ a₀)
--     (wf2 {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ a₀) 

--   defToPath : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀} → ∀ A₁ A₂
--                → (ba₁ : B b₀a₀ A₁) → (ba₂ : B b₀a₀ A₂) → (A₁ ≡ A₂)
--   defToPath {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ = funExt λ x → isoToPath (defToIso {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ x) 




--   -- fiberDefinition : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀}
--   --                   → ∀ A → (ba : B b₀a₀ A) → (a₀ : A₀)
--   --                   → IsDefinition λ A′ → {!A′ ≡ A!}
--   -- fiberDefinition = {!ua !} 
