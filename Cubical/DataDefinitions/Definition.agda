{-# OPTIONS --cubical --safe #-}

module Cubical.DataDefinitions.Definition where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Logic

open import Cubical.Data.Sum

open import Cubical.Data.Sigma

open import Cubical.Data.Bool

open import Cubical.Data.Unit

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
  constructor isDefiningProperty

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

  field
    ww4 : ∀ {A₁ A₂} → (ba₁ : B A₁) → (ba₂ : B A₂) → subst B (defToPath ba₁ ba₂) ba₁ ≡ ba₂

  defToPath-Refl : ∀ {A} → ∀ ba → defToPath ba ba ≡ refl
  defToPath-Refl {A} ba = isInjectiveTransport (funExt λ x → cong (transp (λ i → A) i0) (ww-law _ _ x))

  defToPath-consistent : ∀ {A₁ A₂} → (ba : B A₁) →  (b : A₁ ≡ A₂) → defToPath ba (subst B b ba) ≡ b
  defToPath-consistent ba b =
    J {x = _} (λ y x → defToPath {y} {_} ba ((subst B x ba)) ≡ x) ((cong (defToPath ba ) (transportRefl _) ∙ defToPath-Refl ba)) b

  -- zzz : ∀ A₀ → (ba₀ : B A₀)
  --         → ∀ A₁ A₂ → ∀ ba₁ → ∀ ba₂
  --         → ∀ x →  ww1 A₁ A₂ ba₁ ba₂ x ≡ {!(defToPath ba₁ ba₀) ∙ (defToPath ba₀ ba₂) !}
  -- zzz = {!!}

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



-- record Definition : Type (ℓ-suc (ℓ-suc ℓ-zero)) where
--   constructor definition

--   open IsDefiningProperty public

--   field
--     𝑰def : Type₀
--     defs : 𝑰def → Type₀ → Type₁
--     areDefs : ∀ {𝒊} → (IsDefiningProperty (defs 𝒊)) 
--     defs→ : ∀ {𝒊₁} {𝒊₂} → ∀ {A} → defs 𝒊₁ A → defs 𝒊₂ A
--     defs-id : ∀ {𝒊} → ∀ {A} → (d : defs 𝒊 A) → defs→ d ≡ d
--     defs-∘ : ∀ {𝒊₁ 𝒊₂ 𝒊₃} → ∀ {A} →
--                (x : defs _ A) → ((defs→ {𝒊₂} {𝒊₃}) ∘ (defs→ {𝒊₁} {𝒊₂})) x ≡ (defs→ {𝒊₁} {𝒊₃}) x

--   def-trans : ∀ {𝒊₁ 𝒊₂} → ∀ {A₁ A₂} → (ba₁ : defs 𝒊₁ A₁) → (ba₂ : defs 𝒊₂ A₂)
--                → A₁ → A₂ 
--   def-trans = λ ba₁ ba₂ → ww1 {B = defs _} areDefs _ _ ba₁ (defs→ ba₂)


--   def-trans′ : ∀ {𝒊₁ 𝒊₂} → ∀ {A₁ A₂} → (ba₁ : defs 𝒊₁ A₁) → (ba₂ : defs 𝒊₂ A₂)
--                → A₁ → A₂ 
--   def-trans′ = λ ba₁ ba₂ → ww1 {B = defs _} areDefs _ _ (defs→ ba₁) ba₂


--   field
--     defs-f : ∀ {𝒊₁} {𝒊₂} → ∀ {A₁ A₂} → (ba₁ : defs 𝒊₁ A₁) → (ba₂ : defs 𝒊₂ A₂) → ∀ x
--                → def-trans ba₁ ba₂ x ≡ def-trans′ ba₁ ba₂ x 

--   defs-F : ∀ {𝒊₁} {𝒊₂} → ∀ {A₁ A₂} → (ba₁ : defs 𝒊₁ A₁) → (ba₂ : defs 𝒊₁ A₂) → ∀ x
--                → ww1 {B = defs _} areDefs _ _ ba₁ ba₂ x
--                ≡
--                ww1 {B = defs 𝒊₂} areDefs _ _ (defs→ ba₁) (defs→ ba₂) x
--   defs-F ba₁ ba₂ x =
--    cong (λ qq → ww1 areDefs _ _ ba₁ qq x) (sym ( defs-∘ _ ∙ (defs-id _)))
--    ∙ defs-f ba₁ (defs→ ba₂) x


-- Being : ∀ A → isSet A → IsDefiningProperty (A ≡_)
-- Being A isSetA =
--   isDefiningProperty
--   (λ A₁ A₂ x x₁ → transport ((sym x) ∙ x₁))
--   (λ A₁ ba x → transportTransport⁻ ba (transport refl x) ∙ (transportRefl x))
--   (λ A₁ A₂ A₃ ba₁ ba₂ ba₃ x →
--    J
--    (λ A₂′ ba₂′ → ((λ {a} → transport ((λ i → ba₂′ (~ i)) ∙ ba₃)) ∘ transport ((λ i → ba₁ (~ i)) ∙ ba₂′)) x
--                            ≡ transport ((λ i → ba₁ (~ i)) ∙ ba₃) x)
--    (J (λ A₃′ ba₃′ → transport ((λ i → refl {x = A} (~ i)) ∙ ba₃′) (transport ((λ i → ba₁ (~ i)) ∙ refl) x) ≡ transport ((λ i → ba₁ (~ i)) ∙ ba₃′) x)
--    (cong (transp (λ i → A) i0) (transportRefl (transp (λ .i → A) i0
--        (transp (λ i → A) i0
--         (transp (λ i → ba₁ (~ i)) i0 (transp (λ .i → A₁) i0 x)))) ∙ (transportRefl (transp (λ i → A) i0
--        (transp (λ i → ba₁ (~ i)) i0 (transp (λ .i → A₁) i0 x))) ∙ transportRefl _ )))
--    ba₃)
--    ba₂
--   )
--   λ A₁ x → subst isSet x isSetA

-- record DataType : Type (ℓ-suc (ℓ-suc ℓ-zero)) where

--   constructor dataType

--   field
--     def : Definition

--   open Definition def public

--   open IsDefiningProperty

--   field
--     𝑰 : Type₀
--     impl-dp : 𝑰 → 𝑰def
--     impl : 𝑰 → Type₀
--     impl-ok : ∀ 𝒊 → defs (impl-dp 𝒊) (impl 𝒊)

--   impl→′ : ∀ {𝒊₁ 𝒊₂} → impl 𝒊₁ → impl 𝒊₂ 
--   impl→′ {𝒊₁} {𝒊₂} x =  ww1 {B = defs (impl-dp 𝒊₂)} areDefs (impl 𝒊₁) (impl 𝒊₂) (defs→ ((impl-ok 𝒊₁))) (impl-ok 𝒊₂) x

--   impl→ : ∀ {𝒊₁ 𝒊₂} → impl 𝒊₁ → impl 𝒊₂ 
--   impl→ {𝒊₁} {𝒊₂} x = ww1 {B = defs (impl-dp 𝒊₁)} areDefs (impl 𝒊₁) (impl 𝒊₂) ((impl-ok 𝒊₁)) (defs→ (impl-ok 𝒊₂)) x

--   def-impl-law : ∀ {𝒊₁ 𝒊₂} → ∀ x → impl→ {𝒊₁} {𝒊₂} x ≡ impl→′ x
--   def-impl-law = defs-f _ _

--   impl-id : ∀ {𝒊} → ∀ x → impl→ {𝒊} {𝒊} x ≡ x
--   impl-id {𝒊} x = subst (λ q → ww1 areDefs (impl 𝒊) (impl 𝒊) (impl-ok 𝒊) (q) x ≡ x)
--                   (sym (defs-id (impl-ok 𝒊)))
--                   (ww-law areDefs _ (impl-ok 𝒊) x)
  
--   def-impl-∘ : ∀ {𝒊₁ 𝒊₂ 𝒊₃} → ∀ x → impl→ {𝒊₂} {𝒊₃} (impl→ {𝒊₁} {𝒊₂} x) ≡ impl→ x
--   def-impl-∘ {𝒊₁} {𝒊₂} {𝒊₃} x =
--      (cong (λ f → f ((ww1 areDefs (impl 𝒊₁) (impl 𝒊₂) (impl-ok 𝒊₁) (defs→ (impl-ok 𝒊₂)) x)))
--               (funExt (defs-F {impl-dp 𝒊₂} {impl-dp 𝒊₁} (impl-ok 𝒊₂) (defs→ (impl-ok 𝒊₃)))))
--      ∙ ww3 areDefs (impl 𝒊₁) (impl 𝒊₂) (impl 𝒊₃) (impl-ok 𝒊₁) (defs→ (impl-ok 𝒊₂)) (defs→ (defs→ (impl-ok 𝒊₃))) x  
--      ∙ cong (λ qq → ww1 areDefs (impl 𝒊₁) (impl 𝒊₃) (impl-ok 𝒊₁) (qq) x) (defs-∘ _)

--   def-section : ∀ {𝒊₁ 𝒊₂} →  section (impl→ {𝒊₂} {𝒊₁}) (impl→ {𝒊₁} {𝒊₂})
--   def-section {𝒊₁} {𝒊₂} b = def-impl-∘ _ ∙ impl-id _

--   DT : Type₀ 
--   DT = Σ _ impl / λ a b → impl→ (snd a) ≡ snd b

--   DT≡ : ∀ 𝒊 → impl 𝒊 ≡ DT
--   DT≡ 𝒊 = isoToPath (iso
--     (λ x → _/_.[ _ , x ])
--     (elimSetQuotients (λ x → ww-Set (areDefs {impl-dp 𝒊}) (impl 𝒊) (impl-ok _))
--       (λ a → impl→ (snd a))
--       λ a b r → ((sym (def-impl-∘ _)) ∙  (cong (impl→) r)))
--     (( elimSetQuotientsProp (λ x → squash/ _ x) (λ a → eq/ _ a (def-section _))))
--     λ a → impl-id _
--     -- λ a → 
--     )

--   B-DT : ∀ 𝒊def → ∀ 𝒊 → defs 𝒊def DT
--   B-DT 𝒊def 𝒊 = subst (defs 𝒊def) (DT≡ 𝒊 ) (defs→ (impl-ok 𝒊) )

--   dt : ∀ 𝒊 → impl 𝒊 → DT
--   dt 𝒊 x = _/_.[ 𝒊 , x ]



-- TrivialDef : (A : Type₀) → isSet A → Definition
-- TrivialDef A isSet-A =
--   definition
--     Unit
--     (λ _ → A ≡_)
--     (Being _ isSet-A)
--     (idfun _)
--     (λ _ → refl)
--     (λ _ → refl)
--     λ ba₁ ba₂ x → refl


-- SimpleDef : ∀ {B} → IsDefiningProperty B → Definition
-- SimpleDef {B} idp =
--   definition
--     Unit
--     (λ _ → B)
--     idp
--     (idfun _)
--     (λ _ → refl)
--     (λ _ → refl)
--     λ ba₁ ba₂ x → refl


-- record _Def≈_ {B₁ B₂} (idp₁ : IsDefiningProperty B₁) (idp₂ : IsDefiningProperty B₂) : Type₁ where
--   constructor def≈

--   open IsDefiningProperty

--   field 
--     1→2 : ∀ {A} → B₁ A → B₂ A
--     2→1 : ∀ {A} → B₂ A → B₁ A
--     sec : ∀ {A} → section (1→2 {A}) 2→1
--     ret : ∀ {A} → retract (1→2 {A}) 2→1
--     law≈ : ∀ {A₁′} → ∀ {A₂′} → ∀ ba₁′ → ∀ ba₂′ → ∀ x →
--                         ww1 idp₂ A₁′ A₂′ ba₁′ (1→2 ba₂′) x ≡
--                         ww1 idp₁ A₁′ A₂′ (2→1 ba₁′) ba₂′ x 
  
--   law≈′ : (∀ {A₁′} → ∀ {A₂′} → ∀ ba₁′ → ∀ ba₂′ → ∀ x → IsDefiningProperty.ww1 idp₁ A₁′ A₂′ ba₁′ (2→1 ba₂′) x ≡
--                         IsDefiningProperty.ww1 idp₂ A₁′ A₂′ (1→2 ba₁′) ba₂′ x )
--   law≈′ {A₁′} {A₂′} ba₁′ ba₂′ x =
--       (cong (λ ba₁′ → ww1 idp₁ A₁′ A₂′ ba₁′ (2→1 ba₂′) x) (sym (ret ba₁′)))
--       ∙ sym (law≈ {A₁′} {A₂′} (1→2 ba₁′) (2→1 ba₂′) x) ∙
--       cong (λ a →  ww1 idp₂ A₁′ A₂′ (1→2 ba₁′) a x) (sec ba₂′)

  
--   From2Defs : Definition
--   From2Defs = 
--      definition
--        Bool
--        (caseBool B₁ B₂)
--        (λ {b} → areDefs b)
--        defs→
--        defs-id
--        (λ {𝒊₁} {𝒊₂} {𝒊₃} {A} → defs-∘ {𝒊₁} {𝒊₂} {𝒊₃} {A})
--        λ {𝒊₁} {𝒊₂} {A₁} {A₂} → defs-f {𝒊₁} {𝒊₂} {A₁} {A₂}

--      where
--        areDefs : ∀ b → IsDefiningProperty (caseBool B₁ B₂ b)
--        areDefs false = idp₂
--        areDefs true = idp₁

--        defs→ : {𝒊₁ 𝒊₂ : Bool} {A : Set} → caseBool B₁ B₂ 𝒊₁ A → caseBool B₁ B₂ 𝒊₂ A
--        defs→ {false} {false} {A} x = x
--        defs→ {false} {true} {A} = 2→1
--        defs→ {true} {false} {A} = 1→2
--        defs→ {true} {true} {A} x = x

--        defs-id : {𝒊 : Bool} {A : Set} (d : caseBool B₁ B₂ 𝒊 A) → defs→ d ≡ d
--        defs-id {false} d = refl
--        defs-id {true} d = refl

--        defs-∘ :  {𝒊₁ 𝒊₂ 𝒊₃ : Bool} {A : Set} (x : caseBool B₁ B₂ 𝒊₁ A) → (defs→ ∘ defs→ {𝒊₁} {𝒊₂}) x ≡ defs→ x
--        defs-∘ {false} {false} {false} x = refl
--        defs-∘ {false} {false} {true} x = refl
--        defs-∘ {false} {true} {false} = sec 
--        defs-∘ {false} {true} {true} x = refl
--        defs-∘ {true} {false} {false} x = refl
--        defs-∘ {true} {false} {true} = ret
--        defs-∘ {true} {true} {false} x = refl
--        defs-∘ {true} {true} {true} x = refl

--        defs-f : {𝒊₁ 𝒊₂ : Bool} {A₁ A₂ : Set} (ba₁ : caseBool B₁ B₂ 𝒊₁ A₁)
--                    (ba₂ : caseBool B₁ B₂ 𝒊₂ A₂) (x : A₁) →
--                     IsDefiningProperty.ww1 (areDefs 𝒊₁) A₁ A₂ ba₁ (defs→ ba₂) x ≡
--                     IsDefiningProperty.ww1 (areDefs 𝒊₂) A₁ A₂ (defs→ ba₁) ba₂ x
--        defs-f {false} {false} ba₁ ba₂ x = refl
--        defs-f {false} {true} = law≈
--        defs-f {true} {false} = law≈′
--        defs-f {true} {true} ba₁ ba₂ x = refl

-- open _Def≈_ using (From2Defs) public



-- DT-fromSome : ∀ B → (idp : IsDefiningProperty B) → ∀ A → (B A) → ∀ A′ → B A′ → DataType 
-- DataType.def (DT-fromSome B idp A x A′ x₁) = SimpleDef idp
-- DataType.𝑰 (DT-fromSome B idp A x A′ x₁) = Bool
-- DataType.impl-dp (DT-fromSome B idp A x A′ x₁) x₂ = _
-- DataType.impl (DT-fromSome B idp A x A′ x₁) false = A
-- DataType.impl (DT-fromSome B idp A x A′ x₁) true = A′
-- DataType.impl-ok (DT-fromSome B idp A x A′ x₁) false = x
-- DataType.impl-ok (DT-fromSome B idp A x A′ x₁) true = x₁

-- -- IsDef≡ : (A : Type₀) → IsDefinition λ x → A ≡ x
-- -- IsDef≡ A = isDefinition
-- --   (λ A₁ A₂ x x₁ → transport ((sym x) ∙ x₁))
-- --   (λ A₁ ba x → transportTransport⁻ ba _ ∙ transportRefl _)
-- --   λ A₁ A₂ x xx b →
-- --     let q = J (λ (A′ : Type₀) (x₁ : A₂ ≡ A′) → ∀ y → (transport x₁ (transport (sym x₁) y)) ≡ y )
-- --             (λ y → transportRefl _ ∙ transportRefl y)
-- --             (((sym x) ∙ xx)) --J {!!} {!!} xx 
-- --     in  (cong (transport ((sym x) ∙ xx)) (cong (transp (λ i → x i) i0) (cong (transp (λ i → xx (~ i)) i0) (transportRefl b)) ∙ (sym (transportRefl _))))
-- --         ∙ q b


-- -- -- data xxx {B : _} (isd : IsDefinition B) {𝓘 : Type₀} (𝓐Σ : 𝓘 → Σ Type₀ B) : Type₀ where
-- -- --   xx : (𝓲 : 𝓘) → fst (𝓐Σ 𝓲) → xxx isd 𝓐Σ



-- -- record IsFamilyDefinition {B₀} {isd : IsDefinition B₀} (B : ∀ {A₀} → B₀ A₀ → (A₀ → Type₀) → Type₁) : Type₁ where
-- --   constructor isFamilyDefinition
-- --   field
-- --     wf1 : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀} → ∀ A₁ A₂
-- --             → (B b₀a₀ A₁) → (B b₀a₀ A₂) → ∀ a₀ → A₁ a₀ → A₂ a₀
-- --     wf-law : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀} → ∀ A → ∀ ba → (a₀ : A₀) → (x : A a₀) → wf1 {b₀a₀ = b₀a₀} A A ba ba a₀ x ≡ x
-- --     wf2 : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀} → ∀ A₁ A₂
-- --             → (ba₁ : B b₀a₀ A₁) → (ba₂ : B b₀a₀ A₂) → ∀ a₀
-- --             → section (wf1 {A₀} {b₀a₀} A₂ A₁ ba₂ ba₁ a₀) (wf1 {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ a₀)


-- --   defToIso : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀} → ∀ A₁ A₂
-- --                → (ba₁ : B b₀a₀ A₁) → (ba₂ : B b₀a₀ A₂) → ∀ a₀ → Iso (A₁ a₀) (A₂ a₀)
-- --   defToIso {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ a₀ =
-- --     iso
-- --     (wf1 {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ a₀)
-- --     (wf1 {A₀} {b₀a₀} A₂ A₁ ba₂ ba₁ a₀)
-- --     (wf2 {A₀} {b₀a₀} A₂ A₁ ba₂ ba₁ a₀)
-- --     (wf2 {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ a₀) 

-- --   defToPath : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀} → ∀ A₁ A₂
-- --                → (ba₁ : B b₀a₀ A₁) → (ba₂ : B b₀a₀ A₂) → (A₁ ≡ A₂)
-- --   defToPath {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ = funExt λ x → isoToPath (defToIso {A₀} {b₀a₀} A₁ A₂ ba₁ ba₂ x) 




-- --   -- fiberDefinition : ∀ {A₀} → ∀ {b₀a₀ : B₀ A₀}
-- --   --                   → ∀ A → (ba : B b₀a₀ A) → (a₀ : A₀)
-- --   --                   → IsDefinition λ A′ → {!A′ ≡ A!}
-- --   -- fiberDefinition = {!ua !} 
