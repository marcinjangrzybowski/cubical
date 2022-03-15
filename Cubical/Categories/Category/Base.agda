{-# OPTIONS --safe #-}
module Cubical.Categories.Category.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Foundations.Transport

open import Cubical.Data.Bool

open import Cubical.Data.Sigma

open import Cubical.HITs.SetTruncation

private
  variable
    ℓ ℓ' : Level

-- Categories with hom-sets
record Category ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  -- no-eta-equality ; NOTE: need eta equality for `opop`
  field
    ob : Type ℓ
    Hom[_,_] : ob → ob → Type ℓ'
    id   : ∀ {x} → Hom[ x , x ]
    _⋆_  : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ]) → Hom[ x , z ]
    ⋆IdL : ∀ {x y} (f : Hom[ x , y ]) → id ⋆ f ≡ f
    ⋆IdR : ∀ {x y} (f : Hom[ x , y ]) → f ⋆ id ≡ f
    ⋆Assoc : ∀ {x y z w} (f : Hom[ x , y ]) (g : Hom[ y , z ]) (h : Hom[ z , w ])
           → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
    isSetHom : ∀ {x y} → isSet Hom[ x , y ]

  -- composition: alternative to diagramatic order
  _∘_ : ∀ {x y z} (g : Hom[ y , z ]) (f : Hom[ x , y ]) → Hom[ x , z ]
  g ∘ f = f ⋆ g

  infixr 9 _⋆_
  infixr 9 _∘_


trunc-subst-hSet : {A : Type ℓ} → {B : A → Type ℓ'} → (isSet-B : ∀ a → isSet (B a)) → {x y : A} → ∥ x ≡ y ∥₂ → B x → B y
trunc-subst-hSet isSet-B {x} {y} p = transport (elim (λ _ → isOfHLevel≡ 2 (isSet-B _) (isSet-B _) ) (cong _) p) 

subst-under-Π : ∀ {ℓ''} → {A : Type ℓ} → {D : Type ℓ''} → {B : A → Type ℓ'} → {x y : A} → (p : x ≡ y )
                 → (f : ∀ {a} → (B a) → D) → (Bx : (B x))
                 → f Bx ≡ f (subst B p Bx) 
subst-under-Π {B = B} p f Bx i = f { p i } (transp (λ i₁ → B (p (i₁ ∧ i))) (~ i) Bx)


module Alt where

  record CategoryAlt ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

    field
      ob : Type ℓ
      HomF[_] : ob → Type ℓ'
      isSetHom : ∀ x → isSet HomF[ x ]
      target : ∀ {x} → HomF[ x ] → ob
      id   : ∀ {x} → HomF[ x ]      
      id-target : ∥ (∀ x → x ≡ target (id {x})) ∥₂
      
    id-target' : ∀ {x} → ∥ x ≡ target (id {x}) ∥₂
    id-target' {x} = setTruncΠ id-target x
    
    field

      _⋆_  : ∀ {x} (f : HomF[ x ]) (g : HomF[ target f ]) → HomF[ x ]
      ⋆-target : ∥ (∀ x → (f : HomF[ x ]) → ∀ g → target (f ⋆ g) ≡ target g) ∥₂

    ⋆-target' : ∀ {x} → (f : HomF[ x ]) → ∀ g → ∥ target (f ⋆ g) ≡ target g ∥₂
    ⋆-target' {x} f g = setTruncΠ (setTruncΠ (setTruncΠ ⋆-target x ) f ) g 

    field
      ⋆IdL : ∀ {x} (f : HomF[ x ]) → id ⋆ trunc-subst-hSet isSetHom (id-target') f ≡ f
      ⋆IdR : ∀ {x} (f : HomF[ x ]) → f ⋆ id ≡ f
      ⋆Assoc : ∀ {x} (f : HomF[ x ]) (g : HomF[ target f ]) (h : HomF[ target (f ⋆ g) ])
             → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ trunc-subst-hSet isSetHom (⋆-target' _ _) h)


    ToCategory : Category ℓ (ℓ-max ℓ ℓ')
    Category.ob ToCategory = ob
    Category.Hom[ ToCategory , A ] B = Σ HomF[ A ] λ x → ∥ B ≡ target x ∥₂
    Category.id ToCategory = id , setTruncΠ id-target _
    fst ((ToCategory Category.⋆ (f , f≡) ) (g , _)) = f ⋆ trunc-subst-hSet isSetHom f≡ g
    snd ((ToCategory Category.⋆ (f , f≡)) (g , g≡)) = 
        elim3ᵗ {D = λ f≡ _ _ → _ ≡ target (f ⋆ trunc-subst-hSet isSetHom f≡ g)}
          (λ f≡ g≡ ⋆-target → g≡ ∙ subst-under-Π f≡ target g ∙ sym (⋆-target _ f _))
           f≡ g≡ ⋆-target

    Category.⋆IdL ToCategory (f , f≡) = ΣPathP (⋆IdL _ , {!!})
    Category.⋆IdR ToCategory (f , f≡) =
      elim {B = λ x → (ToCategory Category.⋆ (f , x)) (id , setTruncΠ id-target _) ≡ (f , x)}
            (λ _ → isProp→isSet (isSetΣ (isSetHom _) (λ _ → squash₂) _ _))
            (λ f≡ → ΣPathP (( {!!}  ∙ ⋆IdR f) , {!!})) f≡ 
      --ΣPathP ({!subst-under-Π (snd f)!} ∙ ⋆IdR (fst f) , {!!})
    Category.⋆Assoc ToCategory (f , f≡) (g , g≡) (h , h≡) = ΣPathP (⋆Assoc _ _ _ ∙ cong (f ⋆_) {!!} , {!!})
    Category.isSetHom ToCategory = isSetΣ (isSetHom _) λ _ → squash₂

--   open Category

--   -- FromCategory : Category ℓ ℓ' → CategoryAlt ℓ (ℓ-max ℓ ℓ')
--   -- CategoryAlt.ob (FromCategory C) = ob C
--   -- CategoryAlt.HomF[ FromCategory C ] X = {!!}
--   -- CategoryAlt.target (FromCategory C) = {!elim!}
--   -- CategoryAlt.id (FromCategory C) = {!!}
--   -- CategoryAlt.id-target (FromCategory C) = {!!}
--   -- CategoryAlt._⋆_ (FromCategory C) = {!!}
--   -- CategoryAlt.⋆-target (FromCategory C) = {!!}
--   -- CategoryAlt.⋆IdL (FromCategory C) = {!!}
--   -- CategoryAlt.⋆IdR (FromCategory C) = {!!}
--   -- CategoryAlt.⋆Assoc (FromCategory C) = {!!}
--   -- CategoryAlt.isSetHom (FromCategory C) = squash₂

--   -- FromCategory : Category ℓ ℓ' → CategoryAlt ℓ (ℓ-max ℓ ℓ')
--   -- CategoryAlt.ob (FromCategory C) = ob C
--   -- CategoryAlt.HomF[ FromCategory C ] X = Σ _ (Hom[_,_] C X) 
--   -- CategoryAlt.target (FromCategory C) = fst
--   -- CategoryAlt.id (FromCategory C) = _ , Category.id C
--   -- CategoryAlt.id-target (FromCategory C) = refl
--   -- fst ((FromCategory C CategoryAlt.⋆ f) g) = _
--   -- snd ((FromCategory C CategoryAlt.⋆ f) g) = _⋆_ C (snd f) (snd g)
--   -- CategoryAlt.⋆-target (FromCategory C) _ _ = refl
--   -- fst (CategoryAlt.⋆IdL (FromCategory C) (fst₁ , snd₁) i) = transportRefl fst₁ i
--   -- snd (CategoryAlt.⋆IdL (FromCategory C) (fst₁ , snd₁) i) = {!!}
--   -- fst (CategoryAlt.⋆IdR (FromCategory C) (fst₁ , snd₁) i) = fst₁
--   -- snd (CategoryAlt.⋆IdR (FromCategory C) (_ , snd₁) i) = ⋆IdR C snd₁ i
--   -- CategoryAlt.⋆Assoc (FromCategory C) {x} f g h =
--   --   ΣPathP (sym (transportRefl (fst h))
--   --     , symP {A = λ i → Hom[_,_] C x (transportRefl (fst h) i)} (toPathP ({!!} ∙ sym (⋆Assoc C (snd f) (snd g) (snd h))))) 
--   -- CategoryAlt.isSetHom (FromCategory C) = {!!}

--   -- record CategoryAlt' ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
--   -- -- no-eta-equality ; NOTE: need eta equality for `opop`
--   --   field
--   --     ob : Type ℓ
--   --     HomF[_] : ob → Type ℓ'
--   --     target : ∀ {x} → HomF[ x ] → ob
--   --     _⋆_  : ∀ {x} (f : HomF[ x ]) (g : HomF[ target f ]) → HomF[ x ]
--   --     ⋆-target : ∀ {x} → (f : HomF[ x ]) → ∀ g → target (f ⋆ g) ≡ target g 
--   --     ⋆Assoc : ∀ {x} (f : HomF[ x ]) (g : HomF[ target f ]) (h : HomF[ target (f ⋆ g) ])
--   --            → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ subst HomF[_] (⋆-target _ _) h)
--   --     isSetHom : ∀ {x} → isSet HomF[ x ]

--   --   ToCategory : Category ℓ (ℓ-max ℓ ℓ')
--   --   Category.ob ToCategory = ob
--   --   Category.Hom[ ToCategory , A ] B = (A ≡ B) ⊎ (Σ HomF[ A ] λ x → target x ≡ B)
--   --   Category.id ToCategory = inl refl
--   --   (ToCategory Category.⋆ inl x) g = {!!}
--   --   (ToCategory Category.⋆ inr x) (inl x₁) = {!!}
--   --   (ToCategory Category.⋆ inr x) (inr x₁) = inr ( fst x ⋆ {!fst x₁!} , {!!})
--   --   Category.⋆IdL ToCategory = {!!}
--   --   Category.⋆IdR ToCategory = {!!}
--   --   Category.⋆Assoc ToCategory = {!!}
--   --   Category.isSetHom ToCategory = {!!}

-- -- open Category

-- -- -- Helpful syntax/notation
-- -- _[_,_] : (C : Category ℓ ℓ') → (x y : C .ob) → Type ℓ'
-- -- _[_,_] = Hom[_,_]

-- -- -- Needed to define this in order to be able to make the subsequence syntax declaration
-- -- seq' : ∀ (C : Category ℓ ℓ') {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → C [ x , z ]
-- -- seq' = _⋆_

-- -- infixl 15 seq'
-- -- syntax seq' C f g = f ⋆⟨ C ⟩ g

-- -- -- composition
-- -- comp' : ∀ (C : Category ℓ ℓ') {x y z} (g : C [ y , z ]) (f : C [ x , y ]) → C [ x , z ]
-- -- comp' = _∘_

-- -- infixr 16 comp'
-- -- syntax comp' C g f = g ∘⟨ C ⟩ f

-- -- -- Isomorphisms and paths in categories
-- -- record CatIso (C : Category ℓ ℓ') (x y : C .ob) : Type ℓ' where
-- --   constructor catiso
-- --   field
-- --     mor : C [ x , y ]
-- --     inv : C [ y , x ]
-- --     sec : inv ⋆⟨ C ⟩ mor ≡ C .id
-- --     ret : mor ⋆⟨ C ⟩ inv ≡ C .id

-- -- pathToIso : {C : Category ℓ ℓ'} {x y : C .ob} (p : x ≡ y) → CatIso C x y
-- -- pathToIso {C = C} p = J (λ z _ → CatIso _ _ z) (catiso idx idx (C .⋆IdL idx) (C .⋆IdL idx)) p
-- --   where
-- --     idx = C .id

-- -- -- Univalent Categories
-- -- record isUnivalent (C : Category ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
-- --   field
-- --     univ : (x y : C .ob) → isEquiv (pathToIso {C = C} {x = x} {y = y})

-- --   -- package up the univalence equivalence
-- --   univEquiv : ∀ (x y : C .ob) → (x ≡ y) ≃ (CatIso _ x y)
-- --   univEquiv x y = pathToIso , univ x y

-- --   -- The function extracting paths from category-theoretic isomorphisms.
-- --   CatIsoToPath : {x y : C .ob} (p : CatIso _ x y) → x ≡ y
-- --   CatIsoToPath {x = x} {y = y} p =
-- --     equivFun (invEquiv (univEquiv x y)) p

-- -- -- Opposite category
-- -- _^op : Category ℓ ℓ' → Category ℓ ℓ'
-- -- ob (C ^op)           = ob C
-- -- Hom[_,_] (C ^op) x y = C [ y , x ]
-- -- id (C ^op)           = id C
-- -- _⋆_ (C ^op) f g      = g ⋆⟨ C ⟩ f
-- -- ⋆IdL (C ^op)         = C .⋆IdR
-- -- ⋆IdR (C ^op)         = C .⋆IdL
-- -- ⋆Assoc (C ^op) f g h = sym (C .⋆Assoc _ _ _)
-- -- isSetHom (C ^op)     = C .isSetHom

