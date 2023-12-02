{-# OPTIONS --safe #-}
module Cubical.Categories.Category.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_ ; uncurry to uc)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport as T
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Implicit
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Path
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Categories.Category.Base

open Category

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} where

  -- isSet where your allowed to compare paths where one side is only
  -- equal up to path. Is there a generalization of this?
  isSetHomP1 : ∀ {x y : C .ob} {n : C [ x , y ]}
              → isOfHLevelDep 1 (λ m → m ≡ n)
  isSetHomP1 {x = x} {y} {n} = isOfHLevel→isOfHLevelDep 1 (λ m → isSetHom C m n)

  -- isSet where the arrows can be between non-definitionally equal obs
  isSetHomP2l : ∀ {y : C .ob}
              → isOfHLevelDep 2 (λ x → C [ x , y ])
  isSetHomP2l = isOfHLevel→isOfHLevelDep 2 (λ a → isSetHom C {x = a})

  isSetHomP2r : ∀ {x : C .ob}
              → isOfHLevelDep 2 (λ y → C [ x , y ])
  isSetHomP2r = isOfHLevel→isOfHLevelDep 2 (λ a → isSetHom C {y = a})


-- opposite of opposite is definitionally equal to itself
involutiveOp : ∀ {C : Category ℓ ℓ'} → C ^op ^op ≡ C
involutiveOp = refl

uaIdEquiv' : {A : Type ℓ} {isEquivIdFunA : isEquiv (idfun A)} →
    ua (idfun A , isEquivIdFunA) ≡ refl
uaIdEquiv' {A = A} {isEquivIdFunA} i j = Glue A {φ = i ∨ ~ j ∨ j}
  (λ _ → A , _ , isPropIsEquiv _ isEquivIdFunA (idIsEquiv A) j)


record CategoryPath (C C' : Category ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

 field
   p : C .ob ≡ C' .ob
   h : PathP (λ i → p i → p i → Type ℓ') (C .Hom[_,_]) (C' .Hom[_,_])
   id≡ : PathP (λ i → {x : p i} → h i x x) (C .id) (C' .id)
   ⋆≡ : PathP (λ i → {x y z : p i} → h i x y → h i y z → h i x z) (C ._⋆_) (C' ._⋆_)


 isSetHom≡ : PathP (λ i → ∀ {x y} → isSet (h i x y))
   (C .isSetHom) (C' .isSetHom)
 isSetHom≡ = isProp→PathP (λ _ → isPropImplicitΠ2 λ _ _ → isPropIsSet) _ _

 mk≡ : C ≡ C'
 ob (mk≡ i) = p i
 Hom[_,_] (mk≡ i) = h i
 id (mk≡ i) = id≡ i
 _⋆_ (mk≡ i) = ⋆≡ i
 ⋆IdL (mk≡ i) =
   isProp→PathP
   (λ i → isPropImplicitΠ2 λ x y → isPropΠ
    λ f → isOfHLevelPath' 1 (isSetHom≡ i {x} {y}) (⋆≡ i (id≡ i) f) f)
    (C .⋆IdL) (C' .⋆IdL) i
 ⋆IdR (mk≡ i) =
   isProp→PathP
   (λ i → isPropImplicitΠ2 λ x y → isPropΠ
    λ f → isOfHLevelPath' 1 (isSetHom≡ i {x} {y}) (⋆≡ i f (id≡ i)) f)
    (C .⋆IdR) (C' .⋆IdR) i
 ⋆Assoc (mk≡ i) =
     isProp→PathP
   (λ i → isPropImplicitΠ4 λ x y z w → isPropΠ3
    λ f f' f'' → isOfHLevelPath' 1 (isSetHom≡ i {x} {w})
     (⋆≡ i (⋆≡ i {x} {y} {z} f f') f'') (⋆≡ i f (⋆≡ i f' f'')))
    (C .⋆Assoc) (C' .⋆Assoc) i
 isSetHom (mk≡ i) = isSetHom≡ i


module _ {C C' : Category ℓ ℓ'} where

 open CategoryPath

 ≡→CategoryPath : C ≡ C' → CategoryPath C C'
 ≡→CategoryPath pa = c
  where
  c : CategoryPath C C'
  p c = cong ob pa
  h c = cong Hom[_,_] pa
  id≡ c = cong id pa
  ⋆≡ c = cong _⋆_ pa
  
 CategoryPathIso : Iso (CategoryPath C C') (C ≡ C')  
 Iso.fun CategoryPathIso = CategoryPath.mk≡
 Iso.inv CategoryPathIso = ≡→CategoryPath 
 Iso.rightInv CategoryPathIso b i j = c 
  where
  cp = ≡→CategoryPath b
  b' = CategoryPath.mk≡ cp
  module _ (j : I) where
    module c' = Category (b j)
  
  c : Category ℓ ℓ'
  ob c = c'.ob j
  Hom[_,_] c = c'.Hom[_,_] j 
  id c = c'.id j
  _⋆_ c = c'._⋆_ j
  ⋆IdL c = isProp→SquareP (λ i j →
      isPropImplicitΠ2 λ x y → isPropΠ λ f →
        (isSetHom≡ cp j {x} {y})
         (c'._⋆_ j (c'.id j) f) f)
      refl refl (λ j → b' j .⋆IdL) (λ j → c'.⋆IdL j) i j
  ⋆IdR c = isProp→SquareP (λ i j →
      isPropImplicitΠ2 λ x y → isPropΠ λ f →
        (isSetHom≡ cp j {x} {y})
         (c'._⋆_ j f (c'.id j)) f)
      refl refl (λ j → b' j .⋆IdR) (λ j → c'.⋆IdR j) i j
  ⋆Assoc c = isProp→SquareP (λ i j →
      isPropImplicitΠ4 λ x y z w → isPropΠ3 λ f g h →
        (isSetHom≡ cp j {x} {w})
         (c'._⋆_ j (c'._⋆_ j {x} {y} {z} f g) h)
         (c'._⋆_ j f (c'._⋆_ j g h)))
      refl refl (λ j → b' j .⋆Assoc) (λ j → c'.⋆Assoc j) i j
  isSetHom c = isProp→SquareP (λ i j →
      isPropImplicitΠ2 λ x y → isPropIsSet {A = c'.Hom[_,_] j x y})
      refl refl (λ j → b' j .isSetHom) (λ j → c'.isSetHom j) i j
 Iso.leftInv CategoryPathIso a = refl

 CategoryPath≡ : {cp cp' : CategoryPath C C'} →
     (p≡ : p cp ≡ p cp') →
     SquareP (λ i j → (p≡ i) j → (p≡ i) j → Type ℓ')
          (h cp) (h cp') (λ _ → C .Hom[_,_]) (λ _ → C' .Hom[_,_])
          → cp ≡ cp'
 p (CategoryPath≡ p≡ _ i) = p≡ i
 h (CategoryPath≡ p≡ h≡ i) = h≡ i
 id≡ (CategoryPath≡ {cp = cp} {cp'} p≡ h≡ i) j {x} =
   isSet→SquareP (λ i j →    
     isProp→PathP (λ i → 
      isPropIsSet {A = (∀ {x} → h≡ i j x x)})
       (isSetImplicitΠ (λ x → isSetHom≡ cp j {x} {x}))
        (isSetImplicitΠ (λ x → isSetHom≡ cp' j {x} {x})) i)
        (id≡ cp) (id≡ cp') (λ _ → C .id) (λ _ → C' .id) i j {x}
 ⋆≡ (CategoryPath≡ {cp = cp} {cp'} p≡ h≡ i) j {x} {y} {z} =
   isSet→SquareP (λ i j →    
     isProp→PathP (λ i → 
      isPropIsSet {A = (∀ {x} {y} {z} →
         h≡ i j x y → h≡ i j y z → h≡ i j x z)})
         (isSetImplicitΠ3 (λ x _ z →
          isSetΠ2 λ _ _ → isSetHom≡ cp j {x} {z}))
         (isSetImplicitΠ3 (λ x _ z →
          isSetΠ2 λ _ _ → isSetHom≡ cp' j {x} {z}))
         i)
        (⋆≡ cp) (⋆≡ cp') (λ _ → C ._⋆_) (λ _ → C' ._⋆_) i j
         {x} {y} {z}
 
  
module _ {C : Category ℓ ℓ'} where
  -- Other useful operations on categories

  -- whisker the parallel morphisms g and g' with f
  lCatWhisker : {x y z : C .ob} (f : C [ x , y ]) (g g' : C [ y , z ]) (p : g ≡ g')
                 → f ⋆⟨ C ⟩ g ≡ f ⋆⟨ C ⟩ g'
  lCatWhisker f _ _ p = cong (_⋆_ C f) p

  rCatWhisker : {x y z : C .ob} (f f' : C [ x , y ]) (g : C [ y , z ]) (p : f ≡ f')
                 → f ⋆⟨ C ⟩ g ≡ f' ⋆⟨ C ⟩ g
  rCatWhisker _ _ g p = cong (λ v → v ⋆⟨ C ⟩ g) p

  -- working with equal objects
  idP : ∀ {x x'} {p : x ≡ x'} → C [ x , x' ]
  idP {x} {x'} {p} = subst (λ v → C [ x , v ]) p (C .id)

  -- heterogeneous seq
  seqP : ∀ {x y y' z} {p : y ≡ y'}
       → (f : C [ x , y ]) (g : C [ y' , z ])
       → C [ x , z ]
  seqP {x} {_} {_} {z} {p} f g = f ⋆⟨ C ⟩ (subst (λ a → C [ a , z ]) (sym p) g)

  -- also heterogeneous seq, but substituting on the left
  seqP' : ∀ {x y y' z} {p : y ≡ y'}
        → (f : C [ x , y ]) (g : C [ y' , z ])
        → C [ x , z ]
  seqP' {x} {_} {_} {z} {p} f g = subst (λ a → C [ x , a ]) p f ⋆⟨ C ⟩ g

  -- show that they're equal
  seqP≡seqP' : ∀ {x y y' z} {p : y ≡ y'}
             → (f : C [ x , y ]) (g : C [ y' , z ])
             → seqP {p = p} f g ≡ seqP' {p = p} f g
  seqP≡seqP' {x = x} {z = z} {p = p} f g i =
    (toPathP {A = λ i' → C [ x , p i' ]} {f} refl i)
      ⋆⟨ C ⟩
    (toPathP {A = λ i' → C [ p (~ i') , z ]} {x = g} (sym refl) (~ i))

  -- seqP is equal to normal seq when y ≡ y'
  seqP≡seq : ∀ {x y z}
           → (f : C [ x , y ]) (g : C [ y , z ])
           → seqP {p = refl} f g ≡ f ⋆⟨ C ⟩ g
  seqP≡seq {y = y} {z} f g i = f ⋆⟨ C ⟩ toPathP {A = λ _ → C [ y , z ]} {x = g} refl (~ i)


  -- whiskering with heterogenous seq -- (maybe should let z be heterogeneous too)
  lCatWhiskerP : {x y z y' : C .ob} {p : y ≡ y'}
                  → (f : C [ x , y ]) (g : C [ y , z ]) (g' : C [ y' , z ])
                  → (r : PathP (λ i → C [ p i , z ]) g g')
                  → f ⋆⟨ C ⟩ g ≡ seqP {p = p} f g'
  lCatWhiskerP {z = z} {p = p} f g g' r =
    cong (λ v → f ⋆⟨ C ⟩ v) (sym (fromPathP (symP {A = λ i → C [ p (~ i) , z ]} r)))

  rCatWhiskerP : {x y' y z : C .ob} {p : y' ≡ y}
                  → (f' : C [ x , y' ]) (f : C [ x , y ]) (g : C [ y , z ])
                  → (r : PathP (λ i → C [ x , p i ]) f' f)
                  → f ⋆⟨ C ⟩ g ≡ seqP' {p = p} f' g
  rCatWhiskerP f' f g r = cong (λ v → v ⋆⟨ C ⟩ g) (sym (fromPathP r))


  AssocCong₂⋆L : {x y' y z w : C .ob} →
          {f' : C [ x , y' ]} {f : C [ x , y ]}
          {g' : C [ y' , z ]} {g : C [ y , z ]}
          → f ⋆⟨ C ⟩ g ≡ f' ⋆⟨ C ⟩ g' → (h : C [ z , w ])
          → f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ h) ≡
              f' ⋆⟨ C ⟩ (g' ⋆⟨ C ⟩ h)
  AssocCong₂⋆L p h =
    sym (⋆Assoc C _ _ h)
      ∙∙ (λ i → p i ⋆⟨ C ⟩ h) ∙∙
    ⋆Assoc C _ _ h

  AssocCong₂⋆R : {x y z z' w : C .ob} →
          (f : C [ x , y ])
          {g' : C [ y , z' ]} {g : C [ y , z ]}
          {h' : C [ z' , w ]} {h : C [ z , w ]}
          → g ⋆⟨ C ⟩ h ≡ g' ⋆⟨ C ⟩ h'
          → (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ h ≡
              (f ⋆⟨ C ⟩ g') ⋆⟨ C ⟩ h'
  AssocCong₂⋆R f p =
    ⋆Assoc C f _ _
      ∙∙ (λ i → f ⋆⟨ C ⟩ p i) ∙∙
    sym (⋆Assoc C _ _ _)
