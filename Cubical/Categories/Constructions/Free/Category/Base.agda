-- Free category over a directed graph, along with (most of) its
-- universal property.

-- This differs from the implementation in Free.Category, which
-- assumes the vertices of the input graph form a Set.
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Free.Category.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.UnderlyingGraph

open import Cubical.Categories.Equivalence.WeakEquivalence

open import Cubical.Categories.Constructions.Free

open import Cubical.HITs.PropositionalTruncation


private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' : Level

open Category
open Functor
open NatIso hiding (sqRL; sqLL)
open NatTrans

module FreeCategory (G : Graph ℓg ℓg') where
    data Exp : G .Node → G .Node → Type (ℓ-max ℓg ℓg') where
      ↑_   : ∀ {A B} → G .Edge A B → Exp A B
      idₑ  : ∀ {A} → Exp A A
      _⋆ₑ_ : ∀ {A B C} → Exp A B → Exp B C → Exp A C
      ⋆ₑIdL : ∀ {A B} (e : Exp A B) → idₑ ⋆ₑ e ≡ e
      ⋆ₑIdR : ∀ {A B} (e : Exp A B) → e ⋆ₑ idₑ ≡ e
      ⋆ₑAssoc : ∀ {A B C D} (e : Exp A B)(f : Exp B C)(g : Exp C D)
              → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
      isSetExp : ∀ {A B} → isSet (Exp A B)

    FreeCat : Category ℓg (ℓ-max ℓg ℓg')
    FreeCat .ob = G .Node
    FreeCat .Hom[_,_] = Exp
    FreeCat .id = idₑ
    FreeCat ._⋆_ = _⋆ₑ_
    FreeCat .⋆IdL = ⋆ₑIdL
    FreeCat .⋆IdR = ⋆ₑIdR
    FreeCat .⋆Assoc = ⋆ₑAssoc
    FreeCat .isSetHom = isSetExp

    η : Interp G FreeCat
    η ._$g_ = λ z → z
    η ._<$g>_ = ↑_

    module _ {ℓc ℓc'} {𝓒 : Category ℓc ℓc'} (F F' : Functor FreeCat 𝓒) where
      -- Formulating uniqueness this way works out best definitionally.

      -- If you prove induction from the alternative below of
      --   sem-uniq : (F ∘Interp η ≡ ı) → F ≡ sem ı
      -- then you have to use path comp which has bad definitional behavior
      module _  (agree-on-η : F ∘Interp η ≡ F' ∘Interp η) where
        private
          aoo : ∀ c → F ⟅ c ⟆ ≡ F' ⟅ c ⟆
          aoo = (λ c i → agree-on-η i $g c)

          aom-t : ∀ {c c'} (e : Exp c c') → Type _
          aom-t {c}{c'} e =
            PathP (λ i → 𝓒 [ aoo c i , aoo c' i ]) (F ⟪ e ⟫) (F' ⟪ e ⟫)

          aom-id : ∀ {c} → aom-t (idₑ {c})
          aom-id = F .F-id ◁ (λ i → 𝓒 .id) ▷ sym (F' .F-id)

          aom-seq : ∀ {c c' c''} (e : Exp c c')(e' : Exp c' c'')
                  → aom-t e → aom-t e' → aom-t (e ⋆ₑ e')
          aom-seq e e' ihe ihe' =
            F .F-seq e e' ◁ (λ i → ihe i ⋆⟨ 𝓒 ⟩ ihe' i) ▷ sym (F' .F-seq e e')

          aom : ∀ {c c'} (e : Exp c c') → aom-t e
          aom (↑ x) = λ i → agree-on-η i <$g> x
          aom idₑ = aom-id
          aom (e ⋆ₑ e') = aom-seq e e' (aom e) (aom e')
          aom (⋆ₑIdL e i) =
            isSet→SquareP
              (λ i j → 𝓒 .isSetHom)
              (aom-seq idₑ e aom-id (aom e))
              (aom e)
              (λ i → F ⟪ ⋆ₑIdL e i ⟫) ((λ i → F' ⟪ ⋆ₑIdL e i ⟫)) i
          aom (⋆ₑIdR e i) =
            isSet→SquareP
            (λ i j → 𝓒 .isSetHom)
            (aom-seq e idₑ (aom e) aom-id)
            (aom e)
            (λ i → F ⟪ ⋆ₑIdR e i ⟫) ((λ i → F' ⟪ ⋆ₑIdR e i ⟫)) i
          aom (⋆ₑAssoc e e' e'' i) =
            isSet→SquareP
            (λ _ _ → 𝓒 .isSetHom)
            (aom-seq _ _ (aom-seq _ _ (aom e) (aom e')) (aom e''))
            (aom-seq _ _ (aom e) (aom-seq _ _ (aom e') (aom e'')))
            ((λ i → F ⟪ ⋆ₑAssoc e e' e'' i ⟫))
            (λ i → F' ⟪ ⋆ₑAssoc e e' e'' i ⟫)
            i
          aom (isSetExp e e' x y i j) =
            isSet→SquareP
            {A = λ i j → aom-t (isSetExp e e' x y i j)}
            (λ i j → isOfHLevelPathP 2 (𝓒 .isSetHom)
                       (F ⟪ isSetExp e e' x y i j ⟫)
                       (F' ⟪ isSetExp e e' x y i j ⟫))
            (λ j → aom (x j))
            (λ j → aom (y j))
            (λ i → aom e)
            (λ i → aom e')
            i
            j
        induction : F ≡ F'
        induction = Functor≡ aoo aom

    module Semantics {ℓc ℓc'}
                     (𝓒 : Category ℓc ℓc')
                     (ı : GraphHom G (Cat→Graph 𝓒)) where
      ⟦_⟧ : ∀ {A B} → Exp A B → 𝓒 [ ı $g A , ı $g B ]
      ⟦ ↑ x ⟧ = ı <$g> x
      ⟦ idₑ ⟧ = 𝓒 .id
      ⟦ e ⋆ₑ e' ⟧ = ⟦ e ⟧ ⋆⟨ 𝓒 ⟩ ⟦ e' ⟧
      ⟦ ⋆ₑIdL e i ⟧ = 𝓒 .⋆IdL ⟦ e ⟧ i
      ⟦ ⋆ₑIdR e i ⟧ = 𝓒 .⋆IdR ⟦ e ⟧ i
      ⟦ ⋆ₑAssoc e e' e'' i ⟧ = 𝓒 .⋆Assoc ⟦ e ⟧ ⟦ e' ⟧ ⟦ e'' ⟧ i
      ⟦ isSetExp e e' p q i j ⟧ =
        𝓒 .isSetHom ⟦ e ⟧ ⟦ e' ⟧ (cong ⟦_⟧ p) (cong ⟦_⟧ q) i j

      sem : Functor FreeCat 𝓒
      sem .Functor.F-ob v = ı $g v
      sem .Functor.F-hom e = ⟦ e ⟧
      sem .Functor.F-id = refl
      sem .Functor.F-seq e e' = refl

      sem-extends-ı : (η ⋆Interp sem) ≡ ı
      sem-extends-ı = refl

      sem-uniq : ∀ {F : Functor FreeCat 𝓒} → ((Functor→GraphHom F ∘GrHom η) ≡ ı) → F ≡ sem
      sem-uniq {F} aog = induction F sem aog

      sem-contr : ∃![ F ∈ Functor FreeCat 𝓒 ] Functor→GraphHom F ∘GrHom η ≡ ı
      sem-contr .fst = sem , sem-extends-ı
      sem-contr .snd (sem' , sem'-extends-ı) = ΣPathP paths
        where
          paths : Σ[ p ∈ sem ≡ sem' ]
                  PathP (λ i → Functor→GraphHom (p i) ∘GrHom η ≡ ı)
                        sem-extends-ı
                        sem'-extends-ı
          paths .fst = sym (sem-uniq sem'-extends-ı)
          paths .snd i j = sem'-extends-ı ((~ i) ∨ j)

    η-expansion : {𝓒 : Category ℓc ℓc'} (F : Functor FreeCat 𝓒)
      → F ≡ Semantics.sem 𝓒 (F ∘Interp η)
    η-expansion {𝓒 = 𝓒} F = induction F (Semantics.sem 𝓒 (F ∘Interp η)) refl

-- co-unit of the 2-adjunction
module _ {𝓒 : Category ℓc ℓc'} where
  open FreeCategory (Cat→Graph 𝓒)
  ε : Functor FreeCat 𝓒
  ε = Semantics.sem 𝓒 (Functor→GraphHom {𝓓 = 𝓒} Id)

  ε-reasoning : {𝓓 : Category ℓd ℓd'}
            → (𝓕 : Functor 𝓒 𝓓)
            → 𝓕 ∘F ε ≡ Semantics.sem 𝓓 (Functor→GraphHom 𝓕)
  ε-reasoning {𝓓 = 𝓓} 𝓕 = Semantics.sem-uniq 𝓓 (Functor→GraphHom 𝓕) refl



-- module Equiv (G : Graph ℓg ℓg') (isSetNode : isSet (Node G))
--           (isSetEdge : ∀ v w → isSet (Edge G v w)) where

--  open FreeCategory G

--  F-h : ∀ {x y} → FreeCategory G isSetNode isSetEdge [ x , y ] →
--                  FreeCat [ x , y ]
--  F-h pnil = idₑ
--  F-h (pcons x xs) = (↑ x) ⋆ₑ F-h xs

--  F-h⁻¹ : ∀ {x y} → FreeCat [ x , y ]
--                   → FreeCategory G isSetNode isSetEdge [ x , y ] 
--  F-h⁻¹ (↑ x) = pcons x pnil 
--  F-h⁻¹ idₑ = pnil
--  F-h⁻¹ (x ⋆ₑ x₁) = F-h⁻¹ x ++ F-h⁻¹ x₁
--  F-h⁻¹ (⋆ₑIdL x i) = F-h⁻¹ x
--  F-h⁻¹ (⋆ₑIdR x i) = ++pnil (F-h⁻¹ x) i
--  F-h⁻¹ (⋆ₑAssoc x x₁ x₂ i) = ++assoc (F-h⁻¹ x) (F-h⁻¹ x₁) (F-h⁻¹ x₂) i
--  F-h⁻¹ (isSetExp x x₁ x₂ y i i₁) = isSetPath isSetNode isSetEdge
--   _ _ (F-h⁻¹ x) (F-h⁻¹ x₁) (cong  F-h⁻¹ x₂) (cong F-h⁻¹ y) i i₁   

--  F-h-seq : ∀ {x y z} → (f : FreeCategory G isSetNode isSetEdge [ x , y ])
--       (g : FreeCategory G isSetNode isSetEdge [ y , z ]) →
--       F-h (seq' (FreeCategory G isSetNode isSetEdge) f g) ≡
--       seq' FreeCat (F-h f) (F-h g)
--  F-h-seq pnil g = sym (⋆ₑIdL _)
--  F-h-seq (pcons x f) g = cong ((↑ x) ⋆ₑ_) (F-h-seq f g) ∙ sym (⋆ₑAssoc _ _ _)

--  FC→FC' : Functor 
--                   (FreeCategory G isSetNode isSetEdge)
--                   (FreeCat)
--  F-ob FC→FC' x = x
--  F-hom FC→FC' = F-h
--  F-id FC→FC' = refl
--  F-seq FC→FC' = F-h-seq

--  open isWeakEquivalence

--  we-f : isWeakEquivalence FC→FC' 
--  fullfaith we-f x y = isoToIsEquiv (iso _ F-h⁻¹ {!!} {!!})
--  esssurj we-f d = ∣ d , idCatIso ∣₁

-- -- isWeakEquivalence
