{-# OPTIONS --safe #-}

module Cubical.Experiments.ElmMoreMore where

open import Cubical.Foundations.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (ℤ to Int)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ renaming (elim to ⊥-elim ; rec to ⊥-rec)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe as ℙ renaming (Maybe to ℙ ; nothing to ₋₋ ; just to ⌞_) 
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Relation.Nullary
import Cubical.Functions.Logic as L
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Agda.Builtin.String

open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommMonoid.CommMonoidProd
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring

open import Cubical.HITs.PropositionalTruncation as T₁

open import Cubical.Experiments.Elm
open import Cubical.Experiments.ElmMore

open import Cubical.Functions.Embedding



-- ℕPoset : PosetStr ℓ-zero ℕ
-- PosetStr._≤_ ℕPoset = {!!}
-- PosetStr.isPoset ℕPoset = {!!}

-- instance
--  HasPatList : ∀ {A} → {{HasPat A}} → HasPat (List A)
--  HasPatList {A} {{hpA}} = w
--   where
--   module HPA = HasPat hpA
 
--   module PA =  PosetStr ((HPA.patOrd))
 
--   module PAD =  DecPoset ((HPA.patDecPoset))
 
--   ℙA = _ 
 
--   module DℙA = DecPoset {P = ℙA} (DecPosetℙ _ _ (HPA.patDecPoset))
 
  

--   open PosetStr

--   -- open Poset⊎ _ _ (DecPosetℙ _ _ HPA.patDecPoset)
--   --             _ _ (DecPosetℙ _ _ HPB.patDecPoset)

--   -- open DecPoset DP⊎


--   w : HasPat (List A)
--   w = {!!}


module _ (A : Type) {{hp : HasPat A }} where

 open HasPat hp

 open DecPoset (DecPosetℙ _ _ patDecPoset) 


 data PatChain : Type₀

 patChainTail : PatChain → (ℙ Pat) → DecProp ℓ-zero
 patChainTail' : PatChain → (ℙ Pat) → DecProp ℓ-zero


 data PatChain where
  [] : PatChain
  _∷p[_,_] : (pc : PatChain) → (p : ℙ Pat) → (True (snd (patChainTail' pc p)))    → PatChain

 patChainTail [] y = ((Unit , isPropUnit) , yes _)
 patChainTail (xs ∷p[ x , p ]) y =
   DecProp⊓ (patChainTail xs y) (¬DecProp (y ≤ᵈ x)) 

 
 
 patChainCompltₚ : PatChain → hProp ℓ-zero 
 patChainCompltₚ pc = L.¬ (L.∃[ x ] (fst (patChainTail pc x)))

 patChainComplt'ₚ : PatChain → hProp ℓ-zero 
 patChainComplt'ₚ pc = L.¬ (L.∃[ x ] (fst (patChainTail' pc x)))



 -- open AC─ {!pat─!}

 restAC : PatChain → StrAntiChain λ _ → Unit , isPropUnit
 restAC [] = fst (ℙSAC _ _ _ pat─  patSAC)
 restAC (x ∷p[ p , x₁ ]) = AC─.AC─' (─ℙ _ _ _ pat─  patSAC) p (restAC x)

 patChainComplt2 : PatChain → DecProp ℓ-zero 
 patChainComplt2 pc = isEmptySAC _ (restAC pc)


 -- PatsGuard : ∀ {P} → A → StrAntiChain P → DecProp ℓ-zero
 -- PatsGuard _ DecPoset.[] = (Unit , isPropUnit) , yes _
 -- PatsGuard a (x DecPoset.∷ p [ x₁ , x₂ ]s) = (⊥ , isProp⊥) , no λ ()

 -- patChainComplt2→p : ∀ xs x → ⟨ minimal x ⟩ → {!!}
 -- patChainComplt2→p = {!!}
 
 patChainTail' xs p = sc∃Dec _ (¬DecProp ∘ (_≮≯ p)) (restAC xs)


 -- patChainComplt2⇔patChainComplt'ₚ : ∀ pc →
 --   ⟨ fst (patChainComplt2 pc) L.⇔ patChainComplt'ₚ pc ⟩  
 -- patChainComplt2⇔patChainComplt'ₚ [] = (λ x x₁ → x) ,
 --   λ f → f ∣ ₋₋ , ∣ inr (λ x → x ∣ ₋₋  , tt , tt ∣₁) ∣₁ ∣₁

 -- patChainComplt2⇔patChainComplt'ₚ (pc ∷p[ p , x ]) = {!!}


 isInPC : PatChain → ℙ Pat → Type₀
 isInPC [] _ = ⊥
 isInPC (xs ∷p[ p , x₂ ]) x = (isInPC xs x) ⊎ ⟨ x ≤ₚ p ⟩


 isInPC⊔ : ∀ pc p → ⟨ minimal p ⟩ → isInPC pc p  ⊎ ⟨ fst (∈SAC _ p (restAC pc)) ⟩ 
 isInPC⊔ [] p pMin = inr ∣ inr tt ∣₁
 isInPC⊔ (pc ∷p[ p₁ , x ]) p pMin =
  ⊎.rec
     (inl ∘ inl)
     (λ in─ →
        ⊎.rec (inl ∘ inr)
         (inr ∘
           (λ a → AC─.stillIn (─ℙ _ _ _ pat─  patSAC) p₁ (restAC pc) p pMin a in─))
         (p₁ ≮≯ₘ (p , pMin)))
    (isInPC⊔ pc p pMin)
 
 -- toSAC : PatChain → StrAntiChain λ _ → Unit , isPropUnit
 -- toSAC x = {!!}
 
 module _ (B : Type) where

  data Cases : Type₀
  record Case : Type


  

  toChain : Cases → PatChain

  cls' : Case → ℙ Pat

  infixl 30 _؛_

  data Cases where
   _؛_ : ∀ co → (c : Case) → {grd : True (snd (patChainTail' (toChain co) (cls' c)))} → Cases
   of : Cases

  infix 40 _⊢>_

  record Case where
   constructor _⊢>_
   field
    cls : ℙ Pat
    bod : patData' cls → B

   evalCase : ∀ a → ⟨ (⌞ toPat a) ≤ₚ cls ⟩ → B
   evalCase a x = bod (fst (patData'Equiv cls) (a , x) )

  cls' = Case.cls

  toChain ((x ؛ x₁) {grd}) = toChain x ∷p[ cls' x₁ , grd ]
  toChain ؛؛_ = []


  evalChainStep' : ∀ a cs → (isInPC (toChain cs) (⌞ (toPat a))) →
    B
  evalChainStep' a (cs ؛ c) (inl x) =  evalChainStep' a cs x
  evalChainStep' a (cs ؛ c) (inr x) = Case.evalCase c a x

  evalChainStep : ∀ a cs → B ⊎ ⟨ fst (∈SAC _ (⌞ (toPat a)) (restAC (toChain cs))) ⟩ 
  evalChainStep a cs =
    ⊎.map (evalChainStep' a cs) (idfun _)
      (isInPC⊔ (toChain cs) (⌞ (toPat a)) w)
   where
    w : ⟨ minimal (⌞ toPat a) ⟩
    w (⌞_ x) = (toPatMin a) x

  record CaseOf : Type₀ where
   constructor co
   field
    cases : Cases
    {compl} : ⟨ fst (patChainComplt2 (toChain cases)) ⟩ 


   eval : A → B
   eval a = ⊎.rec (idfun _)
     (⊥-rec ∘ λ a₁ → ¬-∈SAC-∅ _ _ (restAC (toChain cases)) (compl , a₁))
      (evalChainStep a cases)


hasPatFrom≃ : ∀ {A B} → {{_ : HasPat A}} → B ≃ A → HasPat B
hasPatFrom≃ {{hasPatA}} e = w
 where
 open HasPat

 module w' = HasPat hasPatA 

 w : HasPat _
 Pat w = w'.Pat
 patData w = w'.patData
 patOrd w = w'.patOrd
 patDecPoset w = w'.patDecPoset
 pat─ w = w'.pat─
 patSAC w = w'.patSAC
 toPat w = w'.toPat ∘ fst e
 toPatMin w = w'.toPatMin ∘ fst e
 patDataEquiv w p =
   Σ-cong-equiv-fst e ∙ₑ w'.patDataEquiv p


hasPatAtom : ∀ A → HasPat A
hasPatAtom A = w
 where
 open HasPat

 w : HasPat A
 Pat w = Unit
 patData w x = A
 PosetStr._≤_ (patOrd w) = λ x x₁ → Unit
 IsPoset.is-set (PosetStr.isPoset (patOrd w)) = isSetUnit
 IsPoset.is-prop-valued (PosetStr.isPoset (patOrd w)) _ _ = isPropUnit
 IsPoset.is-refl (PosetStr.isPoset (patOrd w)) = λ a → tt
 IsPoset.is-trans (PosetStr.isPoset (patOrd w)) = λ a b c _ _ → tt
 IsPoset.is-antisym (PosetStr.isPoset (patOrd w)) = λ a b x x₁ i → tt
 DecPoset.patOrdDec (patDecPoset w) = λ x y → yes _
 DecPoset._⊓?_ (patDecPoset w) = λ x y → inl (tt , ((tt , tt) , (λ x₁ _ → tt)))
 fst (pat─ w x y) = DecPoset.[]
 snd (pat─ w x y) = λ x₁ x₂ → snd (fst x₂) ∣ tt , tt , tt ∣₁
 fst (patSAC w) = DecPoset._∷_[_,_]s DecPoset.[] tt tt tt
 snd (patSAC w) x x₁ = snd (snd x₁) ∣ tt , tt , tt ∣₁
 toPat w = λ _ → tt
 toPatMin w = λ a x _ → tt
 patDataEquiv w _ = isoToEquiv rUnit×Iso

instance
 hasPat→ : ∀ {A B} → HasPat (A → B)
 hasPat→ = hasPatAtom _


-- module _ (A B C : _) {{_ : HasPat A}} {{_ : HasPat B}}  {{_ : HasPat C}} where 



--  -- restTest restTest* : {!!}
--  -- restTest = restAC ((A ⊎ A) × (B ⊎ C )) ([] ∷p[ ⌞ ((⌞ inr ₋₋) , (⌞ inr ₋₋)) , tt  ])

 
--  -- restTest* = {!restTest!}

--  funTest : ((A ⊎ A) × (B ⊎ C )) → ℕ
--  funTest = CaseOf.eval
--     (co (of
--      ؛ (⌞ ((⌞ inl ₋₋) , ₋₋)) ⊢> (λ _ → 0)
--      -- ؛ (⌞ ((⌞ inr ₋₋) , ₋₋)) ⊢> {!0!}
--      ؛ (⌞ (₋₋ , (⌞ inr ₋₋))) ⊢> (λ _ → 1)
--      ؛ ₋₋ ⊢> λ _ → 2
--       ))
      
--  -- test' = {!funTest (inr _ , inr _)!} 

--  -- pcTest₁ : PatChain (A × (B ⊎ C ))
--  -- pcTest₁ = {!!}
--  -- ([] ∷p (⌞ (₋₋ , (⌞ inl ₋₋)))) ∷p ((⌞ (₋₋ , ⌞ inr ₋₋)))  
