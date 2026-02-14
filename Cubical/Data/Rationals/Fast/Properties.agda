module Cubical.Data.Rationals.Fast.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws hiding (_⁻¹)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Fast.Int as ℤ using (ℤ; pos·pos; pos0+; pos; negsuc) renaming
  (_+_ to _+ℤ_ ; _·_ to _·ℤ_ ; -_ to -ℤ_ ; abs to ∣_∣ℤ ; sign to sgn)
open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc) renaming
  (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.NatPlusOne hiding (_+₁_)
open import Cubical.Data.Sigma
import Cubical.Data.Bool as 𝟚

open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

open import Cubical.Data.Rationals.Fast.Base

open import Cubical.Data.Nat.GCD
open import Cubical.Data.Nat.Coprime
open import Cubical.Tactics.CommRingSolverFast.IntReflection

∼→sign≡sign : ∀ a a' b b' → (a , b) ∼ (a' , b') → ℤ.sign a ≡ ℤ.sign a'
∼→sign≡sign (ℤ.pos zero)    (ℤ.pos zero)    (1+ _) (1+ _) = λ _ → refl
∼→sign≡sign (ℤ.pos zero)    (ℤ.pos (suc n)) (1+ _) (1+ _) = ⊥.rec ∘ ℕ.znots ∘ ℤ.injPos
∼→sign≡sign (ℤ.pos (suc m)) (ℤ.pos zero)    (1+ _) (1+ _) = ⊥.rec ∘ ℕ.snotz ∘ ℤ.injPos
∼→sign≡sign (ℤ.pos (suc m)) (ℤ.pos (suc n)) (1+ _) (1+ _) = λ _ → refl
∼→sign≡sign (ℤ.pos m)       (ℤ.negsuc n)    (1+ _) (1+ _) = ⊥.rec ∘ ℤ.posNotnegsuc _ _
∼→sign≡sign (ℤ.negsuc m)    (ℤ.pos n)       (1+ _) (1+ _) = ⊥.rec ∘ ℤ.negsucNotpos _ _
∼→sign≡sign (ℤ.negsuc m)    (ℤ.negsuc n)    (1+ _) (1+ _) = λ _ → refl


·CancelL : ∀ {a b} (c : ℕ₊₁) → [ ℕ₊₁→ℤ c ℤ.· a / c ·₊₁ b ] ≡ [ a / b ]
·CancelL {a} {b} c = eq/ _ _ ℤ!

·CancelR : ∀ {a b} (c : ℕ₊₁) → [ a ℤ.· ℕ₊₁→ℤ c / b ·₊₁ c ] ≡ [ a / b ]
·CancelR {a} {b} c = eq/ _ _ ℤ!

module Reduce where
  private
    ℕ[_] = ℕ₊₁→ℕ
    ℤ[_] = ℕ₊₁→ℤ
    +[_] = ℤ.pos

    Cod : ∀ x → Type
    Cod x = Σ[ (p , q) ∈ (ℤ × ℕ₊₁) ] areCoprime (ℤ.abs p , ℕ₊₁→ℕ q) × ([ p / q ] ≡ x)
    isSetValuedCod : ∀ x → isSet (Cod x)
    isSetValuedCod x = isSetΣSndProp
      (isSet× ℤ.isSetℤ (subst isSet 1+Path ℕ.isSetℕ))
      λ _ → isProp× isPropIsGCD (isSetℚ _ _)

    lemma-cop : ∀ {d-1} a c₁ → (c₁ ·ℕ suc d-1 ≡ ∣ a ∣ℤ) → c₁ ≡ ∣ sgn a ·ℤ +[ c₁ ] ∣ℤ
    lemma-cop (pos zero)    zero     _ = refl
    lemma-cop (pos zero)    (suc _)  x = ⊥.rec (ℕ.snotz x)
    lemma-cop (pos (suc n)) c₁       _ = sym $ ℕ.+-zero c₁
    lemma-cop (negsuc n)    zero     _ = refl
    lemma-cop (negsuc n)    (suc c₁) _ = cong suc $ sym $ ℕ.+-zero c₁

  module cop ((a , b) : ℤ × ℕ₊₁) where
    open ToCoprime (∣ a ∣ℤ , b) renaming (toCoprimeAreCoprime to tcac) public

    reduced[] : Cod [ a / b ]
    reduced[] .fst      = sgn a ·ℤ pos c₁ , c₂
    reduced[] .snd .fst = subst (areCoprime ∘ (_, ℕ[ c₂ ]))
                                (lemma-cop a _ (cong (c₁ ·ℕ_) (sym q) ∙ p₁))
                                tcac
    reduced[] .snd .snd = eq/ _ _ $
      sgn a ·ℤ   +[ c₁ ] ·ℤ ℤ[ b ]         ≡⟨ sym $ ℤ.·Assoc (sgn a) _ _ ⟩
      sgn a ·ℤ ( +[ c₁ ] ·ℤ ℤ[ b ])        ≡⟨⟩
      sgn a ·ℤ ( +[ c₁ ·ℕ ℕ[ b ] ])        ≡⟨ cong ((sgn a ·ℤ_) ∘ +[_]) $
                    c₁ ·ℕ ℕ[ b ]           ≡⟨ sym $ cong (c₁ ·ℕ_) p₂ ⟩
                    c₁ ·ℕ (ℕ[ c₂ ] ·ℕ d)   ≡⟨ cong (c₁ ·ℕ_) (ℕ.·-comm ℕ[ c₂ ] d) ⟩
                    c₁ ·ℕ (d ·ℕ ℕ[ c₂ ])   ≡⟨ ℕ.·-assoc c₁ d ℕ[ c₂ ] ⟩
                    c₁ ·ℕ  d ·ℕ ℕ[ c₂ ]    ≡⟨ cong (_·ℕ ℕ[ c₂ ]) p₁ ⟩ refl ⟩
      sgn a ·ℤ ( +[    ∣ a ∣ℤ ·ℕ ℕ[ c₂ ] ]) ≡⟨⟩
      sgn a ·ℤ ( +[  ∣ a ∣ℤ ] ·ℤ ℤ[ c₂ ] )  ≡⟨ ℤ.·Assoc (sgn a) _ _ ⟩
      sgn a ·ℤ   +[  ∣ a ∣ℤ ] ·ℤ ℤ[ c₂ ]    ≡⟨ cong (_·ℤ ℤ[ c₂ ]) (ℤ.sign·abs a) ⟩
                           a ·ℤ ℤ[ c₂ ]    ∎

  reduced[]∼ : ∀ x y r → PathP (λ i → Cod (eq/ x y r i)) (cop.reduced[] x) (cop.reduced[] y)
  reduced[]∼ x@(a , b) y@(a' , b') r = let
    ∣x∣ = (∣ a  ∣ℤ , b)
    ∣y∣ = (∣ a' ∣ℤ , b')

    tc∣x∣≡tc∣y∣ =
      tc ∣x∣                             ≡⟨⟩
      tc (∣ a ∣ℤ , b)                    ≡⟨ sym $ tc-cancelʳ ∣x∣ b' ⟩
      tc (∣ a ∣ℤ ·ℕ ℕ[ b' ] , b ·₊₁ b') ≡⟨ cong (tc ∘ (_, b ·₊₁ b')) $
          ∣ a ∣ℤ ·ℕ ℕ[ b' ]             ≡⟨ sym $ ℤ.abs· a ℤ[ b' ] ⟩
          ∣ a  ·ℤ ℤ[ b' ] ∣ℤ             ≡⟨ cong ∣_∣ℤ r ⟩
          ∣ a' ·ℤ ℤ[ b  ] ∣ℤ             ≡⟨ ℤ.abs· a' ℤ[ b ] ⟩ refl ⟩
      tc (∣ a' ∣ℤ ·ℕ ℕ[ b ] , b ·₊₁ b') ≡⟨ cong (tc ∘ (∣ a' ∣ℤ ·ℕ ℕ[ b ] ,_)) $ ·₊₁-comm b b' ⟩
      tc (∣ a' ∣ℤ ·ℕ ℕ[ b ] , b' ·₊₁ b) ≡⟨ tc-cancelʳ ∣y∣ b ⟩
      tc (∣ a' ∣ℤ , b')                  ≡⟨⟩
      tc ∣y∣                             ∎

    step0 = cong (uncurry (_,_ ∘ (sgn a ·ℤ_) ∘ pos)) tc∣x∣≡tc∣y∣
    step1 = cong ((_, c₂ ∣y∣) ∘ (_·ℤ pos (c₁ ∣y∣))) (∼→sign≡sign a a' b b' r)
    in
      ΣPathPProp (λ _ → isProp× isPropIsGCD (isSetℚ _ _)) $
        sgn a  ·ℤ pos (c₁ ∣x∣) , c₂ ∣x∣ ≡⟨ step0 ⟩
        sgn a  ·ℤ pos (c₁ ∣y∣) , c₂ ∣y∣ ≡⟨ step1 ⟩
        sgn a' ·ℤ pos (c₁ ∣y∣) , c₂ ∣y∣ ∎
    where
      open ToCoprime renaming (toCoprime to tc) ; tc-cancelʳ = toCoprime-cancelʳ

  reduced : ∀ x → Cod x
  reduced = SetQuotient.elim isSetValuedCod cop.reduced[] reduced[]∼

open Reduce public

-- useful functions for defining operations on ℚ

reduce : ℚ → ℚ
reduce = [_] ∘ fst ∘  reduced

record OnCommonDenom : Type where
 no-eta-equality
 field
  g : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
  g-eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
           → ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) ≡ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f))
  g-eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
           → (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d

 eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → [ g (a , b) (e , f) / b ·₊₁ f ] ≡ [ g (c , d) (e , f) / d ·₊₁ f ]
 eql (a , b) (c , d) (e , f) p =
   [ g (a , b) (e , f) / b ·₊₁ f ]
     ≡⟨ sym (·CancelL d) ⟩
   [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / d ·₊₁ (b ·₊₁ f) ]
     ≡[ i ]⟨ [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / ·₊₁-assoc d b f i ] ⟩
   [ ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) / (d ·₊₁ b) ·₊₁ f ]
     ≡[ i ]⟨ [ g-eql (a , b) (c , d) (e , f) p i / ·₊₁-comm d b i ·₊₁ f ] ⟩
   [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / (b ·₊₁ d) ·₊₁ f ]
     ≡[ i ]⟨ [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / ·₊₁-assoc b d f (~ i) ] ⟩
   [ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f)) / b ·₊₁ (d ·₊₁ f) ]
     ≡⟨ ·CancelL b ⟩
   [ g (c , d) (e , f) / d ·₊₁ f ] ∎
 eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
      → [ g (a , b) (c , d) / b ·₊₁ d ] ≡ [ g (a , b) (e , f) / b ·₊₁ f ]
 eqr (a , b) (c , d) (e , f) p =
   [ g (a , b) (c , d) / b ·₊₁ d ]
     ≡⟨ sym (·CancelR f) ⟩
   [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / (b ·₊₁ d) ·₊₁ f ]
     ≡[ i ]⟨ [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / ·₊₁-assoc b d f (~ i) ] ⟩
   [ (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f / b ·₊₁ (d ·₊₁ f) ]
     ≡[ i ]⟨ [ g-eqr (a , b) (c , d) (e , f) p i / b ·₊₁ ·₊₁-comm d f i ] ⟩
   [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / b ·₊₁ (f ·₊₁ d) ]
     ≡[ i ]⟨ [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / ·₊₁-assoc b f d i ] ⟩
   [ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d / (b ·₊₁ f) ·₊₁ d ]
     ≡⟨ ·CancelR d ⟩
   [ g (a , b) (e , f) / b ·₊₁ f ] ∎


 go : ℚ → ℚ → ℚ
 go = SetQuotient.Rec2.go w
  where
  w : SetQuotient.Rec2 ℚ
  w .SetQuotient.Rec2.isSetB = isSetℚ
  w .SetQuotient.Rec2.f (a , b) (c , d) = [ g (a , b) (c , d) / b ·₊₁ d ]
  w .SetQuotient.Rec2.f∼ (a , b) (c , d) (e , f) p = eqr (a , b) (c , d) (e , f) p
  w .SetQuotient.Rec2.∼f (a , b) (c , d) (e , f) p = eql (a , b) (c , d) (e , f) p

record OnCommonDenomSym : Type where
 no-eta-equality
 field
  g : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
  g-sym : ∀ x y → g x y ≡ g y x
  g-eql : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
           → ℕ₊₁→ℤ d ℤ.· (g (a , b) (e , f)) ≡ ℕ₊₁→ℤ b ℤ.· (g (c , d) (e , f))

 q-eqr : ∀ ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : c ℤ.· ℕ₊₁→ℤ f ≡ e ℤ.· ℕ₊₁→ℤ d)
                 → (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡ (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d
 q-eqr (a , b) (c , d) (e , f) p =
           (g (a , b) (c , d)) ℤ.· ℕ₊₁→ℤ f ≡[ i ]⟨ ℤ.·Comm (g-sym (a , b) (c , d) i) (ℕ₊₁→ℤ f) i ⟩
           ℕ₊₁→ℤ f ℤ.· (g (c , d) (a , b)) ≡⟨ g-eql (c , d) (e , f) (a , b) p ⟩
           ℕ₊₁→ℤ d ℤ.· (g (e , f) (a , b)) ≡[ i ]⟨ ℤ.·Comm (ℕ₊₁→ℤ d) (g-sym (e , f) (a , b) i) i ⟩
           (g (a , b) (e , f)) ℤ.· ℕ₊₁→ℤ d ∎

 go : ℚ → ℚ → ℚ
 go = OnCommonDenom.go w
  where
  w : OnCommonDenom
  w .OnCommonDenom.g = g
  w .OnCommonDenom.g-eql = g-eql
  w .OnCommonDenom.g-eqr = q-eqr

 go-comm : ∀ x y → go x y ≡ go y x
 go-comm = SetQuotient.ElimProp2.go w
  where
  w : SetQuotient.ElimProp2 (λ z z₁ → go z z₁ ≡ go z₁ z)
  w .SetQuotient.ElimProp2.isPropB _ _ = isSetℚ _ _
  w .SetQuotient.ElimProp2.f (a , b) (c , d) i = [ g-sym (a , b) (c , d) i / ·₊₁-comm b d i ]


-- basic arithmetic operations on ℚ

infixl 6 _+_
infixl 7 _·_
infix  8 -_

private abstract
  lem₁ : ∀ a b c d e (p : a ℤ.· b ≡ c ℤ.· d) → b ℤ.· (a ℤ.· e) ≡ d ℤ.· (c ℤ.· e)
  lem₁ a b c d e p =   ℤ.·Assoc b a e
                     ∙ cong (ℤ._· e) (ℤ.·Comm b a ∙ p ∙ ℤ.·Comm c d)
                     ∙ sym (ℤ.·Assoc d c e)

  lem₂ : ∀ a b c → a ℤ.· (b ℤ.· c) ≡ c ℤ.· (b ℤ.· a)
  lem₂ a b c =   cong (a ℤ.·_) (ℤ.·Comm b c) ∙ ℤ.·Assoc a c b
               ∙ cong (ℤ._· b) (ℤ.·Comm a c) ∙ sym (ℤ.·Assoc c a b)
               ∙ cong (c ℤ.·_) (ℤ.·Comm a b)

minR : OnCommonDenomSym
minR .OnCommonDenomSym.g (a , b) (c , d) = ℤ.min (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
minR .OnCommonDenomSym.g-sym (a , b) (c , d) = ℤ.minComm (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
minR .OnCommonDenomSym.g-eql = eq

  where abstract

    eq : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → ℕ₊₁→ℤ d ℤ.· ℤ.min (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b)
       ≡ ℕ₊₁→ℤ b ℤ.· ℤ.min (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d)
    eq (a , b) (c , d) (e , f) p =
      ℕ₊₁→ℤ d ℤ.· ℤ.min (a ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ ℤ.·DistPosRMin (ℕ₊₁→ℕ d)
                              (a ℤ.· ℕ₊₁→ℤ f)
                              (e ℤ.· ℕ₊₁→ℤ b) ⟩
      ℤ.min (ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ d ℤ.· (e ℤ.· ℕ₊₁→ℤ b))
            ≡⟨ cong₂ ℤ.min (ℤ.·Assoc (ℕ₊₁→ℤ d) a (ℕ₊₁→ℤ f))
                           (ℤ.·Assoc (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ b)) ⟩
      ℤ.min (ℕ₊₁→ℤ d ℤ.· a ℤ.· ℕ₊₁→ℤ f)
            (ℕ₊₁→ℤ d ℤ.· e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ cong₂ ℤ.min (cong (ℤ._· ℕ₊₁→ℤ f)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) a ∙
                                  p ∙
                                  ℤ.·Comm c (ℕ₊₁→ℤ b)) ∙
                                  sym (ℤ.·Assoc (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ f)))
                           (cong (ℤ._· ℕ₊₁→ℤ b)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) e) ∙
                                 ℤ.·Comm (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ⟩
      ℤ.min (ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ b ℤ.· (e ℤ.· ℕ₊₁→ℤ d))
            ≡⟨ sym (ℤ.·DistPosRMin (ℕ₊₁→ℕ b)
                                   (c ℤ.· ℕ₊₁→ℤ f)
                                   (e ℤ.· ℕ₊₁→ℤ d)) ⟩
      ℕ₊₁→ℤ b ℤ.· ℤ.min (c ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ d) ∎

min = OnCommonDenomSym.go minR

maxR : OnCommonDenomSym
maxR .OnCommonDenomSym.g (a , b) (c , d) = ℤ.max (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
maxR .OnCommonDenomSym.g-sym (a , b) (c , d) = ℤ.maxComm (a ℤ.· ℕ₊₁→ℤ d) (c ℤ.· ℕ₊₁→ℤ b)
maxR .OnCommonDenomSym.g-eql = eq


  where abstract
    eq : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → ℕ₊₁→ℤ d ℤ.· ℤ.max (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b)
       ≡ ℕ₊₁→ℤ b ℤ.· ℤ.max (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d)
    eq (a , b) (c , d) (e , f) p =
      ℕ₊₁→ℤ d ℤ.· ℤ.max (a ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ ℤ.·DistPosRMax (ℕ₊₁→ℕ d)
                              (a ℤ.· ℕ₊₁→ℤ f)
                              (e ℤ.· ℕ₊₁→ℤ b) ⟩
      ℤ.max (ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ d ℤ.· (e ℤ.· ℕ₊₁→ℤ b))
            ≡⟨ cong₂ ℤ.max (ℤ.·Assoc (ℕ₊₁→ℤ d) a (ℕ₊₁→ℤ f))
                           (ℤ.·Assoc (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ b)) ⟩
      ℤ.max (ℕ₊₁→ℤ d ℤ.· a ℤ.· ℕ₊₁→ℤ f)
            (ℕ₊₁→ℤ d ℤ.· e ℤ.· ℕ₊₁→ℤ b)
            ≡⟨ cong₂ ℤ.max (cong (ℤ._· ℕ₊₁→ℤ f)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) a ∙
                                  p ∙
                                  ℤ.·Comm c (ℕ₊₁→ℤ b)) ∙
                                  sym (ℤ.·Assoc (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ f)))
                           (cong (ℤ._· ℕ₊₁→ℤ b)
                                 (ℤ.·Comm (ℕ₊₁→ℤ d) e) ∙
                                 ℤ.·Comm (e ℤ.· ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ⟩
      ℤ.max (ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f))
            (ℕ₊₁→ℤ b ℤ.· (e ℤ.· ℕ₊₁→ℤ d))
            ≡⟨ sym (ℤ.·DistPosRMax (ℕ₊₁→ℕ b)
                                   (c ℤ.· ℕ₊₁→ℤ f)
                                   (e ℤ.· ℕ₊₁→ℤ d)) ⟩
      ℕ₊₁→ℤ b ℤ.· ℤ.max (c ℤ.· ℕ₊₁→ℤ f)
                         (e ℤ.· ℕ₊₁→ℤ d) ∎

max = OnCommonDenomSym.go maxR


minComm : ∀ x y → min x y ≡ min y x
minComm = OnCommonDenomSym.go-comm minR

maxComm : ∀ x y → max x y ≡ max y x
maxComm = OnCommonDenomSym.go-comm maxR

minIdem : ∀ x → min x x ≡ x
minIdem = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) → eq/ (ℤ.min (a ℤ.· ℕ₊₁→ℤ b) (a ℤ.· ℕ₊₁→ℤ b) , b ·₊₁ b) (a , b)
                    (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.minIdem (a ℤ.· ℕ₊₁→ℤ b)) ∙
                     sym (ℤ.·Assoc a (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ b)) ∙
                     cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ b)))) }

maxIdem : ∀ x → max x x ≡ x
maxIdem = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) → eq/ (ℤ.max (a ℤ.· ℕ₊₁→ℤ b) (a ℤ.· ℕ₊₁→ℤ b) , b ·₊₁ b) (a , b)
                    (cong (ℤ._· ℕ₊₁→ℤ b) (ℤ.maxIdem (a ℤ.· ℕ₊₁→ℤ b)) ∙
                     sym (ℤ.·Assoc a (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ b)) ∙
                     cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ b)))) }

minAssoc : ∀ x y z → min x (min y z) ≡ min (min x y) z
minAssoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d) (e , f) i
    → [ (cong₂ ℤ.min
               (cong (a ℤ.·_) (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))
               ∙ ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
               (ℤ.·DistPosLMin (c ℤ.· ℕ₊₁→ℤ f)
                               (e ℤ.· ℕ₊₁→ℤ d)
                               (ℕ₊₁→ℕ b)
               ∙ cong₂ ℤ.min (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                             (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                             ∙ cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)
                                             ∙ sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))))
        ∙ ℤ.minAssoc (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f)
                     (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ f)
                     (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
        ∙ cong (λ x → ℤ.min x (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)))
               (sym (ℤ.·DistPosLMin (a ℤ.· ℕ₊₁→ℤ d)
                                    (c ℤ.· ℕ₊₁→ℤ b)
                                    (ℕ₊₁→ℕ f)))) i / ·₊₁-assoc b d f i ] }

maxAssoc : ∀ x y z → max x (max y z) ≡ max (max x y) z
maxAssoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d) (e , f) i
    → [ (cong₂ ℤ.max
               (cong (a ℤ.·_) (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ f))
               ∙ ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ f))
               (ℤ.·DistPosLMax (c ℤ.· ℕ₊₁→ℤ f)
                               (e ℤ.· ℕ₊₁→ℤ d)
                               (ℕ₊₁→ℕ b)
               ∙ cong₂ ℤ.max (sym (ℤ.·Assoc c (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ cong (c ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ f) (ℕ₊₁→ℤ b))
                             ∙ ℤ.·Assoc c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f))
                             (sym (ℤ.·Assoc e (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b))
                             ∙ cong (e ℤ.·_) (ℤ.·Comm (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)
                                             ∙ sym (pos·pos (ℕ₊₁→ℕ b) (ℕ₊₁→ℕ d)))))
        ∙ ℤ.maxAssoc (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ f)
                     (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ f)
                     (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
        ∙ cong (λ x → ℤ.max x (e ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)))
               (sym (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ d)
                                    (c ℤ.· ℕ₊₁→ℤ b)
                                    (ℕ₊₁→ℕ f)))) i / ·₊₁-assoc b d f i ] }

minAbsorbLMax : ∀ x y → min x (max x y) ≡ x
minAbsorbLMax = SetQuotient.elimProp2 (λ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d)
    → eq/ (ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.max (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
           ℤ.· ℕ₊₁→ℤ b) ,
           b ·₊₁ (b ·₊₁ d))
          (a , b)
          (ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.max (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
                         ℤ.· ℕ₊₁→ℤ b)
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) x
                                  ℤ.· ℕ₊₁→ℤ b)
                                (ℤ.·DistPosLMax (a ℤ.· ℕ₊₁→ℤ d) _ (ℕ₊₁→ℕ b)) ⟩
           ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
          (ℤ.max (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ b)
                 (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                                (ℤ.max x (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
                                 ℤ.· ℕ₊₁→ℤ b)
                                (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                 cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                cong ℕ₊₁→ℤ (·₊₁-comm d b))) ⟩
           ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
          (ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b)
                                (ℤ.minAbsorbLMax (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) _) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d) ℤ.· ℕ₊₁→ℤ b
                 ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ (b ·₊₁ d)) (ℕ₊₁→ℤ b)) ∙
                    cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ (b ·₊₁ d)) (ℕ₊₁→ℕ b)) ∙
                                   cong ℕ₊₁→ℤ (·₊₁-comm (b ·₊₁ d) b)) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ (b ·₊₁ d)) ∎) }

maxAbsorbLMin : ∀ x y → max x (min x y) ≡ x
maxAbsorbLMin = SetQuotient.elimProp2 (λ _ _ → isSetℚ _ _)
  λ { (a , b) (c , d)
    → eq/ (ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
                  ℤ.· ℕ₊₁→ℤ b) ,
                  b ·₊₁ (b ·₊₁ d))
                 (a , b)
          (ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ d)
                        (c ℤ.· ℕ₊₁→ℤ b)
                  ℤ.· ℕ₊₁→ℤ b)
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) x
                                  ℤ.· ℕ₊₁→ℤ b)
                                (ℤ.·DistPosLMin (a ℤ.· ℕ₊₁→ℤ d) _ (ℕ₊₁→ℕ b)) ⟩
           ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ d ℤ.· ℕ₊₁→ℤ b)
                        (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (λ x → ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                                             (ℤ.min x (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
                                       ℤ.· ℕ₊₁→ℤ b)
                                (sym (ℤ.·Assoc a (ℕ₊₁→ℤ d) (ℕ₊₁→ℤ b)) ∙
                                 cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ d) (ℕ₊₁→ℕ b)) ∙
                                                cong ℕ₊₁→ℤ (·₊₁-comm d b))) ⟩
           ℤ.max (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                 (ℤ.min (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d))
                        (c ℤ.· ℕ₊₁→ℤ b ℤ.· ℕ₊₁→ℤ b))
           ℤ.· ℕ₊₁→ℤ b ≡⟨ cong (ℤ._· ℕ₊₁→ℤ b)
                                (ℤ.maxAbsorbLMin (a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d)) _) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ d) ℤ.· ℕ₊₁→ℤ b
             ≡⟨ sym (ℤ.·Assoc a (ℕ₊₁→ℤ (b ·₊₁ d)) (ℕ₊₁→ℤ b)) ∙
                cong (a ℤ.·_) (sym (pos·pos (ℕ₊₁→ℕ (b ·₊₁ d)) (ℕ₊₁→ℕ b)) ∙
                               cong ℕ₊₁→ℤ (·₊₁-comm (b ·₊₁ d) b)) ⟩
           a ℤ.· ℕ₊₁→ℤ (b ·₊₁ (b ·₊₁ d)) ∎) }

+Rec : OnCommonDenomSym
+Rec .OnCommonDenomSym.g (a , b) (c , d) = a ℤ.· (ℕ₊₁→ℤ d) ℤ.+ c ℤ.· (ℕ₊₁→ℤ b)
+Rec .OnCommonDenomSym.g-sym (a , b) (c , d) = ℤ.+Comm (a ℤ.· (ℕ₊₁→ℤ d)) (c ℤ.· (ℕ₊₁→ℤ b))
+Rec .OnCommonDenomSym.g-eql = eq
  where abstract
    eq : ((a , b) (c , d) (e , f) : ℤ × ℕ₊₁) (p : a ℤ.· ℕ₊₁→ℤ d ≡ c ℤ.· ℕ₊₁→ℤ b)
       → ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ b)
       ≡ ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d)
    eq (a , b) (c , d) (e , f) p =
      ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ b)
        ≡⟨ ℤ.·DistR+ (ℕ₊₁→ℤ d) (a ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ b) ⟩
      ℕ₊₁→ℤ d ℤ.· (a ℤ.· ℕ₊₁→ℤ f) ℤ.+ ℕ₊₁→ℤ d ℤ.· (e ℤ.· ℕ₊₁→ℤ b)
        ≡[ i ]⟨ lem₁ a (ℕ₊₁→ℤ d) c (ℕ₊₁→ℤ b) (ℕ₊₁→ℤ f) p i ℤ.+ lem₂ (ℕ₊₁→ℤ d) e (ℕ₊₁→ℤ b) i ⟩
      ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f) ℤ.+ ℕ₊₁→ℤ b ℤ.· (e ℤ.· ℕ₊₁→ℤ d)
        ≡⟨ sym (ℤ.·DistR+ (ℕ₊₁→ℤ b) (c ℤ.· ℕ₊₁→ℤ f) (e ℤ.· ℕ₊₁→ℤ d)) ⟩
      ℕ₊₁→ℤ b ℤ.· (c ℤ.· ℕ₊₁→ℤ f ℤ.+ e ℤ.· ℕ₊₁→ℤ d) ∎

_impl+_ : ℚ → ℚ → ℚ
_impl+_ = OnCommonDenomSym.go +Rec

_+_ : ℚ → ℚ → ℚ
[ a ] + [ a₁ ] = [ a ] impl+ [ a₁ ]
[ a ] + eq/ a₁ b r i = [ a ] impl+ (eq/ a₁ b r i)
[ a ] + _//_.squash/ x₁ x₂ p q i i₁ =
  isSetℚ ([ a ] + x₁) ([ a ] + x₂) (λ i₁ → [ a ] + p i₁) (λ i₁ → [ a ] + q i₁)  i i₁
eq/ a b r i + [ a₁ ] = (eq/ a b r i) impl+ [ a₁ ]
eq/ a b r i + eq/ a₁ b₁ r₁ i₁ =
 isSet→isSet' isSetℚ
   (λ i₁ → [ a ] impl+ eq/ a₁ b₁ r₁ i₁) (λ i₁ → [ b ] impl+ eq/ a₁ b₁ r₁ i₁)
   (λ i → eq/ a b r i impl+ [ a₁ ]) (λ i → eq/ a b r i impl+ [ b₁ ]) i i₁
eq/ a b r i + _//_.squash/ x₁ x₂ p q i₁ i₂ =
  isGroupoid→isGroupoid' (isSet→isGroupoid isSetℚ)
    (λ i₁ i₂ → isSetℚ ([ a ] + x₁) ([ a ] + x₂) (λ i₃ → [ a ] + p i₃) (λ i₃ → [ a ] + q i₃) i₁ i₂)
    (λ i₁ i₂ → isSetℚ ([ b ] + x₁) ([ b ] + x₂) (λ i₃ → [ b ] + p i₃) (λ i₃ → [ b ] + q i₃) i₁ i₂)
    (λ i i₂ → eq/ a b r i + p i₂) (λ i i₂ → eq/ a b r i + q i₂)
    (λ i i₁ → eq/ a b r i + x₁) (λ i i₁ → eq/ a b r i + x₂)
    i i₁ i₂
_//_.squash/ x x₁ p q i i₁ + z =
  isSetℚ (x + z) (x₁ + z) (cong (_+ z) p) (cong (_+ z) q) i i₁

+-impl : ∀ x y → x + y ≡ x impl+ y
+-impl = SetQuotient.ElimProp2.go w
 where
 w : SetQuotient.ElimProp2 (λ z z₁ → z + z₁ ≡ (z impl+ z₁))
 w .SetQuotient.ElimProp2.isPropB _ _ = isSetℚ _ _
 w .SetQuotient.ElimProp2.f _ _ = refl

+Comm : ∀ x y → x + y ≡ y + x
+Comm x y = +-impl x y ∙∙ OnCommonDenomSym.go-comm +Rec x y ∙∙ sym (+-impl y x)

+IdL : ∀ x → 0 + x ≡ x
+IdL = SetQuotient.elimProp (λ _ → isSetℚ _ _)
  λ { (a , b) i → [ ((cong (ℤ._+ a ℤ.· ℕ₊₁→ℤ 1) (ℤ.·AnnihilL (ℕ₊₁→ℤ b))
                    ∙ sym (pos0+ (a ℤ.· ℕ₊₁→ℤ 1)))
                    ∙ ℤ.·IdR a) i / ·₊₁-identityˡ b i ] }

+IdR : ∀ x → x + 0 ≡ x
+IdR x = +Comm x _ ∙ +IdL x

+Assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+Assoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _) (λ  _ _ _ → eq/ _ _ ℤ!)

·Rec : OnCommonDenomSym
·Rec .OnCommonDenomSym.g (a , _) (c , _) = a ℤ.· c
·Rec .OnCommonDenomSym.g-sym (a , _) (c , _) = ℤ.·Comm a c
·Rec .OnCommonDenomSym.g-eql (a , b) (c , d) (e , _) p = lem₁ a (ℕ₊₁→ℤ d) c (ℕ₊₁→ℤ b) e p

_impl·_ : ℚ → ℚ → ℚ
_impl·_ = OnCommonDenomSym.go ·Rec

_·_ : ℚ → ℚ → ℚ
[ a ] · [ a₁ ] = [ a ] impl· [ a₁ ]
[ a ] · eq/ a₁ b r i = [ a ] impl· (eq/ a₁ b r i)
[ a ] · _//_.squash/ x₁ x₂ p q i i₁ =
  isSetℚ ([ a ] · x₁) ([ a ] · x₂) (λ i₁ → [ a ] · p i₁) (λ i₁ → [ a ] · q i₁)  i i₁
eq/ a b r i · [ a₁ ] = (eq/ a b r i) impl· [ a₁ ]
eq/ a b r i · eq/ a₁ b₁ r₁ i₁ =
 isSet→isSet' isSetℚ
   (λ i₁ → [ a ] impl· eq/ a₁ b₁ r₁ i₁) (λ i₁ → [ b ] impl· eq/ a₁ b₁ r₁ i₁)
   (λ i → eq/ a b r i impl· [ a₁ ]) (λ i → eq/ a b r i impl· [ b₁ ]) i i₁
eq/ a b r i · _//_.squash/ x₁ x₂ p q i₁ i₂ =
  isGroupoid→isGroupoid' (isSet→isGroupoid isSetℚ)
    (λ i₁ i₂ → isSetℚ ([ a ] · x₁) ([ a ] · x₂) (λ i₃ → [ a ] · p i₃) (λ i₃ → [ a ] · q i₃) i₁ i₂)
    (λ i₁ i₂ → isSetℚ ([ b ] · x₁) ([ b ] · x₂) (λ i₃ → [ b ] · p i₃) (λ i₃ → [ b ] · q i₃) i₁ i₂)
    (λ i i₂ → eq/ a b r i · p i₂) (λ i i₂ → eq/ a b r i · q i₂)
    (λ i i₁ → eq/ a b r i · x₁) (λ i i₁ → eq/ a b r i · x₂)
    i i₁ i₂
_//_.squash/ x x₁ p q i i₁ · z =
  isSetℚ (x · z) (x₁ · z) (cong (_· z) p) (cong (_· z) q) i i₁

·-impl : ∀ x y → x · y ≡ x impl· y
·-impl = SetQuotient.ElimProp2.go w
 where
 w : SetQuotient.ElimProp2 (λ z z₁ → z · z₁ ≡ (z impl· z₁))
 w .SetQuotient.ElimProp2.isPropB _ _ = isSetℚ _ _
 w .SetQuotient.ElimProp2.f _ _ = refl

·Comm : ∀ x y → x · y ≡ y · x
·Comm x y = ·-impl x y ∙∙ OnCommonDenomSym.go-comm ·Rec x y ∙∙ sym (·-impl y x)


·IdL : ∀ x → 1 · x ≡ x
·IdL = SetQuotient.elimProp (λ _ → isSetℚ _ _) λ (_ , _) → eq/ _ _ ℤ!

·IdR : ∀ x → x · 1 ≡ x
·IdR = SetQuotient.elimProp (λ _ → isSetℚ _ _) λ (_ , _) → eq/ _ _ ℤ!

·AnnihilL : ∀ x → 0 · x ≡ 0
·AnnihilL = SetQuotient.elimProp (λ _ → isSetℚ _ _) λ (_ , _) → eq/ _ _ ℤ!

·AnnihilR : ∀ x → x · 0 ≡ 0
·AnnihilR = SetQuotient.elimProp (λ _ → isSetℚ _ _) λ (_ , _) → eq/ _ _ ℤ!

·Assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
·Assoc = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _) (λ  _ _ _ → eq/ _ _ ℤ!)

·DistL+ : ∀ x y z → x · (y + z) ≡ (x · y) + (x · z)
·DistL+ = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _) (λ  _ _ _ → eq/ _ _ ℤ!)

·DistR+ : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
·DistR+ = SetQuotient.elimProp3 (λ _ _ _ → isSetℚ _ _) (λ  _ _ _ → eq/ _ _ ℤ!)


[/]≡· : ∀ n m → [ n / m ] ≡ [ n / 1 ] · [ 1 / m ]
[/]≡· n m = cong₂ [_/_] (sym (ℤ.·IdR n)) (sym (·₊₁-identityˡ _))

[1/n]·[1/m]≡[1/n·m] : ∀ n m → [ 1 / n ] · [ 1 / m ] ≡ [ 1 / n ·₊₁ m ]
[1/n]·[1/m]≡[1/n·m] n m = eq/ _ _ refl


[n/n]≡[m/m] : ∀ n m → [ ℤ.pos (suc n) / 1+ n ] ≡ [ ℤ.pos (suc m) / 1+ m ]
[n/n]≡[m/m] n m = eq/ _ _ (ℤ.·Comm (ℤ.pos (suc n)) (ℤ.pos (suc m)))

[0/n]≡[0/m] : ∀ n m → [ ℤ.pos zero / 1+ n ] ≡ [ ℤ.pos zero / 1+ m ]
[0/n]≡[0/m] n m = eq/ _ _ refl


-_ : ℚ → ℚ
- x = -1 · x

-[/] : ∀ n m → [ ℤ.negsuc m / n ] ≡ - [ ℤ.pos (suc m) / n ]
-[/] n m = cong₂ [_/_] (sym (ℤ.-1·x≡-x _)) (sym (·₊₁-identityˡ _))


-Invol : ∀ x → - - x ≡ x
-Invol x = ·Assoc -1 -1 x ∙ ·IdL x

-Distr : ∀ x y → - (x + y) ≡ - x + - y
-Distr = ·DistL+ -1

negateEquiv : ℚ ≃ ℚ
negateEquiv = isoToEquiv (iso -_ -_ -Invol -Invol)

negateEq : ℚ ≡ ℚ
negateEq = ua negateEquiv

+InvL : ∀ x → (- x) + x ≡ 0
+InvL x = (λ i → (-1 · x) + ·IdL x (~ i)) ∙ (sym (·DistR+ -1 1 x)) ∙ ·AnnihilL x

_-_ : ℚ → ℚ → ℚ
x - y = x + (- y)


-·- : ∀ x y → (- x) · (- y) ≡ x · y
-·- x y = cong (_· (- y)) (·Comm -1 x)
            ∙∙ sym (·Assoc x (- 1) _)
            ∙∙ cong (x ·_) (-Invol y)

-[x-y]≡y-x : ∀ x y → - ( x - y ) ≡ y - x
-[x-y]≡y-x x y = -Distr x (- y) ∙ λ i → +Comm (- x) (-Invol y i) i

-Distr' : ∀ x y → - (x - y) ≡ (- x) + y
-Distr' x y = -[x-y]≡y-x x y ∙ +Comm y (- x)


+InvR : ∀ x → x - x ≡ 0
+InvR x = +Comm x (- x) ∙ +InvL x

+CancelL : ∀ x y z → x + y ≡ x + z → y ≡ z
+CancelL x y z p = sym (q y) ∙ cong ((- x) +_) p ∙ q z
  where q : ∀ y → (- x) + (x + y) ≡ y
        q y = +Assoc (- x) x y ∙ cong (_+ y) (+InvL x) ∙ +IdL y

+CancelR : ∀ x y z → x + y ≡ z + y → x ≡ z
+CancelR x y z p = +CancelL y x z (+Comm y x ∙ p ∙ +Comm z y)

+CancelL- : ∀ x y z → x + y ≡ z → x ≡ z - y
+CancelL- x y z p = (sym (+IdR x)  ∙ cong (x +_) (sym (+InvR y)))
  ∙∙  (+Assoc x y (- y)) ∙∙ cong (_- y) p

abs : ℚ → ℚ
abs x = max x (- x)

abs' : ℚ → ℚ
abs' = SetQuotient.Rec.go w
 where
 w : SetQuotient.Rec ℚ
 w .SetQuotient.Rec.isSetB = isSetℚ
 w .SetQuotient.Rec.f (a , b) = [ ℤ.pos (ℤ.abs a) , b ]
 w .SetQuotient.Rec.f∼ (a , 1+ b) (a' , 1+ b') r = eq/ _ _
   ((sym (ℤ.pos·pos (ℤ.abs a) (suc b')) ∙
      cong ℤ.pos (sym (ℤ.abs· (a) (ℕ₊₁→ℤ (1+ b'))) ))
     ∙∙ cong (λ x → ℤ.pos (ℤ.abs x)) r
     ∙∙ sym ((sym (ℤ.pos·pos (ℤ.abs a') (suc b)) ∙
      cong ℤ.pos (sym (ℤ.abs· (a') (ℕ₊₁→ℤ (1+ b))) ))))

abs'≡abs : ∀ x → abs x ≡ abs' x
abs'≡abs = SetQuotient.ElimProp.go λ where
  .SetQuotient.ElimProp.isPropB _ → isSetℚ _ _
  .SetQuotient.ElimProp.f (a , b) →
    abs [ a / b ]
                            ≡⟨⟩
    max [ a / b ] [ -1 ·ℤ a / 1 ·₊₁ b ]
                            ≡[ i ]⟨ max [ a / b ] [ ℤ.-1·x≡-x a i / ·₊₁-identityˡ b i ] ⟩
    max [ a / b ] [ -ℤ a / b ]
                            ≡⟨⟩
    [ ℤ.max (a ·ℤ ℕ₊₁→ℤ b) (-ℤ a ·ℤ ℕ₊₁→ℤ b) / b ·₊₁ b ]
                            ≡⟨ sym $ cong [_/ _ ] (ℤ.·DistPosLMax a (-ℤ a) (ℕ₊₁→ℕ b)) ⟩
    [ ℤ.max a (-ℤ a) ·ℤ (ℕ₊₁→ℤ b) / b ·₊₁ b ]
                            ≡⟨ ·CancelR b ⟩
    [ ℤ.max a (-ℤ a) / b ]
                            ≡⟨ sym $ cong [_/ b ] (ℤ.abs-max a) ⟩
    [ pos ∣ a ∣ℤ / b ]
                            ≡⟨⟩
    abs' [ a / b ]
                            ∎


ℤ+→ℚ+ : ∀ m n → [ m / 1 ] + [ n / 1 ] ≡ [ m ℤ.+ n / 1 ]
ℤ+→ℚ+ m n = cong [_/ 1 ] (cong₂ ℤ._+_ (ℤ.·IdR m) (ℤ.·IdR n))

ℤ-→ℚ- : ∀ m n → [ m / 1 ] - [ n / 1 ] ≡ [ m ℤ.- n / 1 ]
ℤ-→ℚ- m n = cong [_/ 1 ]
  (cong₂
    ℤ._+_ (ℤ.·IdR m)
    (cong (_·ℤ _) (ℤ.-1·x≡-x n) ∙ ℤ.·IdR (ℤ.- n)))

ℕ+→ℚ+ : ∀ m n → fromNat m + fromNat n ≡ fromNat (m ℕ.+ n)
ℕ+→ℚ+ m n = ℤ+→ℚ+ (ℤ.pos m) (ℤ.pos n) ∙ cong [_/ 1 ] (sym (ℤ.pos+ m n))

ℕ·→ℚ· : ∀ m n → fromNat m · fromNat n ≡ fromNat (m ℕ.· n)
ℕ·→ℚ· m n = cong [_/ 1 ] (sym (ℤ.pos·pos m n))


x+x≡2x : ∀ x → x + x ≡ 2 · x
x+x≡2x x = cong₂ _+_
    (sym (·IdL x))
    (sym (·IdL x))
    ∙ sym (·DistR+ 1 1 x)


-- eqElimTy : (lrhs : ℚ → ℚ × ℚ) → Type
-- eqElimTy lrhs = (∀ {k m} → fst (lrhs ([ (k , 1+ m) ]))
--         ≡  snd (lrhs ([ (k , 1+ m) ])))
-- eqElim₂Ty : (lrhs : ℚ → ℚ → ℚ × ℚ) → Type
-- eqElim₂Ty lrhs = (∀ {k m k' m'} → fst (lrhs [ (k , 1+ m) ] [ (k' , 1+ m') ])
--         ≡  snd (lrhs [ (k , 1+ m) ] [ (k' , 1+ m') ]))

-- eqElim₃Ty : (lrhs : ℚ → ℚ → ℚ → ℚ × ℚ) → Type
-- eqElim₃Ty lrhs = (∀ {k m k' m' k'' m''} → fst (lrhs [ (k , 1+ m) ] [ (k' , 1+ m') ] [ (k'' , 1+ m'') ])
--         ≡  snd (lrhs [ (k , 1+ m) ] [ (k' , 1+ m') ] [ (k'' , 1+ m'') ]))

-- eqElim₄Ty : (lrhs : ℚ → ℚ → ℚ → ℚ → ℚ × ℚ) → Type
-- eqElim₄Ty lrhs = (∀ {k m k' m' k'' m'' k''' m'''} →
--   fst (lrhs [ (k , 1+ m) ] [ (k' , 1+ m') ] [ (k'' , 1+ m'') ] [ (k''' , 1+ m''') ])
--         ≡  snd (lrhs [ (k , 1+ m) ] [ (k' , 1+ m') ] [ (k'' , 1+ m'') ] [ (k''' , 1+ m''') ]))


-- eqElim₅Ty : (lrhs : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ × ℚ) → Type
-- eqElim₅Ty lrhs = (∀ {k m k' m' k'' m'' k''' m'''  k'''' m''''} →
--   fst (lrhs [ (k , 1+ m) ] [ (k' , 1+ m') ] [ (k'' , 1+ m'') ] [ (k''' , 1+ m''') ] [ (k'''' , 1+ m'''') ])
--         ≡  snd (lrhs [ (k , 1+ m) ] [ (k' , 1+ m') ] [ (k'' , 1+ m'') ] [ (k''' , 1+ m''') ] [ (k'''' , 1+ m'''') ]))


-- eqElim₆Ty : (lrhs : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ × ℚ) → Type
-- eqElim₆Ty lrhs = (∀ {k m k' m' k'' m'' k''' m'''  k'''' m'''' k''''' m'''''} →
--   fst (lrhs [ (k , 1+ m) ] [ (k' , 1+ m') ] [ (k'' , 1+ m'') ] [ (k''' , 1+ m''') ] [ (k'''' , 1+ m'''') ]
--    [ (k''''' , 1+ m''''') ])
--         ≡  snd (lrhs [ (k , 1+ m) ] [ (k' , 1+ m') ] [ (k'' , 1+ m'') ] [ (k''' , 1+ m''') ]
--          [ (k'''' , 1+ m'''') ] [ (k''''' , 1+ m''''') ]))



-- eqElim : (lrhs : ℚ → ℚ × ℚ) → eqElimTy lrhs
--     → ∀ (ε : ℚ) → fst (lrhs ε) ≡ snd (lrhs ε)
-- eqElim lrhs p = SetQuotient.ElimProp.go w
--   where

--   w : SetQuotient.ElimProp (λ z → fst (lrhs z) ≡ snd (lrhs z))
--   w .SetQuotient.ElimProp.isPropB _ = isSetℚ _ _
--   w .SetQuotient.ElimProp.f (n , (1+ n₁)) = p {n} {n₁}

-- eqElim₂ : (lrhs : ℚ → ℚ → ℚ × ℚ) → eqElim₂Ty lrhs
--     → ∀ (x y : ℚ) → fst (lrhs x y) ≡ (snd (lrhs x y))
-- eqElim₂ lrhs p = SetQuotient.ElimProp2.go w
--   where
--   w : SetQuotient.ElimProp2 (λ z z' → fst (lrhs z z') ≡ snd (lrhs z z'))
--   w .SetQuotient.ElimProp2.isPropB _ _ = isSetℚ _ _
--   w .SetQuotient.ElimProp2.f (n , (1+ n₁)) (m , (1+ m₁)) = p {n} {n₁} {m} {m₁}

-- eqElim₃ : (lrhs : ℚ → ℚ → ℚ → ℚ × ℚ) → eqElim₃Ty lrhs
--     → ∀ (x y z : ℚ) → fst (lrhs x y z) ≡ (snd (lrhs x y z))
-- eqElim₃ lrhs p = SetQuotient.ElimProp3.go w
--   where
--   w : SetQuotient.ElimProp3 (λ z z' z'' → fst (lrhs z z' z'') ≡ snd (lrhs z z' z''))
--   w .SetQuotient.ElimProp3.isPropB _ _ _ = isSetℚ _ _
--   w .SetQuotient.ElimProp3.f (n , (1+ n₁)) (m , (1+ m₁)) (m' , (1+ m₁')) = p {n} {n₁} {m} {m₁} {m'} {m₁'}

-- eqElim₄ : (lrhs : ℚ → ℚ → ℚ → ℚ → ℚ × ℚ) → eqElim₄Ty lrhs
--     → ∀ (x y z z' : ℚ) → fst (lrhs x y z z') ≡ (snd (lrhs x y z z'))
-- eqElim₄ lrhs p = SetQuotient.ElimProp4.go w
--   where
--   w : SetQuotient.ElimProp4 (λ z z' z'' z''' → fst (lrhs z z' z'' z''') ≡ snd (lrhs z z' z'' z'''))
--   w .SetQuotient.ElimProp4.isPropB _ _ _ _ = isSetℚ _ _
--   w .SetQuotient.ElimProp4.f (n , (1+ n₁)) (m , (1+ m₁)) (m' , (1+ m₁')) (m'' , (1+ m₁'')) =
--    p {n} {n₁} {m} {m₁} {m'} {m₁'} {m''} {m₁''}


-- eqElim₅ : (lrhs : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ × ℚ) → eqElim₅Ty lrhs
--     → ∀ (x y z z' z'' : ℚ) → fst (lrhs x y z z' z'') ≡ (snd (lrhs x y z z' z''))
-- eqElim₅ lrhs p = SetQuotient.ElimProp5.go w
--   where
--   w : SetQuotient.ElimProp5 (λ z z' z'' z''' z'''' →
--     fst (lrhs z z' z'' z''' z'''') ≡ snd (lrhs z z' z'' z''' z''''))
--   w .SetQuotient.ElimProp5.isPropB _ _ _ _ _ = isSetℚ _ _
--   w .SetQuotient.ElimProp5.f (n , (1+ n₁)) (m , (1+ m₁)) (m' , (1+ m₁')) (m'' , (1+ m₁'')) (m''' , (1+ m₁''')) =
--    p {n} {n₁} {m} {m₁} {m'} {m₁'} {m''} {m₁''} {m'''} {m₁'''}


-- eqElim₆ : (lrhs : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ × ℚ) → eqElim₆Ty lrhs
--     → ∀ (x y z z' z'' z''' : ℚ) → fst (lrhs x y z z' z'' z''') ≡ (snd (lrhs x y z z' z'' z'''))
-- eqElim₆ lrhs p = SetQuotient.ElimProp6.go w
--   where
--   w : SetQuotient.ElimProp6 (λ z z' z'' z''' z'''' z''''' →
--     fst (lrhs z z' z'' z''' z'''' z''''') ≡ snd (lrhs z z' z'' z''' z'''' z'''''))
--   w .SetQuotient.ElimProp6.isPropB _ _ _ _ _ _ = isSetℚ _ _
--   w .SetQuotient.ElimProp6.f (n , (1+ n₁)) (m , (1+ m₁)) (m' , (1+ m₁')) (m'' , (1+ m₁''))
--    (m''' , (1+ m₁''')) (m'''' , (1+ m₁'''')) =
--    p {n} {n₁} {m} {m₁} {m'} {m₁'} {m''} {m₁''} {m'''} {m₁'''} {m''''} {m₁''''}

