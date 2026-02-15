module Cubical.Tactics.CommRingSolverFast.OverDecidable where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Reflection.Sugar

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Relation.Nullary



open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool;true;false;if_then_else_;_and_)
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Empty
open import Cubical.Data.Maybe

open import Cubical.Algebra.Ring.Properties

open import Cubical.Tactics.CommRingSolverFast.Utility
open import Cubical.Tactics.CommRingSolverFast.RawRing
open import Cubical.Tactics.CommRingSolverFast.AlgebraExpression
open import Cubical.Tactics.CommRingSolverFast.RawAlgebra

private
  variable
    ℓ ℓ' : Level


module DecCommRingSolver (R@(⟨R⟩ , _) : CommRing ℓ)
                         (_≟_ : Discrete ⟨R⟩ )
                         (R'@(⟨R'⟩ , _) : CommRing ℓ')
                         (hom@(scalar‵ , _) : CommRingHom R R')
                         where
 open CommRingStr (snd R)
 RRng : RawRing ℓ
 RRng = rawring ⟨R⟩ 0r 1r _+_ _·_ (-_)
 open RingTheory (CommRing→Ring R)
 module R‵ where
   open CommRingStr (snd R') public
   open RingTheory (CommRing→Ring R') public

 open IsCommRingHom (snd hom)

 open CommRingStr (snd R') using () renaming
   (0r to 0r‵;1r to 1r‵;_+_ to _+‵_; _·_ to _·‵_; -_ to -‵_)

 RAlg : RawAlgebra RRng ℓ'
 RAlg = rawalgebra ⟨R'⟩ scalar‵ 0r‵ 1r‵ (_+‵_) (_·‵_) (-‵_)



 open Eval RRng RAlg


 data IteratedHornerForms : ℕ → Type ℓ where
   const : ⟨R⟩ → IteratedHornerForms ℕ.zero
   0H : {n : ℕ} → IteratedHornerForms (ℕ.suc n)
   _·X+_ : {n : ℕ} → IteratedHornerForms (ℕ.suc n) → IteratedHornerForms n
                   → IteratedHornerForms (ℕ.suc n)

 isZero : {n : ℕ} → IteratedHornerForms n → Bool
 isZero (const x) = 𝟚.Dec→Bool (x ≟ 0r)
 isZero 0H = true
 isZero (P ·X+ Q) = (isZero P) 𝟚.and (isZero Q)

 leftIsZero : {n : ℕ}
              (P : IteratedHornerForms (ℕ.suc n))
              (Q : IteratedHornerForms n)
              → isZero (P ·X+ Q) ≡ true
              → isZero P ≡ true
 leftIsZero P Q isZeroSum with isZero P
 ... | true = refl
 ... | false = isZeroSum

 rightIsZero : {n : ℕ}
              (P : IteratedHornerForms (ℕ.suc n))
              (Q : IteratedHornerForms n)
              → isZero (P ·X+ Q) ≡ true
              → isZero Q ≡ true
 rightIsZero P Q isZeroSum with isZero Q
 ... | true = refl
 ... | false = byBoolAbsurdity (snd (extractFromAnd _ _ isZeroSum))



 eval : {n : ℕ} (P : IteratedHornerForms n)
        → Vec ⟨R'⟩ n → ⟨R'⟩
 eval  (const r) [] = scalar‵ r
 eval 0H (_ ∷ _) = 0r‵
 eval (P ·X+ Q) (x ∷ xs) =
      let
          P' = (eval P (x ∷ xs))
          Q' = eval Q xs
      in if (isZero P)
         then Q'
         else ((P' ·‵ x) +‵ Q')


 -- module IteratedHornerOperations where


 private
   1H' : (n : ℕ) → IteratedHornerForms n
   1H' ℕ.zero = const 1r
   1H' (ℕ.suc n) = 0H ·X+ 1H' n

   0H' : (n : ℕ) → IteratedHornerForms n
   0H' ℕ.zero = const 0r
   0H' (ℕ.suc n) = 0H

 1ₕ : {n : ℕ} → IteratedHornerForms n
 1ₕ {n = n} = 1H' n

 0ₕ : {n : ℕ} → IteratedHornerForms n
 0ₕ {n = n} = 0H' n

 X : (n : ℕ) (k : Fin n) → IteratedHornerForms n
 X (ℕ.suc m) zero = 1ₕ ·X+ 0ₕ
 X (ℕ.suc m) (suc k) = 0ₕ ·X+ X m k

 _+ₕ_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
              → IteratedHornerForms n
 (const r) +ₕ (const s) = const (r + s)
 0H +ₕ Q = Q
 (P ·X+ r) +ₕ 0H = P ·X+ r
 (P ·X+ r) +ₕ (Q ·X+ s) =
   let left = (P +ₕ Q)
       right = (r +ₕ s)
   in if ((isZero left) and (isZero right))
      then 0ₕ
      else left ·X+ right

 -ₕ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
 -ₕ (const x) = const (- x)
 -ₕ 0H = 0H
 -ₕ (P ·X+ Q) = (-ₕ P) ·X+ (-ₕ Q)

 _⋆_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms (ℕ.suc n)
               → IteratedHornerForms (ℕ.suc n)
 _·ₕ_ : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
               → IteratedHornerForms n
 r ⋆ 0H = 0H
 r ⋆ (P ·X+ Q) =
   if (isZero r)
   then 0ₕ
   else (r ⋆ P) ·X+ (r ·ₕ Q)

 const x ·ₕ const y = const (x · y)
 0H ·ₕ Q = 0H
 (P ·X+ Q) ·ₕ S =
    let
       z = (P ·ₕ S)
    in if (isZero z)
       then (Q ⋆ S)
       else (z ·X+ 0ₕ) +ₕ (Q ⋆ S)

 isZeroPresLeft⋆ :
   {n : ℕ}
   (r : IteratedHornerForms n)
   (P : IteratedHornerForms (ℕ.suc n))
   → isZero r ≡ true
   → isZero (r ⋆ P) ≡ true
 isZeroPresLeft⋆ r 0H isZero-r = refl
 isZeroPresLeft⋆ r (P ·X+ Q) isZero-r with isZero r
 ...  | true = refl
 ...  | false = byBoolAbsurdity isZero-r

 isZeroPresLeft·ₕ :
   {n : ℕ} (P Q : IteratedHornerForms n)
   → isZero P ≡ true
   → isZero (P ·ₕ Q) ≡ true
 isZeroPresLeft·ₕ (const y) (const x) isZeroP =
   let zz = 𝟚.toWitness {Q = y ≟ 0r} (subst 𝟚.Bool→Type (sym isZeroP) _ )
    in cong {y = yes (0LeftAnnihilates' _ _ zz)} 𝟚.Dec→Bool (isPropDec (is-set _ _) _ _)
 isZeroPresLeft·ₕ 0H Q isZeroP = refl
 isZeroPresLeft·ₕ (P ·X+ Q) S isZeroSum with isZero (P ·ₕ S) 𝟚.≟ true
 ... | no p = byBoolAbsurdity (sym notZeroProd ∙ isZeroProd)
              where notZeroProd = 𝟚.¬true→false _ p
                    isZeroP = extractFromAndLeft isZeroSum
                    isZeroProd = isZeroPresLeft·ₕ P S isZeroP
 ... | yes p with isZero (P ·ₕ S)
 ...        | true = isZeroPresLeft⋆ Q S isZeroQ
                     where isZeroQ = extractFromAndRight isZeroSum
 ...        | false = byBoolAbsurdity p

 asRawRing : (n : ℕ) → RawRing ℓ
 RawRing.Carrier (asRawRing n) = IteratedHornerForms n
 RawRing.0r (asRawRing n) = 0ₕ
 RawRing.1r (asRawRing n) = 1ₕ
 RawRing._+_ (asRawRing n) = _+ₕ_
 RawRing._·_ (asRawRing n) = _·ₕ_
 RawRing.- (asRawRing n) =  -ₕ


 someCalculation : {x : fst R'} → _ ≡ _
 someCalculation {x = x} =
   0r‵                   ≡⟨ sym (R‵.+IdR 0r‵) ⟩
   0r‵ +‵ 0r‵              ≡[ i ]⟨ R‵.0LeftAnnihilates x (~ i) +‵ 0r‵ ⟩
   0r‵ ·‵ x +‵ 0r‵          ∎


 evalIsZero : {n : ℕ} (P : IteratedHornerForms n)
            → (l : Vec ⟨R'⟩ n)
            → isZero P ≡ true
            → eval P l ≡ 0r‵
 evalIsZero (const x) [] isZeroP =
   cong scalar‵ (𝟚.toWitness {Q = x ≟ 0r} (subst 𝟚.Bool→Type (sym isZeroP) _ )) ∙
      pres0
 evalIsZero 0H (x ∷ xs) _ = refl
 evalIsZero {n = ℕ.suc n} (P ·X+ Q) (x ∷ xs) isZeroPandQ with isZero P
 ... | true = eval Q xs   ≡⟨ evalIsZero Q xs isZeroQ ⟩
              0r‵ ∎
              where isZeroQ = snd (extractFromAnd _ _ isZeroPandQ)
 ... | false = byBoolAbsurdity isZeroP
              where isZeroP = isZeroPandQ

 computeEvalSummandIsZero :
              {n : ℕ}
              (P : IteratedHornerForms (ℕ.suc n))
              (Q : IteratedHornerForms n)
            → (xs : Vec ⟨R'⟩ n)
            → (x : ⟨R'⟩)
            → isZero P ≡ true
            → eval (P ·X+ Q) (x ∷ xs) ≡ eval Q xs
 computeEvalSummandIsZero P Q xs x isZeroP with isZero P
 ... | true = refl
 ... | false = byBoolAbsurdity isZeroP

 computeEvalNotZero :
              {n : ℕ}
              (P : IteratedHornerForms (ℕ.suc n))
              (Q : IteratedHornerForms n)
            → (xs : Vec ⟨R'⟩ n)
            → (x : ⟨R'⟩)
            → ¬ (isZero P ≡ true)
            → eval (P ·X+ Q) (x ∷ xs) ≡ (eval P (x ∷ xs)) ·‵ x +‵ eval Q xs
 computeEvalNotZero P Q xs x notZeroP with isZero P
 ... | true = byBoolAbsurdity (sym (𝟚.¬true→false true notZeroP))
 ... | false = refl

 combineCasesEval :
   {n : ℕ}  (P : IteratedHornerForms (ℕ.suc n)) (Q : IteratedHornerForms n)
   (x : ⟨R'⟩) (xs : Vec ⟨R'⟩ n)
   →   eval (P ·X+ Q) (x ∷ xs)
     ≡ (eval P (x ∷ xs)) ·‵ x +‵ eval Q xs
 combineCasesEval P Q x xs with isZero P 𝟚.≟ true
 ... | yes p =
      eval (P ·X+ Q) (x ∷ xs)            ≡⟨ computeEvalSummandIsZero P Q xs x p ⟩
      eval Q xs                          ≡⟨ sym (R‵.+IdL _) ⟩
      0r‵ +‵ eval Q xs                     ≡[ i ]⟨ R‵.0LeftAnnihilates x (~ i) +‵ eval Q xs ⟩
      0r‵ ·‵ x +‵ eval Q xs                 ≡[ i ]⟨ (evalIsZero P (x ∷ xs) p (~ i)) ·‵ x +‵ eval Q xs ⟩
      (eval P (x ∷ xs)) ·‵ x +‵ eval Q xs ∎
 ... | no p  = computeEvalNotZero P Q xs x p


 compute+ₕEvalBothZero :
   (n : ℕ) (P Q : IteratedHornerForms (ℕ.suc n))
   (r s : IteratedHornerForms n)
   (x : ⟨R'⟩) (xs : Vec ⟨R'⟩ n)
   → (isZero (P +ₕ Q) and isZero (r +ₕ s)) ≡ true
   → eval ((P ·X+ r) +ₕ (Q ·X+ s)) (x ∷ xs) ≡ eval ((P +ₕ Q) ·X+ (r +ₕ s)) (x ∷ xs)
 compute+ₕEvalBothZero n P Q r s x xs bothZero with isZero (P +ₕ Q) and isZero (r +ₕ s) | bothZero
 ... | true | p =
              eval 0H (x ∷ xs)                            ≡⟨ refl ⟩
              0r‵                                                  ≡⟨ someCalculation ⟩
              0r‵ ·‵ x +‵ 0r‵                                          ≡⟨ step1  ⟩
              (eval (P +ₕ Q) (x ∷ xs)) ·‵ x +‵ eval (r +ₕ s) xs       ≡⟨ step2 ⟩
              eval ((P +ₕ Q) ·X+ (r +ₕ s)) (x ∷ xs) ∎
           where step1 : 0r‵ ·‵ x +‵ 0r‵ ≡ (eval (P +ₕ Q) (x ∷ xs)) ·‵ x +‵ eval (r +ₕ s) xs
                 step1 i = (evalIsZero (P +ₕ Q) (x ∷ xs) (fst (extractFromAnd _ _ (bothZero))) (~ i))
                            ·‵ x
                   +‵ (evalIsZero (r +ₕ s) xs (snd (extractFromAnd _ _ (bothZero))) (~ i))
                 step2 = sym (combineCasesEval (P +ₕ Q) (r +ₕ s) x xs)
 ... | false | p = byBoolAbsurdity p

 compute+ₕEvalNotBothZero :
   (n : ℕ) (P Q : IteratedHornerForms (ℕ.suc n))
   (r s : IteratedHornerForms n)
   (x : (fst R')) (xs : Vec (fst R') n)
   → (isZero (P +ₕ Q) and isZero (r +ₕ s)) ≡ false
   → eval ((P ·X+ r) +ₕ (Q ·X+ s)) (x ∷ xs) ≡ eval ((P +ₕ Q) ·X+ (r +ₕ s)) (x ∷ xs)
 compute+ₕEvalNotBothZero n P Q r s _ _ notBothZero
   with isZero (P +ₕ Q) and isZero (r +ₕ s) | notBothZero
 ... | true | p = byBoolAbsurdity (sym p)
 ... | false | p = refl



 Variable : (n : ℕ) (k : Fin n) → IteratedHornerForms n
 Variable n k = X n k

 Constant : (n : ℕ) (r : ⟨R⟩) → IteratedHornerForms n
 Constant ℕ.zero r = const r
 Constant (ℕ.suc n) r =
   decRec (λ _ → 0ₕ) (λ _ → 0ₕ ·X+ Constant n r) (r ≟ 0r)


--    module HomomorphismProperties  where


 EvalHom+0 : {n : ℕ} (P : IteratedHornerForms n) (xs : Vec ⟨R'⟩ n)
     → eval (0ₕ +ₕ P) xs ≡ eval P xs
 EvalHom+0 {n = ℕ.zero} (const x) [] = cong scalar‵ (+IdL ( x))
 EvalHom+0 {n = ℕ.suc _} P xs = refl

 Eval0H : {n : ℕ} (xs : Vec ⟨R'⟩ n)
        → eval 0ₕ xs ≡ 0r‵
 Eval0H  [] = pres0
 Eval0H (x ∷ xs) = refl

 Eval1ₕ : {n : ℕ} (xs : Vec ⟨R'⟩ n)
        → eval  1ₕ xs ≡ 1r‵
 Eval1ₕ [] = pres1
 Eval1ₕ (x ∷ xs) =
   eval 1ₕ (x ∷ xs)                             ≡⟨ refl ⟩
   eval (0H ·X+ 1ₕ) (x ∷ xs)                    ≡⟨ combineCasesEval 0H 1ₕ x xs ⟩
   eval  0H (x ∷ xs) ·‵ x +‵ eval 1ₕ xs   ≡⟨ cong (λ u → u ·‵ x +‵ eval 1ₕ xs)
                                                                  (Eval0H (x ∷ xs)) ⟩
   0r‵ ·‵ x +‵ eval 1ₕ xs                          ≡⟨ cong (λ u → 0r‵ ·‵ x +‵ u)
                                                       (Eval1ₕ xs) ⟩
   0r‵ ·‵ x +‵ 1r‵                                  ≡⟨ cong (λ u → u +‵ 1r‵)
                                                        (R‵.0LeftAnnihilates _) ⟩
   0r‵ +‵ 1r‵                                      ≡⟨ R‵.+IdL _ ⟩
   1r‵ ∎

 -EvalDist :
   {n : ℕ} (P : IteratedHornerForms n) (xs : Vec ⟨R'⟩ n)
   → eval (-ₕ P) xs ≡ -‵ eval P xs
 -EvalDist (const x) []   = pres- _
 -EvalDist 0H  xs =  Eval0H xs ∙
   sym (R‵.0Selfinverse)
   ∙ cong -‵_ (sym (Eval0H xs)) --
 -EvalDist (P ·X+ Q) (x ∷ xs) =
     eval (-ₕ (P ·X+ Q)) (x ∷ xs)
   ≡⟨ refl ⟩
     eval ((-ₕ P) ·X+ (-ₕ Q)) (x ∷ xs)
   ≡⟨ combineCasesEval (-ₕ P) (-ₕ Q) x xs ⟩
     (eval (-ₕ P) (x ∷ xs)) ·‵ x +‵ eval (-ₕ Q) xs
   ≡⟨ cong (λ u → u ·‵ x +‵ eval (-ₕ Q) xs) (-EvalDist P _) ⟩
     (-‵ eval P (x ∷ xs)) ·‵ x +‵ eval (-ₕ Q) xs
   ≡⟨ cong (λ u → (-‵ eval P (x ∷ xs)) ·‵ x +‵ u) (-EvalDist Q _) ⟩
     (-‵ eval P (x ∷ xs)) ·‵ x +‵ -‵ eval Q xs
   ≡[ i ]⟨ R‵.-DistL· (eval P (x ∷ xs)) x i +‵  -‵ eval Q xs ⟩
     -‵ ((eval P (x ∷ xs)) ·‵ x) +‵ (-‵ eval Q xs)
   ≡⟨ R‵.-Dist _ _ ⟩
     -‵ ((eval P (x ∷ xs)) ·‵ x +‵ eval Q xs)
   ≡[ i ]⟨ -‵ combineCasesEval P Q x xs (~ i) ⟩
     -‵ eval (P ·X+ Q) (x ∷ xs) ∎

 combineCases+ : {n : ℕ} (P Q : IteratedHornerForms (ℕ.suc n))
                 (r s : IteratedHornerForms n)
                 (x : fst R') (xs : Vec (fst R') n)
                 → eval ((P ·X+ r) +ₕ (Q ·X+ s)) (x ∷ xs)
                 ≡ eval ((P +ₕ Q) ·X+ (r +ₕ s)) (x ∷ xs)
 combineCases+ {n = n} P Q r s x xs with (isZero (P +ₕ Q) and isZero (r +ₕ s)) 𝟚.≟ true
 ... | yes p = compute+ₕEvalBothZero n P Q r s x xs p
 ... | no p = compute+ₕEvalNotBothZero n P Q r s x xs (𝟚.¬true→false _ p)

 +Homeval :
   {n : ℕ} (P Q : IteratedHornerForms n) (xs : Vec ⟨R'⟩ n)
   → eval (P +ₕ Q) xs ≡ (eval P xs) +‵ (eval Q xs)
 +Homeval (const x) (const y) [] = pres+ _ _
 +Homeval 0H Q xs =
   eval (0H +ₕ Q) xs            ≡⟨ refl ⟩
   eval Q xs                    ≡⟨ sym (R‵.+IdL _) ⟩
   0r‵ +‵ eval Q xs               ≡⟨ cong (λ u → u +‵ eval Q xs) (sym (Eval0H xs)) ⟩
   eval 0H xs +‵ eval Q xs ∎
 +Homeval (P ·X+ Q) 0H xs =
   eval ((P ·X+ Q) +ₕ 0H) xs                    ≡⟨ refl ⟩
   eval (P ·X+ Q) xs                            ≡⟨ sym (R‵.+IdR _) ⟩
   eval (P ·X+ Q) xs +‵ 0r‵
  ≡⟨ cong (λ u → eval (P ·X+ Q) xs +‵ u) (sym (Eval0H xs)) ⟩
   eval (P ·X+ Q) xs +‵ eval 0H xs ∎
 +Homeval (P ·X+ Q) (S ·X+ T) (x ∷ xs) =
   eval ((P ·X+ Q) +ₕ (S ·X+ T)) (x ∷ xs)
  ≡⟨ combineCases+ P S Q T x xs ⟩
   eval ((P +ₕ S) ·X+ (Q +ₕ T)) (x ∷ xs)
  ≡⟨ combineCasesEval (P +ₕ S) (Q +ₕ T) x xs ⟩
   (eval (P +ₕ S) (x ∷ xs)) ·‵ x +‵ eval (Q +ₕ T) xs
  ≡⟨ cong (λ u → (eval (P +ₕ S) (x ∷ xs)) ·‵ x +‵ u) (+Homeval Q T xs) ⟩
   (eval (P +ₕ S) (x ∷ xs)) ·‵ x +‵ (eval Q xs +‵ eval T xs)
  ≡⟨ cong (λ u → u ·‵ x +‵ (eval Q xs +‵ eval T xs)) (+Homeval P S (x ∷ xs)) ⟩
   (eval P (x ∷ xs) +‵ eval S (x ∷ xs)) ·‵ x
   +‵ (eval Q xs +‵ eval T xs)
  ≡⟨ cong (λ u → u +‵ (eval Q xs +‵ eval T xs)) (R‵.·DistL+ _ _ _) ⟩
   (eval P (x ∷ xs)) ·‵ x +‵ (eval S (x ∷ xs)) ·‵ x
   +‵ (eval Q xs +‵ eval T xs)
  ≡⟨ R‵.+ShufflePairs _ _ _ _ ⟩
   ((eval P (x ∷ xs)) ·‵ x +‵ eval Q xs)
   +‵ ((eval S (x ∷ xs)) ·‵ x +‵ eval T xs)
  ≡[ i ]⟨ combineCasesEval P Q x xs (~ i) +‵ combineCasesEval S T x xs (~ i) ⟩
   eval (P ·X+ Q) (x ∷ xs)
   +‵ eval (S ·X+ T) (x ∷ xs) ∎

 ⋆Homeval : {n : ℕ}
            (r : IteratedHornerForms n)
            (P : IteratedHornerForms (ℕ.suc n)) (x : ⟨R'⟩) (xs : Vec ⟨R'⟩ n)
          → eval (r ⋆ P) (x ∷ xs) ≡ eval r xs ·‵ eval P (x ∷ xs)

 ⋆0LeftAnnihilates :
   {n : ℕ} (P : IteratedHornerForms (ℕ.suc n)) (xs : Vec ⟨R'⟩ (ℕ.suc n))
   → eval (0ₕ ⋆ P) xs ≡ 0r‵
 ⋆0LeftAnnihilates 0H xs = Eval0H xs
 ⋆0LeftAnnihilates {n = ℕ.zero} (P ·X+ Q) (x ∷ xs) =
    evalIsZero (0ₕ ⋆ (P ·X+ Q)) (x ∷ xs)
      (cong {x = (0ₕ ⋆ (P ·X+ Q))} {y = 0ₕ} isZero
       (cong {x = 0r ≟ 0r} {y = yes refl} (λ zz → (if (𝟚.Dec→Bool zz) then 0ₕ else
    ((0ₕ ⋆ P) ·X+ (0ₕ ·ₕ Q)))) (isPropDec (is-set _ _) _ _)))

 ⋆0LeftAnnihilates {n = ℕ.suc _} (P ·X+ Q) (x ∷ xs) = refl

 ⋆isZeroLeftAnnihilates :
   {n : ℕ} (r : IteratedHornerForms n)
           (P : IteratedHornerForms (ℕ.suc n))
   (xs : Vec ⟨R'⟩ (ℕ.suc n))
   → isZero r ≡ true
   → eval (r ⋆ P) xs ≡ 0r‵
 ⋆isZeroLeftAnnihilates r P xs isZero-r = evalIsZero (r ⋆ P) xs (isZeroPresLeft⋆ r P isZero-r)

 ·0LeftAnnihilates :
   {n : ℕ} (P : IteratedHornerForms n) (xs : Vec ⟨R'⟩ n)
   → eval (0ₕ ·ₕ P) xs ≡ 0r‵
 ·0LeftAnnihilates (const x) xs =
   cong (λ x → eval (const x) xs) (0LeftAnnihilates x) ∙ Eval0H xs
 ·0LeftAnnihilates 0H xs = Eval0H xs
 ·0LeftAnnihilates (P ·X+ P₁) xs = Eval0H xs

 ·isZeroLeftAnnihilates :
   {n : ℕ} (P Q : IteratedHornerForms n)
   (xs : Vec (fst R') n)
   → isZero P ≡ true
   → eval (P ·ₕ Q) xs ≡ 0r‵
 ·isZeroLeftAnnihilates P Q xs isZeroP = evalIsZero (P ·ₕ Q) xs (isZeroPresLeft·ₕ P Q isZeroP)

 ·Homeval : {n : ℕ} (P Q : IteratedHornerForms n) (xs : Vec ⟨R'⟩ n)
   → eval (P ·ₕ Q) xs ≡ (eval P xs) ·‵ (eval Q xs)

 combineCases⋆ : {n : ℕ} (x : fst R') (xs : Vec (fst R') n)
               → (r : IteratedHornerForms n)
               → (P : IteratedHornerForms (ℕ.suc n))
               → (Q : IteratedHornerForms n)
               → eval (r ⋆ (P ·X+ Q)) (x ∷ xs) ≡ eval ((r ⋆ P) ·X+ (r ·ₕ Q)) (x ∷ xs)
 combineCases⋆ x xs r P Q with isZero r 𝟚.≟ true
 ... | yes p =
   eval (r ⋆ (P ·X+ Q)) (x ∷ xs)                ≡⟨ ⋆isZeroLeftAnnihilates r (P ·X+ Q) (x ∷ xs) p ⟩
   0r‵                                           ≡⟨ someCalculation ⟩
   0r‵ ·‵ x +‵ 0r‵                                  ≡⟨ step1 ⟩
   eval (r ⋆ P) (x ∷ xs) ·‵ x +‵ eval (r ·ₕ Q) xs  ≡⟨ sym (combineCasesEval (r ⋆ P) (r ·ₕ Q) x xs) ⟩
   eval ((r ⋆ P) ·X+ (r ·ₕ Q)) (x ∷ xs) ∎
   where
     step1 : 0r‵ ·‵ x +‵ 0r‵ ≡ eval (r ⋆ P) (x ∷ xs) ·‵ x +‵ eval (r ·ₕ Q) xs
     step1 i = ⋆isZeroLeftAnnihilates r P (x ∷ xs) p (~ i) ·‵ x +‵ ·isZeroLeftAnnihilates r Q xs p (~ i)
 ... | no p with isZero r
 ...           | true = byAbsurdity (p refl)
 ...           | false = refl

 ⋆Homeval r 0H x xs =
   eval (r ⋆ 0H) (x ∷ xs)                ≡⟨ refl ⟩
   0r‵                                    ≡⟨ sym (R‵.0RightAnnihilates _) ⟩
   eval r xs ·‵ 0r‵                        ≡⟨ refl ⟩
   eval r xs ·‵ eval  0H (x ∷ xs) ∎
 ⋆Homeval r (P ·X+ Q) x xs =
     eval (r ⋆ (P ·X+ Q)) (x ∷ xs)                ≡⟨ combineCases⋆ x xs r P Q ⟩
     eval ((r ⋆ P) ·X+ (r ·ₕ Q)) (x ∷ xs)
   ≡⟨ combineCasesEval (r ⋆ P) (r ·ₕ Q) x xs ⟩
     (eval (r ⋆ P) (x ∷ xs)) ·‵ x +‵ eval (r ·ₕ Q) xs
   ≡⟨ cong (λ u → u ·‵ x +‵ eval (r ·ₕ Q) xs) (⋆Homeval r P x xs) ⟩
     (eval r xs ·‵ eval P (x ∷ xs)) ·‵ x +‵ eval (r ·ₕ Q) xs
   ≡⟨ cong (λ u → (eval r xs ·‵ eval P (x ∷ xs)) ·‵ x +‵ u) (·Homeval r Q xs) ⟩
     (eval r xs ·‵ eval P (x ∷ xs)) ·‵ x +‵ eval r xs ·‵ eval Q xs
   ≡⟨ cong (λ u → u  +‵ eval r xs ·‵ eval Q xs) (sym (R‵.·Assoc _ _ _)) ⟩
     eval r xs ·‵ (eval P (x ∷ xs) ·‵ x) +‵ eval r xs ·‵ eval Q xs
   ≡⟨ sym (R‵.·DistR+ _ _ _) ⟩
     eval r xs ·‵ ((eval P (x ∷ xs) ·‵ x) +‵ eval Q xs)
   ≡[ i ]⟨ eval r xs ·‵ combineCasesEval P Q x xs (~ i) ⟩
     eval r xs ·‵ eval (P ·X+ Q) (x ∷ xs) ∎

 lemmaForCombineCases· :
   {n : ℕ} (Q : IteratedHornerForms n) (P S : IteratedHornerForms (ℕ.suc n))
   (xs : Vec (fst R') (ℕ.suc n))
   →  isZero (P ·ₕ S) ≡ true
   → eval ((P ·X+ Q) ·ₕ S) xs ≡ eval (Q ⋆ S) xs
 lemmaForCombineCases· Q P S xs isZeroProd with isZero (P ·ₕ S)
 ... | true = refl
 ... | false = byBoolAbsurdity isZeroProd

 combineCases· :
   {n : ℕ} (Q : IteratedHornerForms n) (P S : IteratedHornerForms (ℕ.suc n))
   (xs : Vec (fst R') (ℕ.suc n))
   → eval ((P ·X+ Q) ·ₕ S) xs ≡ eval (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) xs
 combineCases· Q P S (x ∷ xs) with isZero (P ·ₕ S) 𝟚.≟ true
 ... | yes p =
       eval ((P ·X+ Q) ·ₕ S) (x ∷ xs)                          ≡⟨ lemmaForCombineCases· Q P S (x ∷ xs) p ⟩
       eval (Q ⋆ S) (x ∷ xs)                                   ≡⟨ sym (R‵.+IdL _) ⟩
       0r‵ +‵ eval (Q ⋆ S) (x ∷ xs)                              ≡⟨ step1 ⟩
       eval ((P ·ₕ S) ·X+ 0ₕ) (x ∷ xs) +‵ eval (Q ⋆ S) (x ∷ xs)  ≡⟨ step2 ⟩
       eval (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) (x ∷ xs)             ∎
       where
         lemma =
           eval ((P ·ₕ S) ·X+ 0ₕ) (x ∷ xs)          ≡⟨ combineCasesEval (P ·ₕ S) 0ₕ x xs ⟩
           eval (P ·ₕ S) (x ∷ xs) ·‵ x +‵ eval 0ₕ xs  ≡[ i ]⟨ evalIsZero (P ·ₕ S) (x ∷ xs) p i ·‵ x +‵ Eval0H xs i ⟩
           0r‵ ·‵ x +‵ 0r‵                             ≡⟨ sym (someCalculation) ⟩
           0r‵                                      ∎
         step1 : _ ≡ _
         step1 i = lemma (~ i) +‵ eval (Q ⋆ S) (x ∷ xs)
         step2 = sym (+Homeval ((P ·ₕ S) ·X+ 0ₕ) (Q ⋆ S) (x ∷ xs))
 ... | no p with isZero (P ·ₕ S)
 ...           | true = byAbsurdity (p refl)
 ...           | false = refl

 ·Homeval (const x) (const y) [] = pres· _ _
 ·Homeval 0H Q xs =
   eval (0H ·ₕ Q) xs       ≡⟨ Eval0H xs ⟩
   0r‵                     ≡⟨ sym (R‵.0LeftAnnihilates _) ⟩
   0r‵ ·‵ eval Q xs         ≡⟨ cong (λ u → u ·‵ eval Q xs) (sym (Eval0H xs)) ⟩
   eval 0H xs ·‵ eval Q xs ∎
 ·Homeval (P ·X+ Q) S (x ∷ xs) =
     eval ((P ·X+ Q) ·ₕ S) (x ∷ xs)
   ≡⟨ combineCases· Q P S (x ∷ xs) ⟩
     eval (((P ·ₕ S) ·X+ 0ₕ) +ₕ (Q ⋆ S)) (x ∷ xs)
   ≡⟨ +Homeval ((P ·ₕ S) ·X+ 0ₕ) (Q ⋆ S) (x ∷ xs) ⟩
     eval ((P ·ₕ S) ·X+ 0ₕ) (x ∷ xs) +‵ eval (Q ⋆ S) (x ∷ xs)
   ≡⟨ cong (λ u → u +‵ eval (Q ⋆ S) (x ∷ xs)) (combineCasesEval (P ·ₕ S) 0ₕ x xs) ⟩
     (eval (P ·ₕ S) (x ∷ xs) ·‵ x +‵ eval 0ₕ xs) +‵ eval (Q ⋆ S) (x ∷ xs)
   ≡⟨ cong (λ u → u +‵ eval (Q ⋆ S) (x ∷ xs))
         ((eval (P ·ₕ S) (x ∷ xs) ·‵ x +‵ eval 0ₕ xs)
        ≡⟨ cong (λ u → eval (P ·ₕ S) (x ∷ xs) ·‵ x +‵ u) (Eval0H xs) ⟩
          (eval (P ·ₕ S) (x ∷ xs) ·‵ x +‵ 0r‵)
        ≡⟨ R‵.+IdR _ ⟩
          (eval (P ·ₕ S) (x ∷ xs) ·‵ x)
        ≡⟨ cong (λ u → u ·‵ x) (·Homeval P S (x ∷ xs)) ⟩
          ((eval P (x ∷ xs) ·‵ eval S (x ∷ xs)) ·‵ x)
        ≡⟨ sym (R‵.·Assoc _ _ _) ⟩
          (eval P (x ∷ xs) ·‵ (eval S (x ∷ xs) ·‵ x))
        ≡⟨ cong (λ u → eval P (x ∷ xs) ·‵ u) (R‵.·Comm _ _) ⟩
          (eval P (x ∷ xs) ·‵ (x ·‵ eval S (x ∷ xs)))
        ≡⟨ R‵.·Assoc _ _ _ ⟩
          (eval P (x ∷ xs) ·‵ x) ·‵ eval S (x ∷ xs)
         ∎) ⟩
     (eval P (x ∷ xs) ·‵ x) ·‵ eval S (x ∷ xs) +‵ eval (Q ⋆ S) (x ∷ xs)
   ≡⟨ cong (λ u → (eval P (x ∷ xs) ·‵ x) ·‵ eval S (x ∷ xs) +‵ u)
           (⋆Homeval Q S x xs) ⟩
     (eval P (x ∷ xs) ·‵ x) ·‵ eval S (x ∷ xs) +‵ eval Q xs ·‵ eval S (x ∷ xs)
   ≡⟨ sym (R‵.·DistL+ _ _ _) ⟩
     ((eval P (x ∷ xs) ·‵ x) +‵ eval Q xs) ·‵ eval S (x ∷ xs)
   ≡⟨ cong (λ u → u ·‵ eval S (x ∷ xs)) (sym (combineCasesEval P Q x xs)) ⟩
     eval (P ·X+ Q) (x ∷ xs) ·‵ eval S (x ∷ xs) ∎


--    module EqualityToNormalform  where

 RExpr : (n : ℕ) → Type _
 RExpr = Expr RRng (fst R')

 normalize : {n : ℕ} → RExpr n → IteratedHornerForms n
 normalize {n = n} (K r) = Constant n r
 normalize {n = n} (∣ k) = Variable n k
 normalize (x +' y) =
   (normalize x) +ₕ (normalize y)
 normalize (x ·' y) =
   (normalize x) ·ₕ (normalize y)
 normalize (-' x) =  -ₕ (normalize x)

 -- -- normalizeIHF : {n : ℕ} → IteratedHornerForms n → IteratedHornerForms n
 -- -- normalizeIHF (const x) = {!!}
 -- -- normalizeIHF 0H = {!!}
 -- -- normalizeIHF (x ·X+ x₁) = {!!}

 isEqualToNormalform :
      {n : ℕ} (e : RExpr n) (xs : Vec (fst R') n)
    → eval (normalize e) xs ≡ ⟦ e ⟧ xs

 isEqualToNormalform (K r) [] = refl
 isEqualToNormalform {n = ℕ.suc n} (K r) (x ∷ xs) =
   zz (r ≟ 0r)

   where
   zz : ∀ rr → eval (decRec (λ _ → 0ₕ) (λ _ → 0ₕ ·X+ Constant n r) rr) (x ∷ xs) ≡ scalar‵ r
   zz (yes p) = sym (cong scalar‵ p ∙ pres0)
   zz (no _) =
    eval (0ₕ ·X+ Constant n r) (x ∷ xs)           ≡⟨ combineCasesEval 0ₕ (Constant n r) x xs ⟩
    eval 0ₕ (x ∷ xs) ·‵ x +‵ eval (Constant n r) xs ≡⟨ cong (λ u → u ·‵ x +‵ eval (Constant n r) xs)
                                                            (Eval0H (x ∷ xs)) ⟩
    0r‵ ·‵ x +‵ eval (Constant n r) xs               ≡⟨ cong
                                                         (λ u → u +‵ eval (Constant n r) xs)
                                                         (R‵.0LeftAnnihilates _) ⟩
    0r‵ +‵ eval (Constant n r) xs                   ≡⟨ R‵.+IdL _ ⟩
    eval (Constant n r) xs                        ≡⟨ isEqualToNormalform (K r) xs ⟩
    _ ∎
 isEqualToNormalform (∣ zero) (x ∷ xs) =
   eval (1ₕ ·X+ 0ₕ) (x ∷ xs)           ≡⟨ combineCasesEval 1ₕ 0ₕ x xs ⟩
   eval 1ₕ (x ∷ xs) ·‵ x +‵ eval 0ₕ xs   ≡⟨ cong (λ u → u ·‵ x +‵ eval 0ₕ xs)
                                             (Eval1ₕ (x ∷ xs)) ⟩
   1r‵ ·‵ x +‵ eval 0ₕ xs                 ≡⟨ cong (λ u → 1r‵  ·‵ x +‵ u ) (Eval0H xs) ⟩
   1r‵ ·‵ x +‵ 0r‵                        ≡⟨ R‵.+IdR _ ⟩
   1r‵ ·‵ x                             ≡⟨ R‵.·IdL _ ⟩
   x ∎
 isEqualToNormalform {n = ℕ.suc n} (∣ (suc k)) (x ∷ xs) =
     eval (0ₕ ·X+ Variable n k) (x ∷ xs)           ≡⟨ combineCasesEval 0ₕ (Variable n k) x xs ⟩
     eval 0ₕ (x ∷ xs) ·‵ x +‵ eval (Variable n k) xs ≡⟨ cong (λ u → u ·‵ x +‵ eval (Variable n k) xs)
                                                             (Eval0H (x ∷ xs)) ⟩
     0r‵ ·‵ x +‵ eval (Variable n k) xs              ≡⟨ cong (λ u → u +‵ eval (Variable n k) xs)
                                                             (R‵.0LeftAnnihilates _) ⟩
     0r‵ +‵ eval (Variable n k) xs                  ≡⟨ R‵.+IdL _ ⟩
     eval (Variable n k) xs                       ≡⟨ isEqualToNormalform (∣ k) xs ⟩
     ⟦ ∣ (suc k) ⟧ (x ∷ xs) ∎

 isEqualToNormalform (-' e) [] =
   eval (-ₕ (normalize e)) []  ≡⟨ -EvalDist (normalize e) [] ⟩
   -‵ eval (normalize e) []    ≡⟨ cong -‵_ (isEqualToNormalform e [] ) ⟩
   -‵ ⟦ e ⟧ [] ∎
 isEqualToNormalform (-' e) (x ∷ xs) =
   eval (-ₕ (normalize e)) (x ∷ xs) ≡⟨ -EvalDist (normalize e) (x ∷ xs) ⟩
   -‵ eval (normalize e) (x ∷ xs)    ≡⟨ cong -‵_ (isEqualToNormalform e (x ∷ xs) ) ⟩
   -‵ ⟦ e ⟧ (x ∷ xs) ∎

 isEqualToNormalform (e +' e₁) [] =
       eval (normalize e +ₕ normalize e₁) []
     ≡⟨ +Homeval (normalize e) _ [] ⟩
       eval (normalize e) []
       +‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → u +‵ eval (normalize e₁) [])
             (isEqualToNormalform e []) ⟩
       ⟦ e ⟧ []
       +‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → ⟦ e ⟧ [] +‵ u) (isEqualToNormalform e₁ []) ⟩
       ⟦ e ⟧ [] +‵ ⟦ e₁ ⟧ [] ∎
 isEqualToNormalform (e +' e₁) (x ∷ xs) =
       eval (normalize e +ₕ normalize e₁) (x ∷ xs)
     ≡⟨ +Homeval (normalize e) _ (x ∷ xs) ⟩
       eval (normalize e) (x ∷ xs) +‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → u +‵ eval (normalize e₁) (x ∷ xs))
             (isEqualToNormalform e (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) +‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) +‵ u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) +‵ ⟦ e₁ ⟧ (x ∷ xs) ∎

 isEqualToNormalform (e ·' e₁) [] =
       eval (normalize e ·ₕ normalize e₁) []
     ≡⟨ ·Homeval (normalize e) _ [] ⟩
       eval (normalize e) [] ·‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → u ·‵ eval (normalize e₁) [])
             (isEqualToNormalform e []) ⟩
       ⟦ e ⟧ [] ·‵ eval (normalize e₁) []
     ≡⟨ cong (λ u → ⟦ e ⟧ [] ·‵ u) (isEqualToNormalform e₁ []) ⟩
       ⟦ e ⟧ [] ·‵ ⟦ e₁ ⟧ [] ∎

 isEqualToNormalform (e ·' e₁) (x ∷ xs) =
       eval (normalize e ·ₕ normalize e₁) (x ∷ xs)
     ≡⟨ ·Homeval (normalize e) _ (x ∷ xs) ⟩
       eval (normalize e) (x ∷ xs) ·‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → u ·‵ eval (normalize e₁) (x ∷ xs))
             (isEqualToNormalform e (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) ·‵ eval (normalize e₁) (x ∷ xs)
     ≡⟨ cong (λ u → ⟦ e ⟧ (x ∷ xs) ·‵ u) (isEqualToNormalform e₁ (x ∷ xs)) ⟩
       ⟦ e ⟧ (x ∷ xs) ·‵ ⟦ e₁ ⟧ (x ∷ xs) ∎

 -- _expr≟_ : ∀ {n} → ∀ (e₁ e₂ : RExpr n) → Maybe (e₁ ≡ e₂)
 -- _expr≟_ {n} (K x) (K x') = decRec (just ∘ cong K ) (λ _ → nothing) (x ≟ x')
 -- _expr≟_ {n} (∣ x) (∣ x')  = decRec (just ∘ cong ∣ ) (λ _ → nothing) (discreteFin x x')
 -- _expr≟_ {n} (x +' x₁) (x' +' x₁') =
 --    do p ← (x expr≟ x')
 --       p₁ ← (x₁ expr≟ x₁')
 --       just (cong₂ _+'_ p p₁)
 -- _expr≟_ {n} (x ·' x₁) (x' ·' x₁') =
 --    do p ← (x expr≟ x')
 --       p₁ ← (x₁ expr≟ x₁')
 --       just (cong₂ _·'_ p p₁)
 -- _expr≟_ {n} (-' x) (-' x')        = map-Maybe (cong (-'_)) (x expr≟ x')
 -- _expr≟_ {n} _ _ = nothing


 -- _ihr≟_ : ∀ {n} → ∀ (e₁ e₂ : IteratedHornerForms n) → Maybe (e₁ ≡ e₂)
 -- const x ihr≟ const x' = decRec (just ∘ cong const ) (λ _ → nothing) (x ≟ x')
 -- 0H ihr≟ 0H = just refl
 -- (e₁ ·X+ e₂) ihr≟ (e₁' ·X+ e₂') =
 --    do p ← (e₁ ihr≟ e₁')
 --       p₁ ← (e₂ ihr≟ e₂')
 --       just (cong₂ _·X+_ p p₁)
 -- _ ihr≟ _ = nothing

 IHR? : ∀ {n} → ∀ (e₁ e₂ : IteratedHornerForms n) → (Σ (Type ℓ) λ X → X → e₁ ≡ e₂)
 IHR? (const x) (const x') = (x ≡ x') , cong const
 IHR? 0H 0H = ℕ.Unit* , λ _ → refl
 IHR? (e₁ ·X+ e₂) (e₁' ·X+ e₂') =
   let X , f = IHR? e₁ e₁'
       X' , f' = IHR? e₂ e₂'
   in X × X' , λ (x , x') → cong₂ _·X+_ (f x) (f' x')
 IHR? _ _ = ⊥* , λ ()


 solve :
   {n : ℕ} (e₁ e₂ : RExpr n) (xs : Vec (fst R') n)
   → fst (IHR? (normalize e₁) (normalize e₂)) → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs
 solve e₁ e₂ xs z =
   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
   eval (normalize e₁) xs ≡⟨
    cong eval (snd (IHR? (normalize e₁) (normalize e₂)) z) ≡$ xs ⟩
   eval (normalize e₂) xs ≡⟨ isEqualToNormalform e₂ xs ⟩
   ⟦ e₂ ⟧ xs ∎

 congSolve :
   {n : ℕ} (e₁ e₂ : RExpr n) → ∀ {xs xs' : Vec (fst R') n} → xs ≡ xs'
   → fst (IHR? (normalize e₁) (normalize e₂)) → ⟦ e₁ ⟧ xs ≡ ⟦ e₂ ⟧ xs'
 congSolve e₁ e₂ {xs} {xs'} p z =
   ⟦ e₁ ⟧ xs                  ≡⟨ sym (isEqualToNormalform e₁ xs) ⟩
   eval (normalize e₁) xs ≡⟨
    cong₂ eval (snd (IHR? (normalize e₁) (normalize e₂)) z) p ⟩
   eval (normalize e₂) xs' ≡⟨ isEqualToNormalform e₂ xs' ⟩
   ⟦ e₂ ⟧ xs' ∎

