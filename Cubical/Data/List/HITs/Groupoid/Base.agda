{-# OPTIONS --safe #-}

module Cubical.Data.List.HITs.Groupoid.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function


open import Cubical.Data.Nat


pqpr-sides : ∀ {ℓ} {A : Type ℓ} → {x y z : A}
        → (p : x ≡ y) → (q r : y ≡ z)        
        → ∀ i j → I → Partial (i ∨ ~ i ∨ j ∨ ~ j) A
pqpr-sides p q r i j k = 
    λ { (i = i0) → invSides-filler r (sym p) (~ k) j 
      ; (i = i1) → q j 
      ; (j = i0) → p (i ∨ k)
      ; (j = i1) → r (i ∨ k)}

lem-pqpr : ∀ {ℓ} {A : Type ℓ} → {x y z : A}
        → {p : x ≡ y} → {q r : y ≡ z}
        → Square p q p r → r ≡ q
lem-pqpr {p = p} {q} {r} s i j = hcomp (pqpr-sides p q r i j) (s i j)

lem-pqpr⁻ : ∀ {ℓ} {A : Type ℓ} → {x y z : A}
        → {p : x ≡ y} → {q r : y ≡ z}
        → r ≡ q → Square p q p r 
lem-pqpr⁻ {p = p} {q} {r} s i j = hcomp (λ k → pqpr-sides p q r i j (~ k)) (s i j)

private
  variable
    ℓ : Level

infixr 5 _++_

data List (A : Type ℓ) : Type ℓ where
  [] : List A
  [_] : A → List A
  _++_ : List A → List A → List A
  ++-unit-r : (xs : List A) → xs ++ [] ≡ xs
  ++-unit-l : (xs : List A) → [] ++ xs ≡ xs
  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
  ++-triangle : ∀ xs ys → Square {A = List A}                     
                           (++-assoc xs [] ys)
                           refl
                           (cong (_++ ys) (++-unit-r xs))
                           (cong (xs ++_) (++-unit-l ys))

  ++-pentagon-diag : (xs ys zs ws : List A)
       → ((xs ++ ys) ++ zs) ++ ws ≡ xs ++ ys ++ zs ++ ws
  ++-pentagon-△ : (xs ys zs ws : List A) →
        Square refl (++-pentagon-diag xs ys zs ws)
          (sym (++-assoc _ _ _)) (++-assoc _ _ _)
  ++-pentagon-□ : (xs ys zs ws : List A) →
        Square (++-pentagon-diag xs ys zs ws)
           (++-assoc _ _ _)
           (cong (_++ ws) (++-assoc _ _ _))           
           (sym (cong (xs ++_) (++-assoc _ _ _)))

  trunc : isGroupoid (List A)

++-pentagon : {A : Type ℓ} → (xs ys zs ws : List A) → Square
           (++-assoc _ zs _ ∙∙ refl ∙∙ ++-assoc _ ys _)
           (++-assoc _ _ _)
           (cong (_++ ws) (++-assoc _ _ _))           
           (sym (cong (xs ++_) (++-assoc _ _ _)))
++-pentagon xs ys zs ws =
  (λ i j → hcomp
   (λ k → λ { (i = i1) → ++-pentagon-△ xs ys zs ws k j
            ; (j = i0) → ++-assoc (xs ++ ys) zs ws (~ k)
            ; (j = i1) → ++-assoc xs ys (zs ++ ws) k
            })
   ((xs ++ ys) ++ zs ++ ws))
   ◁ ++-pentagon-□ xs ys zs ws


module _ {A : Type ℓ} where

  infixr 5 _∷_
  infixr 5 _∷ʳ_

  _∷_ : A → List A → List A
  x ∷ xs = [ x ] ++ xs

  _∷ʳ_ : List A → A → List A
  xs ∷ʳ x = xs ++ [ x ]


  module Rec  {ℓb} {B : Type ℓb}
              (isGroupoidB : isGroupoid B)
              (b[] : B)
              (b[_] : A → B)
              (_b++_ : B → B → B)
              (b++ur : (b : B) → (b b++ b[]) ≡ b)
              (b++ul : (b : B) → (b[] b++ b) ≡ b)
              (b++-assoc : (bx by bz : B) → ((bx b++ by) b++ bz) ≡ (bx b++ (by b++ bz)))
              (b++-triangle : ∀ bx by →
                               Square
                                 (b++-assoc bx b[] by)
                                 refl
                                 (λ i → b++ur bx i b++ by)
                                 λ i → bx b++ b++ul by i)
              (b++-pent-diag : (bx by bz bw : B) →
                                (((bx b++ by) b++ bz) b++ bw) ≡ 
                                 (bx b++ (by b++ (bz b++ bw))))                                 
              (b++-pent-△ : (bx by bz bw : B) →
                            Square 
                                  refl
                                  (b++-pent-diag bx by bz bw)
                                  (symP (b++-assoc _ _ _))
                                  (b++-assoc _ _ _))
              (b++-pent-□ : (bx by bz bw : B) →
                             Square
                                 (b++-pent-diag bx by bz bw)
                                 (b++-assoc _ _ _)
                                 (λ i → b++-assoc bx by bz i b++ bw)
                                 λ i → bx b++ b++-assoc by bz bw (~ i))
              
              where

    f : List A → B
    f [] = b[]
    f [ a ] = b[ a ]
    f (xs ++ ys) = f xs b++ f ys
    f (++-unit-r x i) = b++ur (f x) i
    f (++-unit-l x i) = b++ul (f x) i
    f (++-assoc xs ys zs i) = b++-assoc (f xs) (f ys) (f zs) i
    f (++-triangle xs ys i j) = b++-triangle (f xs) (f ys) i j
    f (++-pentagon-diag xs ys zs ws i) = b++-pent-diag (f xs) (f ys) (f zs) (f ws) i
    f (++-pentagon-△ xs ys zs ws i j) = b++-pent-△ (f xs) (f ys) (f zs) (f ws) i j
    f (++-pentagon-□ xs ys zs ws i j) = b++-pent-□ (f xs) (f ys) (f zs) (f ws) i j
    f (trunc x y p q r s i₀ i₁ i₂) =
      isGroupoidB (f x) (f y)
                  (cong f p) (cong f q)
                  (cong (cong f) r) (cong (cong f) s) i₀ i₁ i₂


  module Elim {ℓb} {B : List A → Type ℓb}
              (isGrpB : ∀ x → isGroupoid (B x))
              (b[] : B [])
              (b[_] : ∀ a → B [ a ])
              (_b++_ : ∀ {xs ys} → B xs → B ys → B (xs ++ ys))
              (b++ur : ∀ {xs} → (b : B xs) →
                        PathP (λ i → B (++-unit-r xs i)) (b b++ b[]) b)
              (b++ul : ∀ {xs} → (b : B xs) →
                        PathP (λ i → B (++-unit-l xs i)) (b[] b++ b) b)
              (b++-assoc : ∀ {xs ys zs} → (bx : B xs) (by : B ys) (bz : B zs)
                             → PathP (λ i → B (++-assoc xs ys zs i))
                                ((bx b++ by) b++ bz)
                                 (bx b++ (by b++ bz)))
              (b++-triangle : ∀ {xs ys} → (bx : B xs)(by : B ys)
                             → SquareP (λ i j → B (++-triangle xs ys i j))
                                 (b++-assoc bx b[] by)
                                 refl
                                 (λ i → b++ur bx i b++ by)
                                 λ i → bx b++ b++ul by i)
              (b++-pent-diag : ∀ {xs ys zs ws} → (bx : B xs) (by : B ys) (bz : B zs)(bw : B ws)
                             → PathP (λ i → B (++-pentagon-diag xs ys zs ws i))
                                (((bx b++ by) b++ bz) b++ bw)
                                 (bx b++ (by b++ (bz b++ bw))))
              (b++-pent-△ : ∀ {xs ys zs ws} → (bx : B xs) (by : B ys) (bz : B zs)(bw : B ws)
                             → SquareP (λ i j → B (++-pentagon-△ xs ys zs ws i j))
                                 refl
                                  (b++-pent-diag bx by bz bw)
                                  (symP (b++-assoc _ _ _))
                                  (b++-assoc _ _ _))
              (b++-pent-□ : ∀ {xs ys zs ws} → (bx : B xs) (by : B ys) (bz : B zs)(bw : B ws)
                             → SquareP (λ i j → B (++-pentagon-□ xs ys zs ws i j))
                                 (b++-pent-diag bx by bz bw)
                                 (b++-assoc _ _ _)
                                 (λ i → b++-assoc bx by bz i b++ bw)
                                 λ i → bx b++ b++-assoc by bz bw (~ i))
              
              where

    f : ∀ x → B x
    f [] = b[]
    f [ a ] = b[ a ]
    f (xs ++ ys) = f xs b++ f ys
    f (++-unit-r x i) = b++ur (f x) i
    f (++-unit-l x i) = b++ul (f x) i
    f (++-assoc xs ys zs i) = b++-assoc (f xs) (f ys) (f zs) i
    f (++-triangle xs ys i j) = b++-triangle (f xs) (f ys) i j
    f (++-pentagon-diag xs ys zs ws i) = b++-pent-diag (f xs) (f ys) (f zs) (f ws) i
    f (++-pentagon-△ xs ys zs ws i j) = b++-pent-△ (f xs) (f ys) (f zs) (f ws) i j
    f (++-pentagon-□ xs ys zs ws i j) = b++-pent-□ (f xs) (f ys) (f zs) (f ws) i j
    f (trunc x y p q r s i₀ i₁ i₂) =
       (isOfHLevel→isOfHLevelDep (suc (suc (suc zero))) isGrpB)
            (f x) (f y)
            (cong f p) (cong f q)
            (λ i₃ i₄ → f (r i₃ i₄)) (λ i₃ i₄ → f (s i₃ i₄))
            (trunc x y p q r s) i₀ i₁ i₂


  module Elim' {ℓb} {B : List A → Type ℓb}
              (isGrpB : ∀ x → isGroupoid (B x))
              (b[] : B [])
              (b[_] : ∀ a → B [ a ])
              (_b++_ : ∀ {xs ys} → B xs → B ys → B (xs ++ ys))
              (b++ur : ∀ {xs} → (b : B xs) →
                        PathP (λ i → B (++-unit-r xs i)) (b b++ b[]) b)
              (b++ul : ∀ {xs} → (b : B xs) →
                        PathP (λ i → B (++-unit-l xs i)) (b[] b++ b) b)
              (b++-assoc : ∀ {xs ys zs} → (bx : B xs) (by : B ys) (bz : B zs)
                             → PathP (λ i → B (++-assoc xs ys zs i))
                                ((bx b++ by) b++ bz)
                                 (bx b++ (by b++ bz)))
              (b++-triangle : ∀ {xs ys} → (bx : B xs)(by : B ys)
                             → SquareP (λ i j → B (++-triangle xs ys i j))
                                 (b++-assoc bx b[] by)
                                 refl
                                 (λ i → b++ur bx i b++ by)
                                 λ i → bx b++ b++ul by i)
              (b++-pent : ∀ {xs ys zs ws} → (bx : B xs) (by : B ys) (bz : B zs)(bw : B ws)
                             → SquareP (λ i j → B (++-pentagon-□ xs ys zs ws i j))
                                 (λ i → comp (λ j → B (++-pentagon-△ xs ys zs ws j i))
                                     (λ k →
                                      λ {(i = i0) → b++-assoc (bx b++ by) bz bw (~ k)
                                       ; (i = i1) → b++-assoc bx by (bz b++ bw) k})
                                       ((bx b++ by) b++ (bz b++ bw)))
                                 (b++-assoc _ _ _)
                                 (λ i → b++-assoc bx by bz i b++ bw)
                                 λ i → bx b++ b++-assoc by bz bw (~ i))
              
              where

    f : ∀ x → B x
    f [] = b[]
    f [ a ] = b[ a ]
    f (xs ++ ys) = f xs b++ f ys
    f (++-unit-r x i) = b++ur (f x) i
    f (++-unit-l x i) = b++ul (f x) i
    f (++-assoc xs ys zs i) = b++-assoc (f xs) (f ys) (f zs) i
    f (++-triangle xs ys i j) = b++-triangle (f xs) (f ys) i j
    f (++-pentagon-diag xs ys zs ws i) = 
       comp (λ j → B (++-pentagon-△ xs ys zs ws j i))
        (λ k →
          λ {(i = i0) → b++-assoc (f xs b++ f ys) (f zs) (f ws) (~ k)
           ; (i = i1) → b++-assoc (f xs) (f ys) (f zs b++ f ws) k})
           ((f xs b++ f ys) b++ (f zs b++ f ws))
    f (++-pentagon-△ xs ys zs ws i j) =
      fill ((λ k → B (++-pentagon-△ xs ys zs ws k j)))
       (λ k →
          λ {(j = i0) → b++-assoc (f xs b++ f ys) (f zs) (f ws) (~ k)
           ; (j = i1) → b++-assoc (f xs) (f ys) (f zs b++ f ws) k})
       (inS (((f xs b++ f ys) b++ (f zs b++ f ws)))) i
    f (++-pentagon-□ xs ys zs ws i j) = b++-pent (f xs) (f ys) (f zs) (f ws) i j
    f (trunc x y p q r s i₀ i₁ i₂) =
       (isOfHLevel→isOfHLevelDep (suc (suc (suc zero))) isGrpB)
            (f x) (f y)
            (cong f p) (cong f q)
            (λ i₃ i₄ → f (r i₃ i₄)) (λ i₃ i₄ → f (s i₃ i₄))
            (trunc x y p q r s) i₀ i₁ i₂

  module ElimSet {ℓb} {B : List A → Type ℓb}
              (isSetB : ∀ x → isSet (B x))
              (b[] : B [])
              (b[_] : ∀ a → B [ a ])
              (_b++_ : ∀ {xs ys} → B xs → B ys → B (xs ++ ys))
              (b++ur : ∀ {xs} → (b : B xs) →
                        PathP (λ i → B (++-unit-r xs i)) (b b++ b[]) b)
              (b++ul : ∀ {xs} → (b : B xs) →
                        PathP (λ i → B (++-unit-l xs i)) (b[] b++ b) b)
              (b++-assoc : ∀ {xs ys zs} → (bx : B xs) (by : B ys) (bz : B zs)
                             → PathP (λ i → B (++-assoc xs ys zs i))
                                ((bx b++ by) b++ bz)
                                 (bx b++ (by b++ bz)))              
              where

    f : ∀ x → B x
    f = Elim'.f
         (λ _ → isSet→isGroupoid (isSetB _))
         b[]
         b[_]
         _b++_
         b++ur
         b++ul
         b++-assoc
         (λ _ _ → isSet→SquareP (λ i j → isSetB (++-triangle _ _ i j)) _ _ _ _ )         
         (λ _ _ _ _ → isSet→SquareP (λ i j → isSetB (++-pentagon-□ _ _ _ _ i j)) _ _ _ _ )

  module ElimProp {ℓb} {B : List A → Type ℓb}
              (isPropB : ∀ x → isProp (B x))
              (b[] : B [])
              (b[_] : ∀ a → B [ a ])
              (_b++_ : ∀ {xs ys} → B xs → B ys → B (xs ++ ys))
              where

    f : ∀ x → B x
    f = ElimSet.f
         (λ _ → isProp→isSet (isPropB _))
         b[]
         b[_]
         _b++_
         (λ _ → isProp→PathP (λ i → isPropB _) _ _)
         (λ _ → isProp→PathP (λ i → isPropB _) _ _)
         λ _ _ _ → isProp→PathP (λ i → isPropB _) _ _

  module RecSet {ℓb} {B : Type ℓb}
              (isSetB : isSet B)
              (b[] : B)
              (b[_] : A → B)
              (_b++_ : B → B → B)
              (b++ur : (b : B) → (b b++ b[]) ≡ b)
              (b++ul : (b : B) → (b[] b++ b) ≡ b)
              (b++-assoc : (bx by bz : B) → ((bx b++ by) b++ bz) ≡ (bx b++ (by b++ bz)))
              (b++-pent-diag : (bx by bz bw : B) →
                                (((bx b++ by) b++ bz) b++ bw) ≡ 
                                 (bx b++ (by b++ (bz b++ bw))))              
              where
    f : List A → B
    f [] = b[]
    f [ a ] = b[ a ]
    f (xs ++ ys) = f xs b++ f ys
    f (++-unit-r x i) = b++ur (f x) i
    f (++-unit-l x i) = b++ul (f x) i
    f (++-assoc xs ys zs i) = b++-assoc (f xs) (f ys) (f zs) i
    f (++-triangle xs ys i j) = 
      isSet→isSet' isSetB (b++-assoc (f xs) b[] (f ys)) (λ _ → f xs b++ f ys)
        (λ i → b++ur (f xs) i b++ f ys)
        (λ i → f xs b++ b++ul (f ys) i)
        i j
    f (++-pentagon-diag xs ys zs ws i) = b++-pent-diag (f xs) (f ys) (f zs) (f ws) i
    f (++-pentagon-△ xs ys zs ws i j) =
       isSet→isSet' isSetB
         (λ _ → (f xs b++ f ys) b++ (f zs b++ f ws))
         (b++-pent-diag (f xs) (f ys) (f zs) (f ws))
         (sym (b++-assoc (f xs b++ f ys) (f zs) (f ws)))
         (b++-assoc (f xs) (f ys) (f zs b++ f ws)) i j


    f (++-pentagon-□ xs ys zs ws i j) = 
          isSet→isSet' isSetB         
         (b++-pent-diag (f xs) (f ys) (f zs) (f ws))
         (b++-assoc _ _ _)
         (λ i → b++-assoc (f xs) (f ys) (f zs) i b++ f ws)
         (λ i → f xs b++ b++-assoc (f ys) (f zs) (f ws) (~ i))
         i j

    f (trunc x y p q r s i₀ i₁ i₂) = 
       (isOfHLevel→isOfHLevelDep (suc (suc (suc zero))) λ _ → isSet→isGroupoid isSetB)
            (f x) (f y)
            (cong f p) (cong f q)
            (λ i₃ i₄ → f (r i₃ i₄)) (λ i₃ i₄ → f (s i₃ i₄))
            (trunc x y p q r s) i₀ i₁ i₂




  ++-assoc-[]-l : (xs ys : List A)
            → Square
              (++-assoc [] xs ys) refl
              (cong (_++ ys) (++-unit-l xs)) (++-unit-l (xs ++ ys))

  ++-assoc-[]-l xs ys =
     compSqFacesCong (++-unit-l) λ i j →
      hcomp (λ k →
         λ { (i = i0) → hcomp (λ l →
                         λ { (k = i1) → [] ++ ++-assoc [] xs ys (l ∧ j)
                           ; (j = i1) → [] ++ ++-assoc [] xs ys l
                           ; (k = i0) → ++-pentagon-□ [] [] xs ys (~ l) j
                           }) ((++-assoc [] ([] ++ xs) ys (j ∨ k)))
           ; (i = i1) → ++-assoc [] xs ys (k ∨ j) 
           ; (j = i0) → hcomp (λ l → λ { (i = i1) → ++-assoc [] xs ys k
                                       ; (k = i1) → [] ++ (++-unit-l xs i ++ ys)
                                       ; (k = i0) → ++-triangle [] xs i (~ l) ++ ys
                                       }) (++-assoc [] (++-unit-l xs i) ys k)
           ; (j = i1) → [] ++ ++-unit-l (xs ++ ys) i
            }) (hcomp (λ k →
                   λ { (i = i0) → ++-pentagon-△ [] [] xs ys k j 
                     ; (i = i1) → ++-assoc [] xs ys (~ k ∨ j) 
                     ; (j = i0) → ++-assoc (++-unit-r [] i) xs ys (~ k)
                     ; (j = i1) → ++-triangle [] (xs ++ ys) i k
                      }) (++-unit-r [] i ++ xs ++ ys))

  ++-assoc-[]-r : (xs ys : List A)
            → Square
              (++-assoc xs ys []) refl
              (++-unit-r (xs ++ ys)) (cong (xs ++_) (++-unit-r ys))
  ++-assoc-[]-r xs ys =
    compSqFacesCong ++-unit-r λ i j →
      hcomp (λ k →
         λ { (i = i0) →  hcomp (λ l →
                         λ { (k = i1) → ++-assoc xs ys [] (~ l ∨ j) ++ []
                           ; (j = i0) → ++-assoc xs ys [] (~ l) ++ []
                           ; (k = i0) → ++-pentagon-□ xs ys [] [] (~ l) j
                           }) (++-assoc xs (ys ++ []) [] (j ∧ ~ k))
           ; (i = i1) → ++-assoc xs ys [] (~ k ∧ j) 
           ; (j = i1) →  hcomp (λ l →
                           λ { (i = i1) → ++-assoc xs ys [] (~ k)
                             ; (k = i1) → (xs ++ ++-unit-r ys i) ++ []
                             ; (k = i0) → xs ++ ++-triangle ys [] i (l)
                             }) (++-assoc xs (++-unit-r ys i) [] (~ k))
           ; (j = i0) → ++-unit-r (xs ++ ys) i ++ []
            }) (hcomp (λ k →
                   λ { (i = i0) → ++-pentagon-△ xs ys [] [] k j 
                     ; (i = i1) → ++-assoc xs ys [] (k ∧ j) 
                     ; (j = i1) → ++-assoc xs ys (++-unit-l [] i) (k)
                     ; (j = i0) → ++-triangle (xs ++ ys) [] i (~ k)
                      }) ((xs ++ ys) ++ ++-unit-l [] i))


  ++-unit-lr[] : ++-unit-l {A = A} [] ≡ ++-unit-r [] 
  ++-unit-lr[] =
     compSqFacesCong ++-unit-r
      λ i j → hcomp (λ k →
            λ { (i = i0) → ++-assoc-[]-l [] [] j (~ k) 
              ; (i = i1) → ++-triangle [] [] j (~ k) 
              ; (j = i0) → ++-assoc [] [] [] (~ k)
              ; (j = i1) → [] ++ []
               })
     ((lem-pqpr λ i j → ++-unit-l (++-unit-l [] (~ j)) (~ i)) i (~ j))


  length : List A → ℕ
  length = RecSet.f isSetℕ 
    zero
    (λ _ → suc zero)
    _+_
    +-zero
    (λ _ → refl)
    (λ bx by bz → sym (+-assoc bx by bz))
    λ bx by bz bw → sym (+-assoc (bx + by) bz bw) ∙∙ refl ∙∙ sym (+-assoc bx by (bz + bw))


  rev : List A → List A
  rev [] = []
  rev [ x ] = [ x ]
  rev (x ++ y) = rev y ++ rev x
  rev (++-unit-r x i) = ++-unit-l (rev x) i
  rev (++-unit-l x i) = ++-unit-r (rev x) i
  rev (++-assoc x y z i) = ++-assoc (rev z) (rev y) (rev x) (~ i)
  rev (++-triangle x y i j) = ++-triangle (rev y) (rev x) i (~ j)
  rev (++-pentagon-diag x y z w i) = ++-pentagon-diag (rev w) (rev z) (rev y) (rev x) (~ i)
  rev (++-pentagon-△ x y z w i j) = ++-pentagon-△ (rev w) (rev z) (rev y) (rev x) i (~ j)
  rev (++-pentagon-□ x y z w i j) = ++-pentagon-□ (rev w) (rev z) (rev y) (rev x) i (~ j)
  rev (trunc x y p q r s i₀ i₁ i₂) =
    trunc (rev x) (rev y) (cong rev p) (cong rev q) (cong (cong rev) r) (cong (cong rev) s) i₀ i₁ i₂


  rev-rev : ∀ x → rev (rev x) ≡ x
  rev-rev [] = refl
  rev-rev [ x ] = refl
  rev-rev (x ++ y) = cong₂ _++_ (rev-rev x) (rev-rev y)
  rev-rev (++-unit-r x i) j = ++-unit-r (rev-rev x j) i
  rev-rev (++-unit-l x i) j = ++-unit-l (rev-rev x j) i
  rev-rev (++-assoc x y z i) j = ++-assoc (rev-rev x j) (rev-rev y j) (rev-rev z j) i
  rev-rev (++-triangle x y i j) k = (++-triangle (rev-rev x k) (rev-rev y k) i j)
  rev-rev (++-pentagon-diag x y z w i) k =
     ++-pentagon-diag (rev-rev x k) (rev-rev y k) (rev-rev z k) (rev-rev w k) i
  rev-rev (++-pentagon-△ x y z w i j) k =
     ++-pentagon-△ (rev-rev x k) (rev-rev y k) (rev-rev z k) (rev-rev w k) i j
  rev-rev (++-pentagon-□ x y z w i j) k =
     ++-pentagon-□ (rev-rev x k) (rev-rev y k) (rev-rev z k) (rev-rev w k) i j
  rev-rev (trunc x y p q r s i₀ i₁ i₂) k =
     (trunc (rev-rev x k) (rev-rev y k)
             (λ j → (rev-rev (p j) k)) (λ j → (rev-rev (q j) k))
             (λ j j' → (rev-rev (r j j') k)) (λ j j' → (rev-rev (s j j') k))
             i₀ i₁ i₂)

  Iso-rev : Iso (List A) (List A)
  Iso.fun Iso-rev = rev
  Iso.inv Iso-rev = rev
  Iso.rightInv Iso-rev = rev-rev
  Iso.leftInv Iso-rev = rev-rev
