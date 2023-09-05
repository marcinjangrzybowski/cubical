{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.NormalForm where

-- open import Cubical.HITs.FreeGroup.Base renaming (assoc to ·assoc)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

-- open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

import Cubical.Functions.Logic as L

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/₂_ ; [_] to [_]/)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base


private
  variable
    ℓ : Level

module _ {A : Type ℓ} where


  ℙpb : ℙ A → (A → A → Type ℓ) → ℙ A  
  ℙpb p r x = ∃ _ (λ x' → r x x' × ⟨ p x' ⟩) , squash₁


module NormalForm {A : Type ℓ} where


 IsRedex : Bool × A → Bool × A → Type ℓ
 IsRedex (b , x) (b' , x') = (b ≡ not b') × (x ≡ x')

 WillReduce : Bool → A → (xs : List (Bool × A)) → Type ℓ
 WillReduce _ _ [] = ⊥* 
 WillReduce b x (h ∷ _) = IsRedex (b , x) h

 IsNormalised : List (Bool × A) → Type ℓ
 IsNormalised [] = Unit*
 IsNormalised ((b , x) ∷ xs) = (¬ WillReduce b x xs)  × IsNormalised xs


 -- infixr 5 _∷↔_ 

 -- Red : (R : Type ℓ) → Type ℓ
 -- Red R = ((Bool × A) × Maybe (Bool × R))

 data Red : Type ℓ
 data Red[] : Type ℓ

 data Red where
  red· ·red : Red[] → Red
  ·A : (Bool × A) → Red

 data Red[] where
   ↔ : Red → Red[]
   _∷↔_ : Red → Red[] → Red[]

 -- red[]→List : Red[] → List Red
 -- red[]→List (↔ x) = [ x ]
 -- red[]→List (x ∷↔ xs) = x ∷ red[]→List xs

 evRed : Red → List (Bool × A) → List (Bool × A)
 evRed[] : Red[] → List (Bool × A)

 evRed (red· x) xs = evRed[] x ++ xs
 evRed (·red x) xs = xs ++ evRed[] x 
 evRed (·A (b , a)) xs = (b , a) ∷ (xs ∷ʳ (not b , a))
 evRed[] (↔ x) = evRed x []
 evRed[] (x ∷↔ xs) = evRed x (evRed[] xs)

 RED = (Bool × A) × List Red

 evRED : RED → List (Bool × A)
 evRED (x , y) = evRed (·A x) (flatten (Li.map (flip evRed []) y))


 infix 3 [_]_↓'_ [_]_∷↓'_ [_]_↓∷'_ _↓∷Fst_


 _↓∷Fst_ : List (Bool × A) → List (Bool × A) → Type ℓ 
 xs ↓∷Fst ys = Σ (_ × _)  λ (redL , xsR) → ((evRED redL) ++ xsR ≡ xs)

 -- ↓∷Snd : (xs ys : List (Bool × A)) → xs ↓∷Fst ys → Type ℓ
 -- ↓∷Snd = {!!}
 -- ↓∷Fst  = Σ (_ × _)  λ (redL , xsR) → ((evRED redL) ++ xsR ≡ xs)
 
 [_]_↓∷'_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
 [_]_↓'_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
 [_]_∷↓'_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ

 [ [] ] xs ↓∷' ys = ⊥*
 [ x ∷ tx ] xs ↓∷' ys =
   Σ (xs ↓∷Fst ys)
      λ q → [ tx ] snd (fst q) ↓' ys 
 

 
 [ _ ] [] ∷↓' [] = Unit*
 [ _ ] [] ∷↓' _ ∷ _ = ⊥*
 [ _ ] _ ∷ _ ∷↓' [] = ⊥*
 [ [] ] x₁ ∷ xs ∷↓' y ∷ ys = ⊥*
 [ _ ∷ tx ] x ∷ xs ∷↓' y ∷ ys =
    (x ≡ y) × ([ tx ] xs ↓' ys)
 
 [ tx ] xs ↓' ys =
   ([ tx ] xs ↓∷' ys) ⊎.⊎
     ([ tx ] xs ∷↓' ys)  

 ↓∷'→len≥2 : ∀ ts xs ys → [ ts ] xs ↓∷' ys → 2 ≤ length xs  
 ↓∷'→len≥2 (_ ∷ _) xs ys (((redL , xsR) , p) , _) =
   let p' =  cong suc (cong (_+ length xsR)
              (sym (+-suc _ _) ∙ sym (length++ (flatten (Li.map (λ x₁ → evRed x₁ []) (snd redL)))
                [ (not (fst (fst redL)) , snd (fst redL)) ])) ∙ sym (length++
             ((flatten (Li.map (λ x₁ → evRed x₁ []) (snd redL)) ++
                (not (fst (fst redL)) , snd (fst redL)) ∷ [])
                ) xsR)) ∙ cong length p
   in subst (2 ≤_) p' tt   
 
 open BinaryRelation

 -- [[]]↓'→⊥ : ∀ xs ys → [ [] ] xs ↓' ys → xs ≡ ys
 -- [[]]↓'→⊥ [] [] (inr x) = {!!}
 -- [[]]↓'→⊥ (x₁ ∷ xs) [] (inr ())
 -- [[]]↓'→⊥ (x₁ ∷ xs) (x₂ ∷ ys) (inr ())

 -- isTrans-↓∷' : ∀ tx → isTrans [ tx ]_↓∷'_
 -- isTrans-∷↓' : ∀ tx → isTrans [ tx ]_∷↓'_
 isTrans-↓' : ∀ tx tx' → ∀ a b c →
                       ([ tx ] a ↓' b) →
                       ([ tx' ] b ↓' c) →
                       ([ tx ] a ↓' c)

 -- isTrans-↓∷' (x ∷ tx) xs ys zs p q = {!!}


 isTrans-∷↓'-↓∷'-lem : ∀ tx → ∀ a x bL bR →
                       ([ tx ] (x ∷ a) ∷↓' (evRED (x , bL)) ++ bR) →
                       Σ (List Red × List (Bool × A))
                        λ (aL , aR) →
                          {!!} × ([ tx ] aR ↓' bR )
 isTrans-∷↓'-↓∷'-lem = {!!}
 
 isTrans-∷↓'-↓∷' : ∀ tx tx' → ∀ a x bL bR c →
                       ([ tx ] (x ∷ a) ∷↓' (evRED (x , bL)) ++ bR) →
                       ([ tx' ] (evRED (x , bL)) ++ bR ↓∷' c) →
                       ([ tx ] (x ∷ a) ↓∷' c)
 isTrans-∷↓'-↓∷' tx tx' a x bL bR c = {!!}
 -- tx tx' (x ∷ a) (fst₁ , []) bR [] p q = {!!}
 -- isTrans-∷↓'-↓∷' tx tx' (x ∷ a) (fst₁ , []) bR (x₁ ∷ c) p q = {!!}
 -- isTrans-∷↓'-↓∷' tx tx' (x₁ ∷ a) (fst₁ , x ∷ snd₁) bR c p q = {!c!}

 isTrans-↓' tx [] a b c (inr x) (inl ())
 isTrans-↓' tx tx'@(_ ∷ _) a [] c (inr x) (inl x'@(((bL , bR) , p) , q)) =
   ⊥.rec (¬cons≡nil p)
 isTrans-↓' tx@(_ ∷ _) tx'@(_ ∷ _) (ha ∷ a) (x ∷ b) c (inr u) (inl x'@((((_ , bL) , bR) , p) , q)) =
  let pp = sym p ∙ cong (λ h → evRED (h , bL) ++ bR)
             (cons-inj₁ p ∙ sym (fst u))
  in inl (isTrans-∷↓'-↓∷' tx tx' a ha bL bR c
     (subst ([ tx ] (ha ∷ a) ∷↓'_) pp u)
     (subst ( [ tx' ]_↓∷' c) pp x')
    )

 isTrans-↓' tx tx' [] [] [] (inr x) (inr _) = inr _
 isTrans-↓' (_ ∷ tx) [] (x₂ ∷ xs) (x₃ ∷ ys) (x₄ ∷ zs) (inr (p , q)) (inr ())
 isTrans-↓' (_ ∷ tx) (_ ∷ tx') (x₂ ∷ xs) (x₃ ∷ ys) (x₄ ∷ zs) (inr (p , q)) (inr (p' , q'))  = inr (p ∙ p' , isTrans-↓' tx tx' xs ys zs q q')
 isTrans-↓' (_ ∷ tx) tx' xs ys zs (inl ((((rL , rs) , w) , q))) v =
  let u = isTrans-↓' tx tx' rs ys zs q v
  in inl (((rL , rs) , w) , u)


 -- infix 3 _↓_ _∷↓_ _↓∷_

 _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ 
 xs ↓ ys = [ xs ] xs ↓' ys

 -- -- _↓∷_ : List (Bool × A) → List (Bool × A) → Type ℓ
 -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
 -- -- _∷↓_ : List (Bool × A) → List (Bool × A) → Type ℓ

 -- ↓∷H : ∀ n → (l : List (Bool × A)) → length l ≤ n  → List (Bool × A) → Type ℓ
 -- ↓H : ∀ n → (l : List (Bool × A)) → length l ≤ n  → List (Bool × A) → Type ℓ

 -- ↓∷H zero _ _ _ = ⊥*
 -- ↓∷H (suc n) xs l≤sn xs'  =
 --      Σ (_ × _)  λ (redL , xsR) →
 --     (((evRED redL) ++ xsR ≡ xs) ×
 --       (↓∷H n {!!} {!!} {!!} ⊎ ↓H n xsR {!!} xs') )

 -- ↓H n l x x₁ =
 --   {!!}


 -- xs ↓∷ xs' = ↓∷H (length xs) xs (≤-refl (length xs)) xs'
 --   -- Σ (_ × _)  λ (redL , xsR) →
 --   --   (((evRED redL) ++ xsR ≡ xs) × {!? ↓ ?!} )
 
 -- [] ∷↓ [] = Unit*
 -- [] ∷↓ _ ∷ _ = ⊥*
 -- _ ∷ _ ∷↓ [] = ⊥*
 -- x ∷ xs ∷↓ x' ∷ xs' = (x ≡ x') × (xs ↓ xs')
 
 -- xs ↓ xs' = (xs ↓∷ xs') ⊎ (xs ∷↓ xs')

 -- -- module FG (freeGroupGroup : Group ℓ)
 -- --           (η : A → ⟨ freeGroupGroup ⟩) where 

 -- --  FreeGroup = ⟨ freeGroupGroup ⟩

 -- --  open GroupStr (snd freeGroupGroup)

 -- --  open GroupTheory freeGroupGroup

 -- --  η* : Bool × A → FreeGroup
 -- --  η* (b , a) = (if b then idfun _ else inv) (η a)

 -- --  fromList' : FreeGroup → List (Bool × A) → FreeGroup
 -- --  fromList' = foldr (_·_ ∘ η*) 

 -- --  fromList : List (Bool × A) → FreeGroup
 -- --  fromList = fromList' 1g

 -- --  fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
 -- --                            fromList xs · fromList ys
 -- --  fromList· [] _ = sym (·IdL _)
 -- --  fromList· (_ ∷ xs) _ =
 -- --   cong (_ ·_) (fromList· xs _) ∙
 -- --    ·Assoc _ _ _

 -- --  redex-ε-η* : ∀ x x' → IsRedex x x' → η* x · η* x' ≡ 1g
 -- --  redex-ε-η* (false , _) (false , _) (p , _) = ⊥.rec (false≢true p)
 -- --  redex-ε-η* (false , x) (true , _) (_ , q) = 
 -- --    cong (inv (η x) ·_) (cong (η) (sym q)) ∙ ·InvL (η x) 
 -- --  redex-ε-η* (true , x) (false , _) (_ , q) =
 -- --    cong (η x ·_) (cong (inv ∘ η) (sym q)) ∙ ·InvR (η x)
 -- --  redex-ε-η* (true , _) (true , _) (p , _) = ⊥.rec (true≢false p)


 -- -- -- infix 3 _↓_ _∷↓_ _↓∷_

 -- -- -- _↓∷_ : List (Bool × A) → List (Bool × A) → Type ℓ
 -- -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
 -- -- -- _∷↓_ : List (Bool × A) → List (Bool × A) → Type ℓ

 -- -- -- [] ↓∷ xs' = ⊥*
 -- -- -- (x ∷ []) ↓∷ xs' = ⊥*
 -- -- -- (x ∷ x' ∷ xs) ↓∷ xs' = IsRedex x x' × (xs ↓ xs')

 -- -- -- [] ∷↓ [] = Unit*
 -- -- -- [] ∷↓ _ ∷ _ = ⊥*
 -- -- -- _ ∷ _ ∷↓ [] = ⊥*
 -- -- -- x ∷ xs ∷↓ x' ∷ xs' = (x ≡ x') × (xs ↓ xs')

 -- -- -- xs ↓ xs' = (xs ↓∷ xs') ⊎ (xs ∷↓ xs')


 -- -- -- ∷↓refl : ∀ x → x ∷↓ x
 -- -- -- ↓refl : ∀ x → x ↓ x

 -- -- -- ∷↓refl [] = tt*
 -- -- -- ∷↓refl (_ ∷ xs) = refl , ↓refl xs
 
 -- -- -- ↓refl x = ⊎.inr (∷↓refl x)


 -- -- -- -- ∷↓trans : ∀ x y z → x ∷↓ y → y ∷↓ z → x ∷↓ z
 -- -- -- -- ∷↓trans = {!!}
 
 -- -- -- ↓trans-∷↓-↓∷ :  ∀ x y z → x ∷↓ y → y ↓∷ z → x ↓ z

 -- -- -- ↓trans : ∀ x y z → x ↓ y → y ↓ z → x ↓ z
 -- -- -- ↓trans x y z (inr p) (inl q) = {!!}
 -- -- -- -- ↓trans (x ∷ []) (x' ∷ x₂ ∷ ys) zs (inr (fst₁ , inl ())) (inl x₁)
 -- -- -- -- ↓trans (x ∷ []) (x' ∷ x₂ ∷ ys) zs (inr (fst₁ , inr ())) (inl x₁)
 -- -- -- -- ↓trans (x ∷ x₃ ∷ x₄ ∷ xs) (x' ∷ x₂ ∷ ys) zs (inr (p , inl x₁)) (inl (q , r)) =    {!!}
 -- -- -- -- ↓trans (x ∷ x₃ ∷ xs) (x' ∷ x₂ ∷ ys) zs (inr (p , inr (p' , p''))) (inl (q , r)) =
 -- -- -- --   inl (subst2 IsRedex {!!} {!!} q
 -- -- -- --     , (↓trans _ _ _ p'' r))
 
 -- -- -- ↓trans [] [] _ (inr _) (inr x) = inr x
    
 -- -- -- ↓trans (x ∷ xs) (x' ∷ ys) [] (inr p) (inr ())
 -- -- -- ↓trans (x ∷ xs) (x' ∷ ys) (z' ∷ zs) (inr (p , q)) (inr (p' , q')) =
 -- -- --   inr (p ∙ p' , ↓trans _ _ _ q q' )
 
 -- -- -- ↓trans (x ∷ x₂ ∷ x₃) _ _ (inl (p , q)) r =
 -- -- --    inl (p , ↓trans _ _ _ q r)

 -- -- -- ↓trans-∷↓-↓∷ (x ∷ []) (x₃ ∷ x₄ ∷ y) z (fst₁ , inl ()) x₂
 -- -- -- ↓trans-∷↓-↓∷ (x ∷ []) (x₃ ∷ x₄ ∷ y) z (fst₁ , inr ()) x₂
 -- -- -- ↓trans-∷↓-↓∷ (x ∷ y ∷ xs) (x' ∷ y' ∷ ys) z (p , inr (p' , q')) (r , s) =
 -- -- --    inl (subst2 IsRedex (sym p) (sym p') r ,
 -- -- --        ↓trans _ _ _ q' s)
 -- -- -- ↓trans-∷↓-↓∷ (x ∷ y ∷ u ∷ xs) (x' ∷ y' ∷ ys) z (p , inl (r' , s')) (r , s) =
 -- -- --   inl (subst2 IsRedex (sym p) {!!} r ,
 -- -- --     {!!} )
 
 -- -- -- -- ↓→≤length : ∀ xs ys → xs ↓ ys → length ys ≤ length xs
 -- -- -- -- ↓∷→<length : ∀ xs ys → xs ↓∷ ys → length ys < length xs
 -- -- -- -- ∷↓→≤length : ∀ xs ys → xs ∷↓ ys → length ys ≤ length xs

 -- -- -- -- ∷↓→≤length [] [] x = tt
 -- -- -- -- ∷↓→≤length (x₁ ∷ xs) (x₂ ∷ ys) x = ↓→≤length xs ys (snd x)
 -- -- -- -- ↓∷→<length (x₁ ∷ x₂ ∷ xs) ys x =
 -- -- -- --   <-weaken {length ys} (↓→≤length xs ys (snd x))
 -- -- -- -- ↓→≤length xs ys = ⊎.rec
 -- -- -- --   (<-weaken {length ys} ∘ ↓∷→<length xs ys)
 -- -- -- --   (∷↓→≤length xs ys)


 -- -- -- -- ↓∷asym : ∀ xs ys → xs ↓∷ ys → ys ↓∷ xs → ⊥
 -- -- -- -- ↓∷asym xs ys p p' =
 -- -- -- --  <-asym {length ys} (↓∷→<length xs ys p) (↓∷→<length ys xs p')

 -- -- -- -- ∷↓antisym : ∀ x y → x ∷↓ y → y ∷↓ x → x ≡ y
 -- -- -- -- ↓antisym : ∀ x y → x ↓ y → y ↓ x → x ≡ y


 -- -- -- -- ∷↓antisym [] [] p q = refl
 -- -- -- -- ∷↓antisym (_ ∷ xs) (_ ∷ ys) (p , q) (p' , q') = 
 -- -- -- --   cong₂ _∷_ p (↓antisym xs ys q q')


 -- -- -- -- ↓antisym xs ys (inl x) (inl x₁) = ⊥.rec (↓∷asym _ _ x x₁)
 -- -- -- -- ↓antisym xs ys (inl x) (inr x₁) = {!!}
 -- -- -- -- ↓antisym xs ys (inr x) (inl x₁) = {!!}
 -- -- -- -- ↓antisym xs ys (inr x) (inr x₁) = ∷↓antisym xs ys x x₁

 -- -- -- -- _↙_↘_ : List (Bool × A) → List (Bool × A) → List (Bool × A) → Type ℓ
 -- -- -- -- xs ↙ zs ↘ ys = (zs ↓ xs) × (zs ↓ ys)

 -- -- -- -- _↙↘_ : List (Bool × A) → List (Bool × A) → Type ℓ
 -- -- -- -- xs ↙↘ ys = Σ _ (xs ↙_↘ ys)

 -- -- -- -- ↙↘sym : ∀ x y → x ↙↘ y → y ↙↘ x
 -- -- -- -- ↙↘sym x y = map-snd λ (x , y) → y , x

 -- -- -- -- ↙↘refl : ∀ x → x ↙↘ x
 -- -- -- -- ↙↘refl = λ x → x , ↓refl x , ↓refl x

 -- -- -- -- ↘↙→↙↘ : ∀ x y z → x ↓ z → y ↓ z → x ↙↘ y
 -- -- -- -- ↘↙→↙↘ = {!!}
 
 -- -- -- -- ↙↘trans : ∀ x y z → x ↙↘ y → y ↙↘ z → x ↙↘ z
 -- -- -- -- ↙↘trans x y z (x' , p , q) (z' , r , s) =
 -- -- -- --  let (y' , p' , q') = ↘↙→↙↘ x' z' y q r
 -- -- -- --  in y' , (↓trans y' x' x p' p  , ↓trans y' z' z q' s)
 
 -- -- -- -- -- -- -- -- open BinaryRelation _↓_

 -- -- -- -- -- -- -- -- ↓EquivRel : isEquivRel
 -- -- -- -- -- -- -- -- isEquivRel.reflexive ↓EquivRel = ↓refl
 -- -- -- -- -- -- -- -- isEquivRel.symmetric ↓EquivRel = ↓sym
 -- -- -- -- -- -- -- -- isEquivRel.transitive ↓EquivRel = {!!}

 -- -- -- -- -- -- -- -- -- _↓∷_ : List (Bool × A) → List (Bool × A) → Type ℓ
 -- -- -- -- -- -- -- -- -- [] ↓∷ xs' = ⊥*
 -- -- -- -- -- -- -- -- -- (x ∷ []) ↓∷ xs' = ⊥*
 -- -- -- -- -- -- -- -- -- (x ∷ x' ∷ xs) ↓∷ xs' = IsRedex x x' × (xs ≡ xs')
 

 -- -- -- -- -- -- -- -- -- _↓_ : List (Bool × A) → List (Bool × A) → Type ℓ
 -- -- -- -- -- -- -- -- -- [] ↓ xs' = ⊥*
 -- -- -- -- -- -- -- -- -- (x ∷ xs) ↓ [] = (x ∷ xs) ↓∷ []
 -- -- -- -- -- -- -- -- -- (x ∷ xs) ↓ (x' ∷ xs') =
 -- -- -- -- -- -- -- -- --     ((x ∷ xs) ↓∷ (x' ∷ xs'))
 -- -- -- -- -- -- -- -- --   ⊎ ((x ≡ x') × (xs ↓ xs'))

 -- -- -- -- -- -- -- -- -- redex∷↓ : ∀ x x' xs → IsRedex x x' → x ∷ x' ∷ xs ↓ xs
 -- -- -- -- -- -- -- -- -- redex∷↓ x x' [] p = p , refl
 -- -- -- -- -- -- -- -- -- redex∷↓ x x' (x₁ ∷ xs) p = inl (p , refl)

 -- -- -- -- -- -- -- -- -- ↓∷++ : ∀ {a b x x'} c → (x ∷ a) ↓∷ (x' ∷ b) → (x ∷ a ++ c) ↓∷ (x' ∷ b ++ c)
 -- -- -- -- -- -- -- -- -- ↓∷++ {x₁ ∷ []} c (_ , q) = ⊥.rec (¬nil≡cons q)
 -- -- -- -- -- -- -- -- -- ↓∷++ {x₁ ∷ x₂ ∷ a} c = map-snd (cong (_++ c))
 
 -- -- -- -- -- -- -- -- -- ++L↓ : ∀ a b c → a ↓ b → a ++ c ↓ b ++ c
 -- -- -- -- -- -- -- -- -- ++L↓ (x₁ ∷ a) (x₂ ∷ b) c =
 -- -- -- -- -- -- -- -- --  ⊎.map (↓∷++ c) (map-snd (++L↓ a b c))
 -- -- -- -- -- -- -- -- -- ++L↓ (x ∷ x' ∷ []) [] xs (p , _) = redex∷↓ x x' xs p 
 -- -- -- -- -- -- -- -- -- ++L↓ (x₁ ∷ x₂ ∷ x₃ ∷ a) [] c (_ , q) = ⊥.rec (¬cons≡nil q)

 -- -- -- -- -- -- -- -- -- ++R↓ : ∀ a b c → b ↓ c → a ++ b ↓ a ++ c
 -- -- -- -- -- -- -- -- -- ++R↓ [] b c p = p
 -- -- -- -- -- -- -- -- -- ++R↓ (x ∷ a) b c p = inr (refl , ++R↓ a b c p)

 -- -- -- -- -- -- -- -- -- List/↓ : Type ℓ
 -- -- -- -- -- -- -- -- -- List/↓ = _ /₂ _↓_


 -- -- -- -- -- -- -- -- -- module _ (isSetA : isSet A) where

 -- -- -- -- -- -- -- -- --  IsPropIsNormalised : ∀ x → isProp (IsNormalised x)
 -- -- -- -- -- -- -- -- --  IsPropIsNormalised = {!!}

 -- -- -- -- -- -- -- -- --  𝑵 : ℙ (List (Bool × A)) 
 -- -- -- -- -- -- -- -- --  𝑵 x = IsNormalised x , IsPropIsNormalised x

 -- -- -- -- -- -- -- -- --  isSet[𝟚×A] : isSet _
 -- -- -- -- -- -- -- -- --  isSet[𝟚×A] = isOfHLevelList 0 (isSet× 𝟚.isSetBool isSetA)


 -- -- -- -- -- -- -- -- --  ηInj : ∀ a a' → Path List/↓ [ [ (true , a) ] ]/ [ [ (true , a') ] ]/ →
 -- -- -- -- -- -- -- -- --             a ≡ a' 
 -- -- -- -- -- -- -- -- --  ηInj a a' = PT.rec (isSetA _ _)
 -- -- -- -- -- -- -- -- --     {!!} ∘' Iso.fun (SQ.TC.IsoTcTc' _↓_ _ _) 
 -- -- -- -- -- -- -- -- --   where
 -- -- -- -- -- -- -- -- --    w : ∀ a a' → TC.tc _↓_ ((true , a) ∷ []) ((true , a') ∷ []) → a ≡ a'
 -- -- -- -- -- -- -- -- --    w a a' (TC.here (inl ()))
 -- -- -- -- -- -- -- -- --    w a a' (TC.here (inr ()))
 -- -- -- -- -- -- -- -- --    w a a' (TC.there [] x x₁) = {!!}
 -- -- -- -- -- -- -- -- --    w a a' (TC.there ((false , a'') ∷ []) x x₁) =
 -- -- -- -- -- -- -- -- --      {!!}
 -- -- -- -- -- -- -- -- --    w a a' (TC.there ((true , a'') ∷ []) x x₁) =
 -- -- -- -- -- -- -- -- --      w _ _ x ∙ w _ _ x₁
 -- -- -- -- -- -- -- -- --    w a a' (TC.there (x₂ ∷ x₃ ∷ a'') x x₁) = {!!}
      
 -- -- -- -- -- -- -- -- --    w a a' (TC.tcsym x) = sym (w a' a x)
 -- -- -- -- -- -- -- -- --    w a a' (TC.tcrefl x) = cong snd (cons-inj₁ x)
    
 -- -- -- -- -- -- -- -- -- -- List/↓· : List/↓ → List/↓ → List/↓
 -- -- -- -- -- -- -- -- -- -- List/↓· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
 -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++L↓ a b c))
 -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++R↓ a b c))

 -- -- -- -- -- -- -- -- -- -- -- -- List/↓ : List/↓ → List/↓ → List/↓
 -- -- -- -- -- -- -- -- -- -- -- -- List/↓· =  SQ.rec2 squash/ (λ a b → SQ.[ a ++ b ])
 -- -- -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++L↓ a b c))
 -- -- -- -- -- -- -- -- -- -- -- --    (λ a b c → eq/ _ _ ∘ (++R↓ a b c))


 -- -- -- -- -- -- -- -- -- -- -- List/↓Group : GroupStr List/↓
 -- -- -- -- -- -- -- -- -- -- -- GroupStr.1g List/↓Group = SQ.[ [] ]
 -- -- -- -- -- -- -- -- -- -- -- GroupStr._·_ List/↓Group = List/↓·

 -- -- -- -- -- -- -- -- -- -- -- GroupStr.inv List/↓Group =
 -- -- -- -- -- -- -- -- -- -- --   SQ.rec squash/ (SQ.[_] ∘ rev)
 -- -- -- -- -- -- -- -- -- -- --    {!!}
 -- -- -- -- -- -- -- -- -- -- -- GroupStr.isGroup List/↓Group = {!!}


 -- -- -- -- -- -- -- -- -- -- module FG (freeGroupGroup : Group ℓ)
 -- -- -- -- -- -- -- -- -- --           (η : A → ⟨ freeGroupGroup ⟩) where 

 -- -- -- -- -- -- -- -- -- --  FreeGroup = ⟨ freeGroupGroup ⟩

 -- -- -- -- -- -- -- -- -- --  open GroupStr (snd freeGroupGroup)

 -- -- -- -- -- -- -- -- -- --  open GroupTheory freeGroupGroup

 -- -- -- -- -- -- -- -- -- --  η* : Bool × A → FreeGroup
 -- -- -- -- -- -- -- -- -- --  η* (b , a) = (if b then idfun _ else inv) (η a)

 -- -- -- -- -- -- -- -- -- --  fromList' : FreeGroup → List (Bool × A) → FreeGroup
 -- -- -- -- -- -- -- -- -- --  fromList' = foldr (_·_ ∘ η*) 

 -- -- -- -- -- -- -- -- -- --  fromList : List (Bool × A) → FreeGroup
 -- -- -- -- -- -- -- -- -- --  fromList = fromList' 1g

 -- -- -- -- -- -- -- -- -- --  fromList· : ∀ xs ys → fromList (xs ++ ys) ≡
 -- -- -- -- -- -- -- -- -- --                            fromList xs · fromList ys
 -- -- -- -- -- -- -- -- -- --  fromList· [] _ = sym (·IdL _)
 -- -- -- -- -- -- -- -- -- --  fromList· (_ ∷ xs) _ =
 -- -- -- -- -- -- -- -- -- --   cong (_ ·_) (fromList· xs _) ∙
 -- -- -- -- -- -- -- -- -- --    ·Assoc _ _ _

 -- -- -- -- -- -- -- -- -- --  redex-ε-η* : ∀ x x' → IsRedex x x' → η* x · η* x' ≡ 1g
 -- -- -- -- -- -- -- -- -- --  redex-ε-η* (false , _) (false , _) (p , _) = ⊥.rec (false≢true p)
 -- -- -- -- -- -- -- -- -- --  redex-ε-η* (false , x) (true , _) (_ , q) = 
 -- -- -- -- -- -- -- -- -- --    cong (inv (η x) ·_) (cong (η) (sym q)) ∙ ·InvL (η x) 
 -- -- -- -- -- -- -- -- -- --  redex-ε-η* (true , x) (false , _) (_ , q) =
 -- -- -- -- -- -- -- -- -- --    cong (η x ·_) (cong (inv ∘ η) (sym q)) ∙ ·InvR (η x)
 -- -- -- -- -- -- -- -- -- --  redex-ε-η* (true , _) (true , _) (p , _) = ⊥.rec (true≢false p)

 -- -- -- -- -- -- -- -- -- --  -- 𝑵𝑭 : ⟨ freeGroupGroup ⟩ → ℙ (List (Bool × A))
 -- -- -- -- -- -- -- -- -- --  -- 𝑵𝑭 a l = ((fromList l ≡ a) , is-set _ _) L.⊓
 -- -- -- -- -- -- -- -- -- --  --             𝑵 l
 -- -- -- -- -- -- -- -- -- --  -- NF : ⟨ freeGroupGroup ⟩ → Type ℓ
 -- -- -- -- -- -- -- -- -- --  -- NF a = ∃ (List (Bool × A))
 -- -- -- -- -- -- -- -- -- --  --   λ l → (fromList l ≡ a)
 -- -- -- -- -- -- -- -- -- --  --     × IsNormalised l 

 -- -- -- -- -- -- -- -- -- -- module FGAlt where
 -- -- -- -- -- -- -- -- -- --  open import Cubical.HITs.FreeGroup.Alt 
 -- -- -- -- -- -- -- -- -- --  open FG (freeGroupGroup A) η

 -- -- -- -- -- -- -- -- -- --  -- hh : ∀ x b xs → ∀ l → {!NonEmpty (NF ((x , b) ∷ l)) → 
 -- -- -- -- -- -- -- -- -- --  --          !}
 -- -- -- -- -- -- -- -- -- --  -- hh = {!!}

 -- -- -- -- -- -- -- -- -- -- --   non∅NF : ∀ x → NonEmpty (NF x) 
 -- -- -- -- -- -- -- -- -- -- --   non∅NF = ElimProp.go w
 -- -- -- -- -- -- -- -- -- -- --    where
 -- -- -- -- -- -- -- -- -- -- --    open ElimProp
 -- -- -- -- -- -- -- -- -- -- --    w : ElimProp _
 -- -- -- -- -- -- -- -- -- -- --    εB (elim₁ w) q = q ∣ [] , refl , tt* ∣₁
 -- -- -- -- -- -- -- -- -- -- --    ∷B (elim₁ w) false a x x₁ = x₁ {!!}
 -- -- -- -- -- -- -- -- -- -- --    ∷B (elim₁ w) true a x x₁ = {!!}
 -- -- -- -- -- -- -- -- -- -- --    isPropB w = {!!}


 -- -- -- -- -- -- -- -- -- -- -- -- module _ (_≟_ : Discrete A) where

 -- -- -- -- -- -- -- -- -- -- -- --  IsRedex? : ∀ x x' → Dec (IsRedex x x')
 -- -- -- -- -- -- -- -- -- -- -- --  IsRedex? (b , x) (b' , x') =
 -- -- -- -- -- -- -- -- -- -- -- --    subst Dec (sym ΣPathP≡PathPΣ)
 -- -- -- -- -- -- -- -- -- -- -- --      (discreteΣ 𝟚._≟_ (λ _ → _≟_) (b , x) (not b' , x'))

 -- -- -- -- -- -- -- -- -- -- -- --  WillReduce? : ∀ x xs → Dec (WillReduce (fst x) (snd x) xs)  
 -- -- -- -- -- -- -- -- -- -- -- --  WillReduce? _ [] = no λ ()
 -- -- -- -- -- -- -- -- -- -- -- --  WillReduce? _ (_ ∷ xs) = IsRedex? _ _

 -- -- -- -- -- -- -- -- -- -- -- --  IsNormalised? : ∀ xs → Dec (IsNormalised xs)  
 -- -- -- -- -- -- -- -- -- -- -- --  IsNormalised? [] = yes _
 -- -- -- -- -- -- -- -- -- -- -- --  IsNormalised? (x ∷ xs) =
 -- -- -- -- -- -- -- -- -- -- -- --    Dec× (Dec¬ (WillReduce? _ _)) (IsNormalised? _) 


