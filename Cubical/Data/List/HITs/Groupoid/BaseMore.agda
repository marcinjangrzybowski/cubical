{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Data.List.HITs.Groupoid.BaseMore where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (Σ-assoc-≃)
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Empty renaming (elim to ⊥elim ; rec to ⊥rec)

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Nullary


import Cubical.Data.List.Base as B renaming (ind' to elimL)
import Cubical.Data.List.Properties as BP


import Cubical.Functions.Logic as L


open import Cubical.Data.List.HITs.Groupoid.Base
open import Cubical.Data.List.HITs.Groupoid.Properties

open import Cubical.Data.Nat.Order.Recursive


ℕₐ = List Unit

isSetℕₐ : isSet ℕₐ
isSetℕₐ = isOfHLevelRetractFromIso 2 (compIso (isoList (isSet→isGroupoid isSetUnit)) BP.IsoListUnitℕ) isSetℕ


-- module _ {ℓ : Level}{A : Type ℓ} where
--  𝕝4 : A → A → A → A → {!!}
--  𝕝4 = {!!}

-- Shape : ℕ → Type₀
-- Shape n = Σ (List Unit) (λ x → n ≡ length x)


-- isContrList⊤ofLen : ∀ n → isContr (Σ (B.List Unit) (λ xs → n ≡ B.length xs))
-- isContrList⊤ofLen = {!!}

-- isContrShape : ∀ n → isContr (Shape n)
-- isContrShape n =
--          isOfHLevelRetractFromIso 0
--             (List-IsoL (isOfHLevelUnit 3) n)
--             (isContrList⊤ofLen n)

-- Shape≡' : ∀ {n} → {x y : Shape n} → x ≡ y
-- Shape≡' = isContr→isProp (isContrShape _) _ _



-- toShape : {!!}
-- toShape = {!!}

module _ {ℓ : Level}{A B : Type ℓ} where
 congEquivSq : {x y x' y' : A} {p : x ≡ y} {p' : x' ≡ y'}
                {r : _}{s : _} (e : A ≃ B) →
                               (Square (cong (fst e) p)
                    (cong (fst e) p')
                    (cong (fst e) r)
                    (cong (fst e) s))
                    → (Square p p' r s)

 congEquivSq {p = p} {p'} {r} {s} e sq = 
    whiskSq.sq' _
      (congSq (invEq e) sq)
      (λ i → retEq e (p i))
      (λ i → retEq e (p' i))
      (λ i → retEq e (r i))
      (λ i → retEq e (s i))

 congIsoSq : {x y x' y' : A} {p : x ≡ y} {p' : x' ≡ y'}
                {r : _}{s : _}
                (e : Iso A B) →
                               (Square (cong (Iso.fun e) p)
                    (cong (Iso.fun e) p')
                    (cong (Iso.fun e) r)
                    (cong (Iso.fun e) s))
                    → (Square p p' r s)

 congIsoSq {p = p} {p'} {r} {s} e sq i j =
   hcomp (λ k → λ { (i = i0) → (Iso.leftInv e) (p j) k
                  ; (i = i1) → (Iso.leftInv e) (p' j) k
                  ; (j = i0) → (Iso.leftInv e) (r i) k
                  ; (j = i1) → (Iso.leftInv e) (s i) k
                  }) (Iso.inv e (sq i j))


module _ {ℓ : Level}{A : Type ℓ} (isGroupoidA : isGroupoid A) where

 tabuRecFun : ∀ k → (Σ (B.List A) (λ xs → k ≡ B.length xs)) → (A ×^ k)
 tabuRecFun zero x = tt*
 tabuRecFun (suc k) (B.[] , snd₁) = ⊥rec (snotz snd₁)
 tabuRecFun (suc k) (x B.∷ fst₁ , snd₁) = x , tabuRecFun k (fst₁ , injSuc snd₁)

 tabuRecInv : ∀ k  → (A ×^ k) → (Σ (B.List A) (λ xs → k ≡ B.length xs))
 tabuRecInv zero x = B.[] , refl
 tabuRecInv (suc k) (x , xs) =
   let (l , p) = tabuRecInv k xs
   in (x B.∷ l) , cong suc p

 tabuRecSec : ∀ k → section (tabuRecFun k) (tabuRecInv k)
 tabuRecSec zero b i = tt*
 tabuRecSec (suc k) b = ΣPathP (refl , tabuRecSec k (snd b)) 

 tabuRecRet : ∀ k → retract (tabuRecFun k) (tabuRecInv k)
 tabuRecRet zero (B.[] , snd₁) = Σ≡Prop (λ _ → isSetℕ _ _) refl
 tabuRecRet (suc k) (B.[] , snd₁) = ⊥rec (snotz snd₁)
 tabuRecRet zero (x B.∷ fst₁ , snd₁) = ⊥rec (znots snd₁)
 tabuRecRet (suc k) (x B.∷ fst₁ , snd₁) =
  let p = tabuRecRet k (fst₁ , injSuc snd₁)
  in Σ≡Prop (λ _ → isSetℕ _ _) (cong (x B.∷_) (cong fst p))

 tabuRec : ∀ k → Iso (Σ (B.List A) (λ xs → k ≡ B.length xs)) (A ×^ k)
 Iso.fun (tabuRec k) = tabuRecFun k
 Iso.inv (tabuRec k) = tabuRecInv k
 Iso.rightInv (tabuRec k) = tabuRecSec k
 Iso.leftInv (tabuRec k) = tabuRecRet k


 tabuRec' : ∀ k → Iso (Σ (List A) (λ xs → k ≡ length xs)) (A ×^ k)
 tabuRec' k = compIso (List-IsoL isGroupoidA k) (tabuRec k)

 -- viaTabu : ∀ k → (v : A ×^ k) → (xs ys : List A)
 --                 → (p : k ≡ length xs) → (q : k ≡ length ys)
 --                 → v ≡ Iso.fun (tabuRec' k) (xs , p)
 --                 → v ≡ Iso.fun (tabuRec' k) (ys , q)
 --                 → xs ≡ ys
 -- viaTabu k v xs ys p q p' q' =
 --   cong fst (invEq (congEquiv {x = xs , p} {y = ys , q}
 --        (isoToEquiv (tabuRec' k))) (sym p' ∙ q'))



 yyy : Square {A = List ℕ}

           (++-pentagon-diag [ 0 ] [ 1 ] [ 2 ] [ 3 ])
           (++-assoc _ _ _)
           (cong (_++ [ 3 ]) (++-assoc _ _ _))           
           (sym (cong ([ 0 ] ++_) (++-assoc _ _ _)))

 yyy  = congIsoSq (isoList (isSet→isGroupoid isSetℕ))
                  λ i i₁ → 0 B.∷ 1 B.∷ 2 B.∷ 3 B.∷ B.[]


 yyy' : (xs ys zs ws : List A) →
         Square (++-pentagon-diag xs ys zs ws)
            (++-assoc _ _ _)
            (cong (_++ ws) (++-assoc _ _ _))           
            (sym (cong (xs ++_) (++-assoc _ _ _)))

 yyy' xs ys zs ws =
   congSq (flip bind g) yyy
  where
  g : ℕ → List A
  g zero = xs
  g (suc zero) = ys
  g (suc (suc zero)) = zs
  g (suc (suc (suc x))) = ws

 fL : B.List A → ℕ → List A
 fL B.[] x₁ = []
 fL (x B.∷ x₂) zero = [ x ]
 fL (x B.∷ x₂) (suc x₁) = fL x₂ x₁

 Listₐ-sqHlp : (g : ℕ → List A) →
               {a₀₀ a₀₁ : List ℕ} {a₀₋ : a₀₀ ≡ a₀₁}
                 {a₁₀ a₁₁ : List ℕ} {a₁₋ : a₁₀ ≡ a₁₁}
              {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
        → Square
             (cong (Iso.fun (isoList (isSet→isGroupoid isSetℕ))) a₀₋)
             (cong (Iso.fun (isoList (isSet→isGroupoid isSetℕ))) a₁₋)
             (cong (Iso.fun (isoList (isSet→isGroupoid isSetℕ))) a₋₀)
             (cong (Iso.fun (isoList (isSet→isGroupoid isSetℕ))) a₋₁)
        → Square
             (cong (flip bind g) a₀₋)
             (cong (flip bind g) a₁₋)
             (cong (flip bind g) a₋₀)
             (cong (flip bind g) a₋₁)
 Listₐ-sqHlp g x =
   congSq (flip bind g) (congIsoSq (isoList (isSet→isGroupoid isSetℕ)) x)
 
--   -- bind



-- -- yyy : Square (λ i → 1 , 2 , 3 , 4 , tt*) (λ i → 1 , 2 , 3 , 4 , tt*)
-- --              (λ i → 1 , 2 , 3 , 4 , tt*) (λ i → 1 , 2 , 3 , 4 , tt*)
-- --     → Square {A = List ℕ}
-- --           {(([ 1 ] ++ [ 2 ]) ++ [ 3 ]) ++ [ 4 ]}
-- --           {[ 1 ] ++ [ 2 ] ++ [ 3 ] ++ [ 4 ]}
-- --           (++-pentagon-diag [ 1 ] [ 2 ] [ 3 ] [ 4 ])
-- --           {([ 1 ] ++ [ 2 ] ++ [ 3 ]) ++ [ 4 ]}
-- --           {[ 1 ] ++ ([ 2 ] ++ [ 3 ]) ++ [ 4 ]}
-- --           (++-assoc _ _ _)
-- --           (cong (_++ [ 4 ]) (++-assoc _ _ _))           
-- --           (sym (cong ([ 1 ] ++_) (++-assoc _ _ _)))

-- -- yyy pp i j =  fst (congEquivSq
-- --              {x = (([ 1 ] ++ [ 2 ]) ++ [ 3 ]) ++ [ 4 ] , refl}
-- --              {[ 1 ] ++ [ 2 ] ++ [ 3 ] ++ [ 4 ] , refl}
-- --              {([ 1 ] ++ [ 2 ] ++ [ 3 ]) ++ [ 4 ] , refl}
-- --              {[ 1 ] ++ ([ 2 ] ++ [ 3 ]) ++ [ 4 ] , refl}
-- --              {p = Σ≡Prop (λ _ → isSetℕ _ _) (++-pentagon-diag [ 1 ] [ 2 ] [ 3 ] [ 4 ])}
-- --              {Σ≡Prop (λ _ → isSetℕ _ _) (++-assoc _ _ _)}
-- --              {Σ≡Prop (λ _ → isSetℕ _ _) (cong (_++ [ 4 ]) (++-assoc _ _ _))}
-- --              {Σ≡Prop (λ _ → isSetℕ _ _) (sym (cong ([ 1 ] ++_) (++-assoc _ _ _)))}
-- --              (isoToEquiv (tabuRec' (isSet→isGroupoid isSetℕ) 4))
-- --                 pp i j
-- --                 --(λ _ _ → 1 , 2 , 3 , 4 , tt*) 
-- --                -- (isSet→isSet' (isOfHLevel×^ 4 2 isSetℕ)
-- --                --   {!refl!}
-- --                --   {!!}
-- --                --   {!!}
-- --                --   {!!})
-- --                  )



