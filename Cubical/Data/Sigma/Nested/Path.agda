{-

  From (I → Sig ℓ n) we can generate Sig ℓ (n * 3)
  in the two ways by arranging fileds in diferent order
   (this is illustrated in Example.agda)

  Of course for both definitions, the path betwen most nested arguments must be at the end,
  becouse its type depends on all the previous fields.


  In second part of this file, those generated signatures are used to
  define paths of arbitrary dimension (generalization of Path, Square and Cube from Prelude).

  The diferent order of fields results in two diferent (equivalent after uncurring)
  definitions of Pathⁿ.

  Non-primed definition have order of arguments consistent with definitions from Prelude.


-}


{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Sigma.Nested.Path where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Sigma.Nested.Base
open import Cubical.Data.Sigma.Nested.Nested
open import Cubical.Data.Sigma.Nested.Currying

open import Cubical.Foundations.Equiv.HalfAdjoint



sig-PathP : ∀ {ℓ} → ∀ {n}
                 → (p : I → Sig ℓ n)
                 → (x₀ : NestedΣᵣ (p i0)) → (x₁ : NestedΣᵣ (p i1))
                 → Σ[ sₚ ∈ Sig ℓ n ] (NestedΣᵣ sₚ) ≃ (PathP (λ i → NestedΣᵣ (p i)) x₀ x₁)
sig-PathP {n = 0} p x₀ x₁ = _ , isoToEquiv (iso (const refl) (const _) (λ b i j → _) λ a → refl)
sig-PathP {n = 1} p x₀ x₁ = _ , idEquiv _
sig-PathP {n = suc (suc n)} p x₀ x₁ =
  _ , compEquiv
         (Σ-cong-equiv-snd
             λ a → snd (sig-PathP (λ i → snd (p i) (a i)) _ _))
         (isoToEquiv ΣPathPIsoPathPΣ)


-- this verision is putting all the PathPs in the last fields (most nested Sigmas)

sig-PathP-withEnds : ∀ {ℓ} → ∀ {n} → (I → Sig ℓ n) → Sig ℓ (n + n + n)
sig-PathP-withEnds {n = n} s =
   sig-cs.concat
     (sig-cs.concat _ (const (s i1)))
     (fst ∘ uncurry (sig-PathP s) ∘ nestedΣᵣ-cs.split' (s i0) _)



-- sig-PathP-withEnds-iso-lem :  ∀ {ℓ} → ∀ {n} → (s₀ s₁ : Sig ℓ n) → (p : NestedΣᵣ s₀ →  NestedΣᵣ s₁ → Sig ℓ n) →
--      Iso ((Σ ((NestedΣᵣ (s₀)) × (NestedΣᵣ (s₁))) λ (e01) → NestedΣᵣ ((p (fst e01) (snd e01)))))
--           (Σ (NestedΣᵣ (sig-cs.concat (s₀) (λ _ → s₁)))
--             (

--             λ x → NestedΣᵣ (
--                 ((p) (fst (nestedΣᵣ-cs.split' (s₀) (λ _ → s₁) x)) (snd (nestedΣᵣ-cs.split' (s₀) (λ _ → s₁) x))   ))

--                  ))

-- sig-PathP-withEnds-iso-lem = {!!}

-- sig-PathP-withEnds-iso : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
--         → Iso (Σ ((NestedΣᵣ (p i0)) × (NestedΣᵣ (p i1))) λ (e01) → NestedΣᵣ (fst (sig-PathP p (fst e01) (snd e01))))
--               (NestedΣᵣ (sig-PathP-withEnds p))

-- sig-PathP-withEnds-iso {n = n} p = 
--                    -- _ Iso⟨ invIso (Σ-cong-iso-fst
--                    --           (invIso (nestedΣᵣ-cs.isom-concat {n = n} {m = n} _ _))) ⟩
--                    _ Iso⟨ sig-PathP-withEnds-iso-lem (p i0) (p i1) (λ x x₁ → fst (sig-PathP p x x₁)) ⟩
--                    _ Iso⟨ nestedΣᵣ-cs.isom-concat {n = n + n} {m = n} _ _ ⟩ _ ∎Iso



-- this verision is putting puting PathPs as early as it is possible
--   (just after second end is defined)

sig-PathP-withEnds' : ∀ {ℓ} → ∀ {n} → (I → Sig ℓ n) → Sig ℓ (n * 3)
sig-PathP-withEnds' {n = 0} x = _
sig-PathP-withEnds' {n = 1} x = _ , ((_ ,_) ∘ (PathP x))
sig-PathP-withEnds' {n = suc (suc n)} x =
              _ ,
      λ x0 →  _ ,
      λ x1 → PathP _ x0 x1 ,
      λ p → sig-PathP-withEnds' λ i → snd (x i) (p i)



nestedΣᵣ-combine-to : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
                 → NestedΣᵣ (sig-PathP-withEnds' p)
                 → ∀ i → NestedΣᵣ (p i)
nestedΣᵣ-combine-to {n = 0} _ _ _ = _
nestedΣᵣ-combine-to {n = 1} _ x _ = snd (snd x) _
nestedΣᵣ-combine-to {n = suc (suc n)} p x _ =
  _ , (nestedΣᵣ-combine-to ((λ _ → snd (p _) _)) (snd (snd (snd x)) ) _)

nestedΣᵣ-combine-from : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
                  → (∀ i → NestedΣᵣ (p i))
                  → NestedΣᵣ (sig-PathP-withEnds' p)

nestedΣᵣ-combine-from {ℓ} {0} p x = _
nestedΣᵣ-combine-from {ℓ} {1} p x = _ , (_ , λ _ → x _)
nestedΣᵣ-combine-from {ℓ} {suc (suc n)} p x =
   _ , _ , _ , nestedΣᵣ-combine-from (λ _ → snd (p _) _) λ _ → snd (x _)


nestedΣᵣ-combine-iso : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
                  → Iso (NestedΣᵣ (sig-PathP-withEnds' p))
                        (Σ[ (x₀ , x₁) ∈ NestedΣᵣ (p i0) × NestedΣᵣ (p i1) ] PathP (λ i → NestedΣᵣ (p i)) x₀ x₁)

Iso.fun (nestedΣᵣ-combine-iso p) = λ x → _ , λ i → nestedΣᵣ-combine-to p x i
Iso.inv (nestedΣᵣ-combine-iso p) = (λ x → nestedΣᵣ-combine-from p λ _ → (snd x) _)
Iso.rightInv (nestedΣᵣ-combine-iso {n = 0} p) b = refl
Iso.rightInv (nestedΣᵣ-combine-iso {n = 1} p) b = refl
Iso.rightInv (nestedΣᵣ-combine-iso {n = suc (suc n)} p) ((e0 , e1) , b) i = 
  let ((ee0 , ee1) , bb) = Iso.rightInv (nestedΣᵣ-combine-iso {n = suc n} _ )
                 (_ , (λ j → snd (b j))) i
  in ((_ , ee0) , (_ , ee1)) , (λ i₁ → _ , bb i₁)

Iso.leftInv (nestedΣᵣ-combine-iso {n = 0} p) a = refl
Iso.leftInv (nestedΣᵣ-combine-iso {n = 1} p) a = refl
Iso.leftInv (nestedΣᵣ-combine-iso {n = suc (suc n)} p) a i =
  _ , _ , _ , Iso.leftInv (nestedΣᵣ-combine-iso {n = suc n} _) (snd (snd (snd a))) i




-- withEnds'-Iso-withEnds : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
--         → Iso (NestedΣᵣ (sig-PathP-withEnds' p))
--               (NestedΣᵣ (sig-PathP-withEnds p))

-- withEnds'-Iso-withEnds {n = n} p =  _ Iso⟨ nestedΣᵣ-combine-iso p ⟩
--                    _ Iso⟨ (Σ-cong-iso-snd
--                            λ (x₀ , x₁) → equivToIso (invEquiv (snd (sig-PathP p _ _)))) ⟩
--                    _ Iso⟨ invIso (Σ-cong-iso-fst
--                              (invIso (nestedΣᵣ-cs.isom-concat {n = n} {m = n} _ _))) ⟩
--                    _ Iso⟨ nestedΣᵣ-cs.isom-concat {n = n + n} {m = n} _ _ ⟩ _ ∎Iso



mkSigPath : ∀ {ℓ} → ∀ n → NestedΣᵣ (sig-PathP-withEnds' (λ _ → Sig-of-Sig n)) → (I → Sig ℓ n)
mkSigPath {ℓ} n x i =
  equivFun NestedΣᵣ-≃-Sig (snd (snd (Iso.fun Σ-assoc-Iso (Iso.fun (nestedΣᵣ-combine-iso  {n = n} (λ _ → Sig-of-Sig n)) x))) i)









3^ : ℕ → ℕ
3^ zero = suc zero
3^ (suc x) = (3^ x) * 3

3^-lem : ∀ n → 3^ n + 3^ n + 3^ n ≡ 3^ (suc n)
3^-lem n = (λ i → +-assoc (3^ n) (3^ n) (+-zero (3^ n) (~ i)) (~ i)) ∙ *-comm 3 (3^ n)



-- 3^-lem' : ∀ n →  suc (predℕ (3^ n)) ≡ 3^ n
-- 3^-lem' zero = refl
-- 3^-lem' (suc n) = {!!}


-- 3^n-lem2 : ∀ n → (3^ n * 3) ≡ suc (suc (suc ((3^ n * 3) ─ 3)))
-- 3^n-lem2 zero = refl
-- 3^n-lem2 (suc n) = 
--    cong (_* 3) (3^n-lem2 n) ∙ cong (suc ∘ suc)
--      ({!!}
--       ∙
--       {!!}
--       )


-- this function generates explcity description for definition of Pathⁿ

-- note that for each dimension we introduce 2 explicit arguments
-- so for dimension n we will get
--    2 * n   - explicit arguments
--    (3^ n - 1 - (2 * n))  - implicit arguments

pathⁿ-args-desc : ∀ n → Vec Bool (predℕ (3^ n))
pathⁿ-args-desc 0 = []
pathⁿ-args-desc (suc n) =
 let z =   (repeat {n = predℕ (3^ n)} true)
           ++ (false ∷ (repeat {n = predℕ (3^ n)} true))
           ++ (false ∷ pathⁿ-args-desc n)
 in castImpex z

NCubeSig : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Sig ℓ (3^ n)
NCubeSig zero A = A
NCubeSig (suc n) A = sig-subst-n (3^-lem n) (sig-PathP-withEnds (λ _ → NCubeSig n A))

NCubeSig* : ∀ {ℓ} → ℕ → (A : Type ℓ) → Σ ℕ (Sig ℓ)
NCubeSig* zero A = 1 , A
NCubeSig* (suc n) A = _ , (sig-PathP-withEnds (λ _ → snd (NCubeSig* n A)))


-- by dropping last field (the path of the highest dimension)
-- we can create signature of boundary

Boundaryⁿ : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Type ℓ
Boundaryⁿ n A = NestedΣᵣ (dropLast (NCubeSig n A))

Boundaryⁿ* : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Type ℓ
Boundaryⁿ* n A = NestedΣᵣ (dropLast (snd (NCubeSig* n A)))

InsideOfⁿ : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → Boundaryⁿ n A → Type ℓ
InsideOfⁿ {n = n} {A} = lastTy (NCubeSig n A)

InsideOfⁿ* : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → Boundaryⁿ* n A → Type ℓ
InsideOfⁿ* {n = n} {A} = lastTy (snd (NCubeSig* n A))

Pathⁿ : ∀ {ℓ} → (n : ℕ) → (A : Type ℓ) → _
Pathⁿ n A = toTypeFam (pathⁿ-args-desc n) (NCubeSig n A)

Pathⁿ* : ∀ {ℓ} → (n : ℕ) → (A : Type ℓ) → _
Pathⁿ* n A = toTypeFam (castImpex (pathⁿ-args-desc n)) (snd (NCubeSig* n A))

NCubeSig' : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Sig ℓ (3^ n)
NCubeSig' zero A = A
NCubeSig' (suc n) A = sig-PathP-withEnds' λ _ → NCubeSig' n A


Boundaryⁿ' : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Type ℓ
Boundaryⁿ' n A = NestedΣᵣ (dropLast (NCubeSig' n A))

InsideOfⁿ' : ∀ {ℓ} → ∀ {n} → {A : Type ℓ} → Boundaryⁿ' n A → Type ℓ
InsideOfⁿ' {n = n} {A} = lastTy (NCubeSig' n A)

Pathⁿ' : ∀ {ℓ} → (n : ℕ) → (A : Type ℓ) → _
Pathⁿ' n A = toTypeFam (pathⁿ-args-desc n) (NCubeSig' n A)


-- NCubeSig properly describes type of Path , Cube and Square from Prelude
-- this is _not_ the case for NCubeSig' because of diferent order of arguments

private
  Path' : ∀ {ℓ} → (A : Type ℓ) → toTypeFamTy (pathⁿ-args-desc 1) (NCubeSig 1 A)
  Path' = Path

Square' : ∀ {ℓ} → (A : Type ℓ) → toTypeFamTy (pathⁿ-args-desc 2) (NCubeSig 2 A)
Square' A = Square {A = A}

Cube' : ∀ {ℓ} → (A : Type ℓ) → toTypeFamTy (pathⁿ-args-desc 3) (NCubeSig 3 A)
Cube' A = Cube {A = A}

-- Pathⁿ is definationaly equall to Path, Square and Cube with type argument made explicit

Pathⁿ-1-≡-PathP : ∀ {ℓ} → Pathⁿ {ℓ} 1 ≡ Path
Pathⁿ-1-≡-PathP = refl

Pathⁿ-2-≡-Square' : ∀ {ℓ} → Pathⁿ {ℓ} 2 ≡ Square'
Pathⁿ-2-≡-Square' = refl

Pathⁿ-3-≡-Cube' : ∀ {ℓ} → Pathⁿ {ℓ} 3 ≡ Cube'
Pathⁿ-3-≡-Cube' = refl



---

record CubeR {ℓ} {bTy : Type ℓ} (cTy : bTy → Type ℓ) : Type ℓ where
  constructor cubeR

  field
    side0 side1 : bTy


Cubeⁿ : ∀ {ℓ} → ℕ → (A : Type ℓ) → Type ℓ
Cubeⁿ n A = NestedΣᵣ (NCubeSig n A)

Cubeⁿ' : ∀ {ℓ} → ℕ → (A : Type ℓ) → Type ℓ
Cubeⁿ' n A = NestedΣᵣ (NCubeSig' n A)

Cubeⁿ* : ∀ {ℓ} → ℕ → (A : Type ℓ) → Type ℓ
Cubeⁿ* n A = NestedΣᵣ (snd (NCubeSig* n A))

cubeBd' : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Cubeⁿ' n A → Boundaryⁿ' n A
cubeBd' n A = dropLastΣᵣ ( (NCubeSig' n A))

cubeBd* : ∀ {ℓ} → ∀ n → (A : Type ℓ) → Cubeⁿ* n A → Boundaryⁿ* n A
cubeBd* n A = dropLastΣᵣ (snd (NCubeSig* n A))

cubeIns' : ∀ {ℓ} → ∀ n → (A : Type ℓ) → (c : Cubeⁿ' n A) → InsideOfⁿ' {n = n} {A} (cubeBd' n A c)
cubeIns' n A c = getLast ((NCubeSig' n A)) c


module Boundary*-elim-iso-lemmas where

  spwe-drop : ∀ {ℓ} → ∀ {n} → (s : I → Sig ℓ (suc n))  → (x₀ : NestedΣᵣ (s i0)) → (x₁ : NestedΣᵣ (s i1)) →
                             (dropLast (fst (sig-PathP (s) x₀ x₁)))
                           ≡ (fst (sig-PathP (λ i → dropLast (s i)) (dropLastΣᵣ (s i0) x₀) (dropLastΣᵣ (s i1) x₁)))

  spwe-drop {n = zero} s x₀ x₁ = refl
  spwe-drop {n = suc zero} s x₀ x₁ = refl
  spwe-drop {n = suc (suc n)} s x₀ x₁ =
    cong (( PathP _ _ _ ) ,_ ) (funExt λ x → spwe-drop {n = suc n} _ _ _)


  spwe-drop-iso : ∀ {ℓ} → ∀ {n} → (s : I → Sig ℓ n)  → (x₀ : NestedΣᵣ (s i0)) → (x₁ : NestedΣᵣ (s i1)) →
                            Iso (NestedΣᵣ (dropLast (fst (sig-PathP (s) x₀ x₁))))
                                (NestedΣᵣ (fst (sig-PathP (λ i → dropLast (s i)) (dropLastΣᵣ (s i0) x₀) (dropLastΣᵣ (s i1) x₁))))

  spwe-drop-iso {n = 0} _ _ _ = idIso
  spwe-drop-iso {n = 1} s x₀ x₁ = idIso
  spwe-drop-iso {n = 2} s x₀ x₁ = idIso
  spwe-drop-iso {n = suc (suc (suc n))} s x₀ x₁ =
      Σ-cong-iso-snd λ x → spwe-drop-iso {n = suc (suc n)} _ _ _


  concat-dropL-iso :  ∀ {ℓ} → ∀ {n m}
                  → (sₙ : Sig ℓ n)
                  → (sₘ : NestedΣᵣ sₙ → Sig ℓ (suc m))
                  → Iso (NestedΣᵣ (dropLast (sig-cs.concat sₙ sₘ)))
                        (NestedΣᵣ (sig-cs.concat sₙ (dropLast ∘ sₘ)))

  concat-dropL-iso {n = 0} sₙ sₘ = idIso
  concat-dropL-iso {n = 1} {0} sₙ sₘ = idIso
  concat-dropL-iso {n = 1} {suc m} sₙ sₘ = idIso
  concat-dropL-iso {n = (suc (suc zero))} (_ , sₙ) sₘ =
     Σ-cong-iso-snd
       λ x → concat-dropL-iso (sₙ x) (sₘ ∘ (x ,_))
  concat-dropL-iso {n = suc (suc (suc n))} (_ , sₙ) sₘ =
     Σ-cong-iso-snd
       λ x → concat-dropL-iso (sₙ x) (sₘ ∘ (x ,_))


  sig-PathP-withEnds'-iso-dropL : ∀ {ℓ} → ∀ {n} → (p : I → Sig ℓ n)
          → Iso (NestedΣᵣ (dropLast (sig-PathP-withEnds' p)))
                (Σ (Σ (NestedΣᵣ (p i0)) (NestedΣᵣ ∘ (λ _ → p i1)))
                   λ e01 → PathP (λ i → NestedΣᵣ (dropLast (p i)))
                              (dropLastΣᵣ (p i0) (fst e01))
                              (dropLastΣᵣ (p i1) (snd e01))
                )

  Iso.fun (sig-PathP-withEnds'-iso-dropL {n = 0} _) = λ x → (_ , _) , (λ i → _)
  Iso.inv (sig-PathP-withEnds'-iso-dropL {n = 0} _) = λ _ → _
  Iso.rightInv (sig-PathP-withEnds'-iso-dropL {n = 0} _) _ = refl
  Iso.leftInv (sig-PathP-withEnds'-iso-dropL {n = 0} _) _ = refl

  Iso.fun (sig-PathP-withEnds'-iso-dropL {n = n@(suc zero)} _) = _, refl
  Iso.inv (sig-PathP-withEnds'-iso-dropL {n = n@(suc zero)} _) = fst
  Iso.rightInv (sig-PathP-withEnds'-iso-dropL {n = n@(suc zero)} _) _ = refl
  Iso.leftInv (sig-PathP-withEnds'-iso-dropL {n = n@(suc zero)} _) _ = refl

  Iso.fun (sig-PathP-withEnds'-iso-dropL {n = n@(suc (suc zero))} _) (_ , _ , p , e0 , e1) =
       ((_ , e0) , (_ , e1)) , p
  Iso.inv (sig-PathP-withEnds'-iso-dropL {n = n@(suc (suc zero))} _) (((_ , e0) , (_ , e1)) , p) =
       (_ , _ , p , e0 , e1)
       
  Iso.rightInv (sig-PathP-withEnds'-iso-dropL {n = n@(suc (suc zero))} _) _ = refl
  Iso.leftInv (sig-PathP-withEnds'-iso-dropL {n = n@(suc (suc zero))} _) _ = refl
  
  Iso.fun (sig-PathP-withEnds'-iso-dropL {n = n@(suc (suc (suc nn)))} _) (_ , _ , _ , x) =
    let (e0' , e1') , p' = Iso.fun (sig-PathP-withEnds'-iso-dropL {n = (suc (suc nn))} _) x           
    in  ((_ , e0') , _ , e1') , λ i → _ , p' i

  Iso.inv (sig-PathP-withEnds'-iso-dropL {n = n@(suc (suc (suc nn)))} _) (((_ , e0') , _ , e1') , pp') =
    let (e0 , e1 , p) = Iso.inv (sig-PathP-withEnds'-iso-dropL {n = (suc (suc nn))} _) ((e0' , e1') , λ i → snd (pp' i))           
    in  ( _ , _ , _ , e0 , e1 , p)

  Iso.rightInv (sig-PathP-withEnds'-iso-dropL {n = n@(suc (suc (suc nn)))} _) (((_ , e0') , _ , e1') , pp') i =
    let (e0'' , e1'') , p'' = Iso.rightInv (sig-PathP-withEnds'-iso-dropL {n = (suc (suc nn))} _) ((e0' , e1') , λ i → snd (pp' i)) i           
    in ((_ , e0'') , _ , e1'') , λ j → _ , p'' j


  Iso.leftInv (sig-PathP-withEnds'-iso-dropL {n = n@(suc (suc (suc nn)))} s) (_ , _ , p' , x) i = 
    let (e0 , e1 , p) = Iso.leftInv (sig-PathP-withEnds'-iso-dropL {n = (suc (suc nn))} λ j → snd (s j) (p' j)) x i           
    in  ( _ , _ , _ , e0 , e1 , p)




Boundaryⁿ'-elim-iso : ∀ {ℓ} → {A : Type ℓ} → ∀ n →
               Iso (Boundaryⁿ' (suc n) A)
                   (Σ ((Cubeⁿ' n A) × (Cubeⁿ' n A)) λ a → cubeBd' n A (fst a) ≡ cubeBd' n A (snd a) )

Boundaryⁿ'-elim-iso {A = A} n = sig-PathP-withEnds'-iso-dropL λ _ → (NCubeSig' n A)
  where open Boundary*-elim-iso-lemmas 






-- module debugTransp where

--   A = Type

--   zz : (Σ ((Cubeⁿ' 4 A) × (Cubeⁿ' 4 A)) λ a → cubeBd' 4 A (fst a) ≡ cubeBd' 4 A (snd a) ) → {!!}
--   zz x = {!getLast (dropLast (NCubeSig' 4 A)) (Iso.inv (Boundary'-elim-iso 4) x) !}


Cubeⁿ'-elim-iso : ∀ {ℓ} → {A : Type ℓ} → ∀ n →
               Iso (Cubeⁿ' (suc n) A)
                   (Σ ((Cubeⁿ' n A) × (Cubeⁿ' n A)) λ a → (fst a) ≡ (snd a) )

Cubeⁿ'-elim-iso {A = A} n = nestedΣᵣ-combine-iso (λ _ → NCubeSig' n A)

Cubeⁿ'-elim :  ∀ {ℓ} → {A : Type ℓ} → ∀ n → (Cubeⁿ' (suc n) A) → I → (Cubeⁿ' n A)                
Cubeⁿ'-elim n x i = snd (Iso.fun (Cubeⁿ'-elim-iso n) x) i


Cubeⁿ'-ΣInsideⁿ'-iso : ∀ {ℓ} → {A : Type ℓ} → ∀ n →
                         Iso
                          (Cubeⁿ' n A)
                          (Σ (Boundaryⁿ' n A) (InsideOfⁿ' {n = n} {A}) )
                          
Cubeⁿ'-ΣInsideⁿ'-iso {A = A} n = nestedΣᵣ-dropLast.isom-to (3^ n) (NCubeSig' n A)



-- Cube'-split-iso : ∀ {ℓ} → ∀ {A : Type ℓ} → ∀ n m → Iso {!Cubeⁿ' n !} {!!}
-- Cube'-split-iso = {!!}

-- maybe imprve (check?) performance on this, isomorphism should be avoidable
Cubeⁿ'-map : ∀ {ℓ ℓb} → {A : Type ℓ} → {B : Type ℓb} → ∀ n → (A → B) → Cubeⁿ' n A → Cubeⁿ' n B
Cubeⁿ'-map zero f x = f x
Cubeⁿ'-map (suc zero) f (_ , _ , p) = _ , _ , cong f p
Cubeⁿ'-map {A = A} {B = B} (suc (suc n)) f = 
     IsoB.inv ∘ (λ x → _ , cong (Cubeⁿ'-map (suc n) f) (snd x)) ∘ IsoA.fun
  where
    module IsoA = Iso (Cubeⁿ'-elim-iso {A = A} (suc n))
    module IsoB = Iso (Cubeⁿ'-elim-iso {A = B} (suc n))



Cubeⁿ'-map2 : ∀ {ℓ ℓb} → {A A' : Type ℓ} → {B : Type ℓb} → ∀ n → (A → A' → B) → Cubeⁿ' n A → Cubeⁿ' n A' → Cubeⁿ' n B
Cubeⁿ'-map2 zero f x₁ x₂ = f x₁ x₂
-- Cubeⁿ'-map2 (suc zero) f (_ , _ , p₁) (_ , _ , p₂) =  _ , _ , λ i → f (p₁ i) (p₂ i) 
Cubeⁿ'-map2 {A = A} {A'} {B} (suc n) f x₁ x₂ = 
    IsoB.inv (_ , λ i → Cubeⁿ'-map2 {A = A} {A' = A'} {B = B} n f (snd (IsoA.fun x₁) i) (snd (IsoA'.fun x₂) i))
   where
    module IsoA = Iso (Cubeⁿ'-elim-iso {A = A} n)
    module IsoA' = Iso (Cubeⁿ'-elim-iso {A = A'} n)
    module IsoB = Iso (Cubeⁿ'-elim-iso {A = B} n)





Boundaryⁿ'-elim-iso2 : ∀ {ℓ} → {A : Type ℓ} → ∀ n →
               Iso (Boundaryⁿ' (suc n) A)
                   ((Σ (Σ ((Boundaryⁿ' n A) × (Boundaryⁿ' n A)) λ a → (fst a) ≡ (snd a) ))
                     λ x → InsideOfⁿ' {n = n} {A} (fst (fst x)) × InsideOfⁿ' {n = n} {A} (snd (fst x)) )

Boundaryⁿ'-elim-iso2 {A = A} n =
   compIso (Boundaryⁿ'-elim-iso {A = A} n) h 

  where

    cuIso = (isHAEquiv→Iso (snd (iso→HAEquiv (Cubeⁿ'-ΣInsideⁿ'-iso {A = A} n))))

    h : Iso
                (Σ (Cubeⁿ' n A × Cubeⁿ' n A)
                  (λ a → cubeBd' n A (fst a) ≡ cubeBd' n A (snd a)))
                (Σ (Σ (Boundaryⁿ' n A × Boundaryⁿ' n A) (λ a → fst a ≡ snd a))
                  (λ x → InsideOfⁿ' {n = n} {A = A} (fst (fst x)) × InsideOfⁿ' {n = n} {A = A} (snd (fst x))))
    Iso.fun h ((c0 , c1) , bp) =
       let (bd0 , ins0) = Iso.fun cuIso c0
           (bd1 , ins1) = Iso.fun cuIso c1
       in  ((bd0 , bd1) , bp) , ins0 , ins1
       
    Iso.inv h (((bd0 , bd1) , bp) , ins0 , ins1) =
       let c0 = Iso.inv cuIso (bd0 , ins0)
           c1 = Iso.inv cuIso (bd1 , ins1)
       in  ((c0 , c1) , (cong fst (Iso.rightInv cuIso _) ∙∙ bp ∙∙ sym (cong fst (Iso.rightInv cuIso _))))

    Iso.rightInv h (((bd0 , bd1) , bp) , ins0 , ins1) i =
       let (bd0 , ins0) = Iso.rightInv cuIso (bd0 , ins0) i
           (bd1 , ins1) = Iso.rightInv cuIso (bd1 , ins1) i
       in  ((bd0 , bd1) ,
                doubleCompPath-filler
                    (cong fst (Iso.rightInv cuIso _))
                    bp
                    (sym (cong fst (Iso.rightInv cuIso _)))
                    (~ i))
                 , ins0 , ins1

    Iso.leftInv h ((c0 , c1) , bp) i =
       let c0' = Iso.leftInv cuIso c0 i
           c1' = Iso.leftInv cuIso c1 i

           ww' : (j : I) → _
           ww' j =  doubleCompPath-filler ( cong fst (Iso.rightInv cuIso (Iso.fun cuIso c0))) bp
                           (sym (cong fst (Iso.rightInv cuIso (Iso.fun cuIso c1)))) (j)


           ww0 : Square
                        (λ _ → bp i0)
                        (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c0))
                        (sym (cong fst (Iso.rightInv cuIso (Iso.fun cuIso c0))))
                        (λ _ → bp i0)
           ww0 k j =
              hcomp
                (λ l → λ { (j = i0) → fst ((isHAEquiv.com (snd (iso→HAEquiv (Cubeⁿ'-ΣInsideⁿ'-iso {A = A} n))) c0) l (~ k))
                         ; (j = i1) → bp i0
                         ; (k = i0) → bp i0
                         ; (k = i1) → (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c0)) j
                    })
                ( (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c0)) (j ∨  (~ k)))


           ww1 :  Square 
                        (λ _ → bp i1)
                        ((cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c1)))
                        ((sym (cong fst (Iso.rightInv cuIso (Iso.fun cuIso c1)))))
                        (λ _ → bp i1)
           ww1 k j =
              hcomp
                (λ l → λ { (j = i0) → fst ((isHAEquiv.com (snd (iso→HAEquiv (Cubeⁿ'-ΣInsideⁿ'-iso {A = A} n))) c1) l (~ k))
                         ; (j = i1) → bp i1
                         ; (k = i0) → bp i1
                         ; (k = i1) → (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c1)) j
                    })
                ( (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c1)) (j ∨  (~ k)))


           ww : PathP (λ v → PathP (λ v₁ → NestedΣᵣ (dropLast (NCubeSig' n A)))
                               (cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c0) v)
                               ((cong (fst ∘ (Iso.fun cuIso)) (Iso.leftInv cuIso c1) v)))
                         ( cong fst (Iso.rightInv cuIso (Iso.fun cuIso c0))
                             ∙∙ bp ∙∙
                           sym (cong fst (Iso.rightInv cuIso (Iso.fun cuIso c1)))) bp
           ww j l =
              hcomp
                (λ k → λ { (j = i0) → ww' k l --
                         ; (j = i1) → bp l
                         ; (l = i0) → ww0 k j
                         ; (l = i1) → ww1 k j
                    })
                ( bp l)

       in  ((c0' , c1') , λ i₁ → ww i i₁)

-- InsideOfⁿ'-elim-iso :  ∀ {ℓ} → {A : Type ℓ} → ∀ n →
--                          (bd : (Boundaryⁿ' (suc n) A))
--                        → Iso (InsideOfⁿ' {n = suc n} bd)
--                              (PathP (λ i → InsideOfⁿ' {n = n} (snd (fst (Iso.fun (Boundaryⁿ'-elim-iso2 n) bd)) i))
--                                 (fst (snd (Iso.fun (Boundaryⁿ'-elim-iso2 n) bd)))
--                                 (snd (snd (Iso.fun (Boundaryⁿ'-elim-iso2 n) bd))))
                       
-- InsideOfⁿ'-elim-iso zero bd = idIso
-- InsideOfⁿ'-elim-iso (suc n) bd = {!!}


-- Boundaryⁿ'-map : ∀ {ℓ ℓb} → {A : Type ℓ} → {B : Type ℓb}
--                  → ∀ n → (A → B)
--                  → Boundaryⁿ' n A
--                  → Boundaryⁿ' n B

-- InsideOfⁿ'-map : ∀ {ℓ ℓb} → {A : Type ℓ} → {B : Type ℓb}
--                  → ∀ n → (f : A → B)
--                  → (bd : Boundaryⁿ' n A)
--                  → InsideOfⁿ' {n = n} bd 
--                  → InsideOfⁿ' {n = n} (Boundaryⁿ'-map n f bd)



-- Boundaryⁿ'-map zero f _ = tt*

-- Boundaryⁿ'-map (suc n) f bd = 
--   let ( (_ , bdP) , (lid0 , lid1 ) ) = Iso.fun (Boundaryⁿ'-elim-iso2 n) bd
--   in Iso.inv (Boundaryⁿ'-elim-iso2 n)
--               (( (_ , cong (Boundaryⁿ'-map n f) bdP)
--                                  , (InsideOfⁿ'-map n f _ lid0 , InsideOfⁿ'-map n f _ lid1) ))
-- InsideOfⁿ'-map zero f bd x = f x

-- InsideOfⁿ'-map (suc n) f bd x =
--    let z = Iso.fun (InsideOfⁿ'-elim-iso n bd) x
--        zz : (i : I) → lastTy (NCubeSig' n _)
--                         (Boundaryⁿ'-map n f
--                          (snd (fst (Iso.fun (Boundaryⁿ'-elim-iso2 n) bd)) i))
--        zz i = InsideOfⁿ'-map n f (snd (fst (Iso.fun (Boundaryⁿ'-elim-iso2 n) bd)) i) (z i)

--        ww : {!!}
--        ww = Iso.inv (InsideOfⁿ'-elim-iso n _) λ i → {!zz i!}

--    in Iso.inv (InsideOfⁿ'-elim-iso n _) λ i → {!zz i!} 
