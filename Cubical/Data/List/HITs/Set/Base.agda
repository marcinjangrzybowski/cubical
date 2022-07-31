{-# OPTIONS --safe #-}

module Cubical.Data.List.HITs.Set.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Nat


-- open import Cubical.Foundations.CartesianKanOps

-- open import Cubical.Data.Nat
-- open import Cubical.Data.Sum
-- open import Cubical.Data.Sigma
-- open import Cubical.Data.Maybe as Mb
-- open import Cubical.Data.Empty renaming (elim to ⊥elim ; rec to ⊥rec)

-- open import Cubical.Functions.FunExtEquiv

-- open import Cubical.Relation.Nullary


-- import Cubical.Data.List.Base as B
-- import Cubical.Data.List.Properties as BP

-- import Cubical.Functions.Logic as L


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
  trunc : isSet (List A)


module _ {A : Type ℓ} where

  infixr 5 _∷_

  _∷_ : A → List A → List A
  x ∷ xs = [ x ] ++ xs


  module Elim {ℓb} {B : List A → Type ℓb}
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
    f [] = b[]
    f [ a ] = b[ a ]
    f (xs ++ ys) = f xs b++ f ys
    f (++-unit-r x i) = b++ur (f x) i
    f (++-unit-l x i) = b++ul (f x) i
    f (++-assoc xs ys zs i) = b++-assoc (f xs) (f ys) (f zs) i
    f (trunc x y p q i₀ i₁) =
       (isOfHLevel→isOfHLevelDep (suc (suc zero)) isSetB)
            (f x) (f y)
            (cong f p) (cong f q)
            (trunc x y p q) i₀ i₁

  module ElimProp {ℓb} {B : List A → Type ℓb}
              (isPropB : ∀ x → isProp (B x))
              (b[] : B [])
              (b[_] : ∀ a → B [ a ])
              (_b++_ : ∀ {xs ys} → B xs → B ys → B (xs ++ ys))


              where

    f : ∀ x → B x
    f = Elim.f (isProp→isSet ∘ isPropB) b[] b[_] _b++_
      (λ _ → isProp→PathP (λ _ → isPropB _) _ _ )
      (λ _ → isProp→PathP (λ _ → isPropB _) _ _ )
      (λ _ _ _ → isProp→PathP (λ _ → isPropB _) _ _ )

  module Rec {ℓb} {B : Type ℓb}
              (isSetB : isSet B)
              (b[] : B)
              (b[_] : A → B)
              (_b++_ : B → B → B)
              (b++ur : (b : B) → (b b++ b[]) ≡ b)
              (b++ul : (b : B) → (b[] b++ b) ≡ b)
              (b++-assoc : (bx by bz : B) → ((bx b++ by) b++ bz) ≡ (bx b++ (by b++ bz)))

              where
    f : List A → B
    f [] = b[]
    f [ a ] = b[ a ]
    f (xs ++ ys) = f xs b++ f ys
    f (++-unit-r x i) = b++ur (f x) i
    f (++-unit-l x i) = b++ul (f x) i
    f (++-assoc xs ys zs i) = b++-assoc (f xs) (f ys) (f zs) i

    f (trunc x y p q i₀ i₁) = 
       (isOfHLevel→isOfHLevelDep (suc (suc zero)) λ _ → isSetB)
            (f x) (f y)
            (cong f p) (cong f q)
            (trunc x y p q) i₀ i₁



  length : List A → ℕ
  length = Rec.f isSetℕ 
    zero
    (λ _ → suc zero)
    _+_
    +-zero
    (λ _ → refl)
    (λ bx by bz → sym (+-assoc bx by bz))
    


  rev : List A → List A
  rev [] = []
  rev [ x ] = [ x ]
  rev (x ++ y) = rev y ++ rev x
  rev (++-unit-r x i) = ++-unit-l (rev x) i
  rev (++-unit-l x i) = ++-unit-r (rev x) i
  rev (++-assoc x y z i) = ++-assoc (rev z) (rev y) (rev x) (~ i)
  rev (trunc x y p q i₀ i₁) = trunc (rev x) (rev y) (cong rev p) (cong rev q) i₀ i₁ 


-- -- module _ {A : Type ℓ} where

-- --   replicate^2 : ℕ → List A → List A
-- --   replicate^2 k = iter k λ x → x ++ x 

-- --   replicate^2' : ℕ → B.List A → B.List A
-- --   replicate^2' k = iter k λ x → x B.++ x 



-- --   module Elim {ℓb} {B : List A → Type ℓb}
-- --               (isSetB : ∀ x → isSet (B x))
-- --               (b[] : B [])
-- --               (b[_] : ∀ a → B [ a ])
-- --               (_b++_ : ∀ {xs ys} → B xs → B ys → B (xs ++ ys))
-- --               (b++ur : ∀ {xs} → (b : B xs) →
-- --                         PathP (λ i → B (++-unit-r xs i)) (b b++ b[]) b)
-- --               (b++ul : ∀ {xs} → (b : B xs) →
-- --                         PathP (λ i → B (++-unit-l xs i)) (b[] b++ b) b)
-- --               (b++-assoc : ∀ {xs ys zs} → (bx : B xs) (by : B ys) (bz : B zs)
-- --                              → PathP (λ i → B (++-assoc xs ys zs i))
-- --                                 ((bx b++ by) b++ bz)
-- --                                  (bx b++ (by b++ bz)))
              
-- --               where

-- --     f : ∀ x → B x
-- --     f [] = b[]
-- --     f [ a ] = b[ a ]
-- --     f (xs ++ ys) = f xs b++ f ys
-- --     f (++-unit-r x i) = b++ur (f x) i
-- --     f (++-unit-l x i) = b++ul (f x) i
-- --     f (++-assoc xs ys zs i) = b++-assoc (f xs) (f ys) (f zs) i
-- --     f (trunc x y p q i₀ i₁) =
-- --        (isOfHLevel→isOfHLevelDep (suc (suc zero)) isSetB)
-- --             (f x) (f y)
-- --             (cong f p) (cong f q)
-- --             (trunc x y p q) i₀ i₁

-- --   module ElimProp {ℓb} {B : List A → Type ℓb}
-- --               (isPropB : ∀ x → isProp (B x))
-- --               (b[] : B [])
-- --               (b[_] : ∀ a → B [ a ])
-- --               (_b++_ : ∀ {xs ys} → B xs → B ys → B (xs ++ ys))
              
              
-- --               where

-- --     f : ∀ x → B x
-- --     f = Elim.f (isProp→isSet ∘ isPropB) b[] b[_] _b++_
-- --       (λ _ → isProp→PathP (λ _ → isPropB _) _ _ )
-- --       (λ _ → isProp→PathP (λ _ → isPropB _) _ _ )
-- --       (λ _ _ _ → isProp→PathP (λ _ → isPropB _) _ _ )

-- --   module RecSet {ℓb} {B : Type ℓb}
-- --               (isSetB : isSet B)
-- --               (b[] : B)
-- --               (b[_] : A → B)
-- --               (_b++_ : B → B → B)
-- --               (b++ur : (b : B) → (b b++ b[]) ≡ b)
-- --               (b++ul : (b : B) → (b[] b++ b) ≡ b)
-- --               (b++-assoc : (bx by bz : B) → ((bx b++ by) b++ bz) ≡ (bx b++ (by b++ bz)))

-- --               where
-- --     f : List A → B
-- --     f [] = b[]
-- --     f [ a ] = b[ a ]
-- --     f (xs ++ ys) = f xs b++ f ys
-- --     f (++-unit-r x i) = b++ur (f x) i
-- --     f (++-unit-l x i) = b++ul (f x) i
-- --     f (++-assoc xs ys zs i) = b++-assoc (f xs) (f ys) (f zs) i

-- --     f (trunc x y p q i₀ i₁) = 
-- --        (isOfHLevel→isOfHLevelDep (suc (suc zero)) λ _ → isSetB)
-- --             (f x) (f y)
-- --             (cong f p) (cong f q)
-- --             (trunc x y p q) i₀ i₁



-- --   length : List A → ℕ
-- --   length = RecSet.f isSetℕ 
-- --     zero
-- --     (λ _ → suc zero)
-- --     _+_
-- --     +-zero
-- --     (λ _ → refl)
-- --     (λ bx by bz → sym (+-assoc bx by bz))
    

-- --   rev : List A → List A
-- --   rev [] = []
-- --   rev [ x ] = [ x ]
-- --   rev (x ++ y) = rev y ++ rev x
-- --   rev (++-unit-r x i) = ++-unit-l (rev x) i
-- --   rev (++-unit-l x i) = ++-unit-r (rev x) i
-- --   rev (++-assoc x y z i) = ++-assoc (rev z) (rev y) (rev x) (~ i)
-- --   rev (trunc x y p q i₀ i₁) = trunc (rev x) (rev y) (cong rev p) (cong rev q) i₀ i₁ 

-- --   rev-rev : ∀ x → rev (rev x) ≡ x
-- --   rev-rev [] = refl
-- --   rev-rev [ x ] = refl
-- --   rev-rev (x ++ y) = cong₂ _++_ (rev-rev x) (rev-rev y)
-- --   rev-rev (++-unit-r x i) j = ++-unit-r (rev-rev x j) i
-- --   rev-rev (++-unit-l x i) j = ++-unit-l (rev-rev x j) i
-- --   rev-rev (++-assoc x y z i) j = ++-assoc (rev-rev x j) (rev-rev y j) (rev-rev z j) i
-- --   rev-rev (trunc x y p q i₀ i₁) k =
-- --      (trunc (rev-rev x k) (rev-rev y k)
-- --              (λ j → (rev-rev (p j) k)) (λ j → (rev-rev (q j) k))
-- --              i₀ i₁ )

-- --   Iso-rev : Iso (List A) (List A)
-- --   Iso.fun Iso-rev = rev
-- --   Iso.inv Iso-rev = rev
-- --   Iso.rightInv Iso-rev = rev-rev
-- --   Iso.leftInv Iso-rev = rev-rev


-- --   length0≡[] : ∀ {x} → length x ≡ 0 → x ≡ []
-- --   length0≡[] =
-- --     ElimProp.f
-- --        (λ x → isPropΠ λ _ → trunc x [])
-- --        (λ z → refl)
-- --        (λ a p → ⊥rec (snotz p))
-- --        (λ {xs} {ys} px py p →
-- --          let (px0 , py0) = m+n≡0→m≡0×n≡0 {length xs} {length ys} p
-- --          in cong₂ _++_ (px px0) (py py0) ∙' ++-unit-r [])
-- --         _



-- --   isContrLen0 : isContr (Σ (List A) λ x → length x ≡ 0)
-- --   fst isContrLen0 = [] , refl
-- --   snd isContrLen0 = λ y → Σ≡Prop (λ _ → isSetℕ _ _) (sym (length0≡[] (snd y)))

-- --   isContr[]≡[] : isContr ([] ≡ [])
-- --   isContr[]≡[] = refl , λ p j i → length0≡[] {x = p i} (λ i₁ → length (p (i₁ ∨ i))) (~ j)

-- --   Iso-length0≡[] : ∀ {x} → Iso (length x ≡ 0) (x ≡ [])
-- --   Iso.fun Iso-length0≡[] = length0≡[]
-- --   Iso.inv Iso-length0≡[] = cong length
-- --   Iso.rightInv Iso-length0≡[] _ = trunc _ _ _ _
-- --   Iso.leftInv Iso-length0≡[] a = isSetℕ _ _ _ _


-- --   IsEmpty : List A → hProp ℓ-zero
-- --   IsEmpty =
-- --      RecSet.f isSetHProp
-- --      L.⊤ (λ _ → L.⊥) L._⊓_
-- --      L.⊓-identityʳ  L.⊓-identityˡ (λ _ by bz → sym (L.⊓-assoc _ by bz))
     


-- -- --   data Uncons (x : List A) : Type ℓ where
-- -- --     nil : x ≡ [] → Uncons x
-- -- --     cons : ∀ a xs → a ∷ xs ≡ x → Uncons x

-- -- --   Uncons-elim : ∀ {ℓ'} → {x : List A} → (B : Uncons x → Type ℓ')
-- -- --                  → (∀ p → B (nil p) )
-- -- --                  → (∀ a xs p → B (cons a xs p))
-- -- --                  → ∀ u → B u 
-- -- --   Uncons-elim B f _ (nil x₂) = f x₂
-- -- --   Uncons-elim B _ f (cons a xs x₂) = f a xs x₂

-- -- --   Uncons⊎ : (x : List A) → Iso (Uncons x) ((x ≡ []) ⊎ (Σ[ (a , xs) ∈ (A × List A) ] a ∷ xs ≡ x))
-- -- --   Iso.fun (Uncons⊎ x) (nil x₁) = inl x₁
-- -- --   Iso.fun (Uncons⊎ x) (cons a xs x₁) = inr ((a , xs) , x₁)
-- -- --   Iso.inv (Uncons⊎ x) (inl x₁) = nil x₁
-- -- --   Iso.inv (Uncons⊎ x) (inr ((a , xs) , x₁)) = cons a xs x₁
-- -- --   Iso.rightInv (Uncons⊎ x) (inl x₁) = refl
-- -- --   Iso.rightInv (Uncons⊎ x) (inr x₁) = refl
-- -- --   Iso.leftInv (Uncons⊎ x) (nil x₁) = refl
-- -- --   Iso.leftInv (Uncons⊎ x) (cons a xs x₁) = refl

-- -- --   isGroupoid-Uncons : isGroupoid A → (x : List A) → isGroupoid (Uncons x)
-- -- --   isGroupoid-Uncons isGrpA x =
-- -- --      isOfHLevelRetractFromIso 3 (Uncons⊎ x)
-- -- --         (isOfHLevel⊎ 1 (isOfHLevelSuc 2 (trunc _ _))
-- -- --         (isOfHLevelΣ 3 (isOfHLevel× 3 isGrpA trunc) λ _ → isSet→isGroupoid (trunc _ _))) 

-- -- --   u++ : {xs ys : List A} → Uncons xs → Uncons ys → Uncons (xs ++ ys)
-- -- --   u++ (nil x) (nil x₁) = nil (cong₂ _++_ x x₁ ∙  ++-unit-l [] )
-- -- --   u++ (nil x) (cons a xs x₁) = cons a xs (sym (++-unit-l (a ∷ xs)) ∙ cong₂ _++_ (sym x) x₁)
-- -- --   u++ {ys = ys} (cons a xs x) _ = cons a (xs ++ ys) (sym (++-assoc _ _ _) ∙ cong (_++ ys) x)

-- -- --   Uncons≡ : (x : I → List A) → (x0 : Uncons (x i0)) (x1 : Uncons (x i1)) → Type ℓ
-- -- --   Uncons≡ x (nil p) (nil p') = Unit*
-- -- --   Uncons≡ _ (nil x) (cons a xs x₁) = ⊥*
-- -- --   Uncons≡ _ (cons a xs x) (nil x₁) = ⊥*
-- -- --   Uncons≡ x (cons a xs p) (cons a' xs' p') =
-- -- --     Σ ((a ≡ a') × (xs ≡ xs'))
-- -- --      λ axs → Square p p' (cong₂ _∷_ (fst axs) (snd axs)) (λ i → x i) 

-- -- --   Uncons≡refl : {x : List A} → {u : Uncons x} → Uncons≡ (λ _ → x) u u
-- -- --   Uncons≡refl {x} {nil x₁} = tt*
-- -- --   Uncons≡refl {x} {cons a xs x₁} = (refl , refl) , refl
  
-- -- --   uncons≡ : ∀ x x0 x1 
-- -- --          → Uncons≡ x x0 x1
-- -- --          → PathP (λ i → Uncons (x i)) x0 x1
-- -- --   uncons≡ x (nil p0) (nil p1) _ i = nil (isProp→PathP (λ i → isProp≡[] (x i)) p0 p1 i)
-- -- --   uncons≡ x (cons a xs p) (cons a' xs' p') q i =
-- -- --     cons (fst (fst q) i) (snd (fst q) i) (snd q i)


-- -- --   UnconsCons : ∀ {x} → (a : A) → (xs : List A) → (a ∷ xs ≡ x) → Uncons x →
-- -- --                  (Σ[ (a , xs) ∈ (A × List A) ] a ∷ xs ≡ x)
-- -- --   UnconsCons a xs s (nil x₁) = ⊥rec (snotz (cong length (s ∙ x₁)))
-- -- --   UnconsCons _ _ _ (cons a xs p) = (a , xs) , p


-- -- --   UnconsCons-sec : ∀ {x} → (a : A) → (xs : List A) → (p : a ∷ xs ≡ x) →  (u : Uncons x) →
-- -- --                         cons (fst (fst (UnconsCons a xs p u)))
-- -- --                              (snd (fst (UnconsCons a xs p u)))
-- -- --                              (snd (UnconsCons a xs p u)) ≡ u
-- -- --   UnconsCons-sec a xs s (nil x₁) = ⊥rec (snotz (cong length (s ∙ x₁)))
-- -- --   UnconsCons-sec a xs p (cons a₁ xs₁ x) = refl

-- -- --   UnconsNil : ∀ {x} → x ≡ [] →  (xs : Uncons x) →
-- -- --                  x ≡ []
-- -- --   UnconsNil _ (nil p) = p
-- -- --   UnconsNil x₁ (cons _ _ p') = ⊥rec (snotz (cong length (p' ∙ x₁)))

-- -- --   UnconsNil-sec : ∀ {x} → (p : x ≡ []) → (xs : Uncons x) →  nil (UnconsNil p xs) ≡ xs  
-- -- --   UnconsNil-sec p (nil x) = refl
-- -- --   UnconsNil-sec x₁ (cons _ _ p') = ⊥rec (snotz (cong length (p' ∙ x₁)))

-- -- --   Uncons→a,xs : ∀ {x} → Uncons x → Maybe (A × List A) 
-- -- --   Uncons→a,xs (nil x) = nothing
-- -- --   Uncons→a,xs (cons a xs x) = just (a , xs)
  
-- -- --   ¬Nil≡Cons : {x : I → List A} → ∀ {xi0≡[] a xs a∷xs≡xi1} 
-- -- --                     → PathP (λ i → Uncons (x i))
-- -- --                       (nil xi0≡[])
-- -- --                       (cons a xs a∷xs≡xi1)
-- -- --                       → ⊥
-- -- --   ¬Nil≡Cons p = ¬nothing≡just (congP (λ _ → Uncons→a,xs) p)
  
-- -- --   unconsSqNil : {x : I → I → List A}
-- -- --                  → ∀ {p00 p10 p01 p11}
-- -- --                  → {p0j : PathP (λ j → x i0 j ≡ []) p00 p10}
-- -- --                  → {p1j : PathP (λ j → x i1 j ≡ []) p01 p11}
-- -- --                  → {pi0 : PathP (λ i → x i i0 ≡ []) p00 p01}
-- -- --                  → {pi1 : PathP (λ i → x i i1 ≡ []) p10 p11}
-- -- --                  → SquareP (λ i j → Uncons (x i j))
-- -- --                      (λ j → nil (p0j j))
-- -- --                      (λ j → nil (p1j j))
-- -- --                      (λ i → nil (pi0 i))
-- -- --                      (λ i → nil (pi1 i))
-- -- --   unconsSqNil = congSqP (λ _ _ → nil) (isGroupoid→isGroupoid' trunc _ _ _ _ _ _)

-- -- --   unconsSqCons : ∀ {x₀₀ x₀₁ x₀₋ x₁₀ x₁₁ x₁₋ x₋₀ x₋₁}
-- -- --                  → {x : Square {A = List A} {x₀₀} {x₀₁} x₀₋ {x₁₀} {x₁₁} x₁₋ x₋₀ x₋₁}
-- -- --                  {a : A}
-- -- --                  → ∀ {xs₀₀ xs₀₁ xs₀₋ xs₁₀ xs₁₁ xs₁₋ xs₋₀ xs₋₁}
-- -- --                  → (xs : Square {A = List A} {xs₀₀} {xs₀₁} xs₀₋ {xs₁₀} {xs₁₁} xs₁₋ xs₋₀ xs₋₁ )
-- -- --                  → ∀ {p00 p10 p01 p11}
-- -- --                  → {p0j : PathP (λ j → a ∷ xs i0 j ≡ x i0 j) p00 p10}
-- -- --                  → {p1j : PathP (λ j → a ∷ xs i1 j ≡ x i1 j) p01 p11}
-- -- --                  → {pi0 : PathP (λ i → a ∷ xs i i0 ≡ x i i0) p00 p01}
-- -- --                  → {pi1 : PathP (λ i → a ∷ xs i i1 ≡ x i i1) p10 p11}
-- -- --                  → SquareP (λ i j → Uncons (x i j))
-- -- --                      (λ j → cons a (xs i0 j) (p0j j))
-- -- --                      (λ j → cons a (xs i1 j) (p1j j))
-- -- --                      (λ i → cons a (xs i i0) (pi0 i))
-- -- --                      (λ i → cons a (xs i i1) (pi1 i))
-- -- --   unconsSqCons {a = a} sq =
-- -- --      congSqP₂ (λ i j → cons a) sq
-- -- --      (isGroupoid→isGroupoid' trunc _ _ _ _ _ _)

-- -- --   proper : (x : List A) → singl x
-- -- --   proper =
-- -- --     ElimProp.f
-- -- --       (λ x → isContr→isProp (isContrSingl x))
-- -- --        ([] , refl) (λ a → _ , refl)
-- -- --        w
-- -- --     where
-- -- --       w : {xs ys : List A} → singl xs → singl ys → singl (xs ++ ys)
-- -- --       w {xs} {ys} (xs' , xp) (ys' , yp) with (discreteℕ (length xs) zero) | (discreteℕ (length ys) zero)
-- -- --       ... | yes p | yes p₁ = [] , cong₂ _++_ (length0≡[] p) (length0≡[] p₁) ∙ ++-unit-l []
-- -- --       ... | yes p | no ¬p = ys' , cong (_++ ys) (length0≡[] p) ∙ λ i → ++-unit-l (yp i) i
-- -- --       ... | no ¬p | yes p = xs' , cong (xs ++_) (length0≡[] p) ∙ λ i → ++-unit-r (xp i) i
-- -- --       ... | no ¬p | no ¬p₁ = xs' ++ ys' , cong₂ _++_ xp yp

-- -- --   filter : (A → Maybe A) → List A → List A
-- -- --   filter f =
-- -- --     Elim.f (λ _ → trunc)
-- -- --      []
-- -- --      (w ∘ f) (_++_)
-- -- --      ++-unit-r ++-unit-l ++-assoc ++-triangle ++-pentagon-diag ++-pentagon-△ ++-pentagon-□

-- -- --     where
-- -- --       w : Maybe A → List A
-- -- --       w nothing = []
-- -- --       w (just x) = [ x ]

-- -- --   bind : List A → (A → List A) → List A
-- -- --   bind x f =
-- -- --     Elim.f (λ _ → trunc)
-- -- --      []
-- -- --      f (_++_)
-- -- --      ++-unit-r ++-unit-l ++-assoc ++-triangle ++-pentagon-diag ++-pentagon-△ ++-pentagon-□
-- -- --      x
-- -- --   -- propT : A → {!!}
-- -- --   -- propT a = {!fst (proper ([] ++ (([] ++ ([] ++ [ a ])) ++ [ a ]) ++ [] ++ [ a ]))!}

-- -- --   uncons : isGroupoid A → ∀ x → Uncons x
-- -- --   uncons isGrpA =
-- -- --     Elim.f
-- -- --       (isGroupoid-Uncons isGrpA)
-- -- --       (nil refl)
-- -- --       (λ a → cons a [] (++-unit-r [ a ]))
-- -- --       u++
-- -- --       (λ b → uncons≡ _ _ _ (w1 b))
-- -- --       (λ b → uncons≡ _ _ _ (w2 b))
-- -- --       (λ bx by bz → uncons≡ _ _ _ (w3 bx by bz))      
-- -- --       w4
-- -- --       (λ bx by bz bw → uncons≡ _ _ _ (w5 bx by bz bw))
-- -- --       w6
-- -- --       w7

-- -- --     where
-- -- --       w1 : {xs : List A} (b : Uncons xs) → _
-- -- --       w1 {xs} (nil x) = _
-- -- --       w1 (cons a xs x) = (refl , ++-unit-r xs) ,
-- -- --          λ i j → hcomp
-- -- --           (λ k →
-- -- --             λ { (i = i1) → x (j ∧ k)
-- -- --               ; (j = i0) → [ a ] ++ ++-unit-r xs i
-- -- --               ; (j = i1) → ++-unit-r (x k) i
-- -- --               })
-- -- --           (lawCool-r [ a ] xs i (~ j))


-- -- --       w2 : {xs : List A} (b : Uncons xs) → _
-- -- --       w2 (nil x) = _
-- -- --       w2 (cons a xs x) = (refl , refl) ,
-- -- --            λ i j →
-- -- --           hcomp (λ k →
-- -- --              λ { (i = i1) → x (j ∧ k)
-- -- --                ; (j = i0) → x i0
-- -- --                ; (j = i1) → ++-unit-l (x k) i
-- -- --                }) (++-unit-l (x i0) (i ∨ ~ j))

-- -- --       w3 : {xs ys zs : List A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) → _
-- -- --       w3 {xs} {ys} {zs} (nil px) (nil py) (nil pz) = _

-- -- --       w3 (nil px) (nil py) (cons a zs' pz) =
-- -- --          (refl , refl)
-- -- --          , congP (λ _ → sym (++-unit-l _) ∙_ )(
-- -- --                 (λ i → cong₂-∙' _++_ (sym (++-unit-lr[] i)) (sym (cong₂ _++_ px py)) pz i)
-- -- --                ◁ (λ i → (λ j → (++-triangle [] (a ∷ zs') (~ j) i))
-- -- --                        ∙ λ k → ++-assoc (px (~ k)) (py (~ k)) (pz k) i)
-- -- --             ▷ sym (cong₂-∙'' _++_ _ _ (sym px)))


-- -- --       w3 {xs} {ys} {zs} (nil px) (cons a ys' ps) _ =
-- -- --          (refl , refl) ,
-- -- --            (((((cong ((sym (++-assoc [ a ] ys' zs)) ∙_)
-- -- --             (cong-∙ (_++ zs) _ _)) ∙ assoc _ _ _ )) 
-- -- --               )
-- -- --              ◁ ((λ i j →
-- -- --                hcomp
-- -- --                 (λ k → λ { (j = i0) → ++-unit-l (a ∷ ys' ++ zs) (k ∨ (~ i))
-- -- --                          ; (j = i1) → ++-assoc (px (~ k)) (ps k) zs i
-- -- --                          })
-- -- --                 (hcomp
-- -- --                    (λ k →
-- -- --                      λ { (i = i1) → ++-unit-l (++-assoc [ a ] ys' zs (~ j)) (~ k)
-- -- --                        ; (j = i0) → ++-unit-l (a ∷ ys' ++ zs) (~ i ∨ ~ k)
-- -- --                        ; (j = i1) → lawCool-l (a ∷ ys') zs (~ k) i
-- -- --                        })
-- -- --                    (++-assoc [ a ] ys' zs (~ j))))) ▷
                
-- -- --               (doubleCompPath-elim _ _ _ ∙∙ sym (assoc _ _ _) ∙∙   
-- -- --               cong ((λ i → ++-unit-l (a ∷ ys' ++ zs) (~ i)) ∙_)
-- -- --                 ( ((cong ((λ i → cong ([] ++_) (λ i₁ → ++-assoc [ a ] ys' zs (~ i₁)) i) ∙_)
-- -- --                       (sym (cong₂-∙ (λ x y →  y ++ x)
-- -- --                         (λ i → ps i ++ zs)
-- -- --                         λ i → px (~ i)) ))
-- -- --                       ∙ assoc _ _ _
-- -- --                          ) ∙ cong (_∙ cong (λ y → y ++ ys ++ zs) (λ i → px (~ i)))
-- -- --                      (sym (cong-∙ ([] ++_) _ _))
-- -- --                      ∙ cong₂-∙ (λ x y →  y ++ x) _ _)))            


-- -- --       w3 {xs} {ys} {zs} (cons a xs' px) _ _ =
-- -- --         (refl , ++-assoc xs' _ _) ,
-- -- --           ((cong ((sym (++-assoc [ a ] (xs' ++ ys) zs)) ∙_)
-- -- --             (cong-∙ (_++ zs) _ _)) ∙ assoc _ _ _ )
-- -- --          ◁
-- -- --            (λ i j →
-- -- --            hcomp (λ k →
-- -- --              λ {  (j = i0) → a ∷ ++-assoc xs' ys zs i
-- -- --                 ; (j = i1) → ++-assoc (px k) ys zs i
-- -- --                 }) (hcomp (λ k →
-- -- --                     λ { (i = i0) →
-- -- --                         hcomp
-- -- --                           (λ l → λ { (j = i0) → a ∷ ++-assoc xs' ys zs (~ k)
-- -- --                                    ; (j = i1) →
-- -- --                                      invSides-filler
-- -- --                                        (++-pentagon-diag [ a ] xs' ys zs)
-- -- --                                        (cong (_++ zs) (++-assoc [ a ] xs' ys))
-- -- --                                        k l
-- -- --                                    ; (k = i0) → ++-pentagon-diag [ a ] xs' ys zs (~ j ∨ l)
-- -- --                                      })
-- -- --                           (++-pentagon-□ [ a ] xs' ys zs k (~ j))
-- -- --                       ; (i = i1) → ++-assoc [ a ] xs' (ys ++ zs) (~ j)
-- -- --                       ; (j = i0) → [ a ] ++ ++-assoc xs' ys zs (i ∨ ~ k)
-- -- --                       ; (j = i1) → (++-pentagon-△ [ a ] xs' ys zs (~ i) (~ k))
-- -- --                       }) (++-assoc [ a ] xs' (ys ++ zs) (~ i ∨ ~ j))))

-- -- --       w4 : {xs ys  : List A} (bx : Uncons xs) (by : Uncons ys) → _
-- -- --       w4 (nil _) (nil _) = unconsSqNil
-- -- --       w4 {xs} {ys} (nil _) (cons _ ys' _) = unconsSqCons λ _ _ → ys'
-- -- --       w4 {_} {ys} (cons _ xs' _) _ = unconsSqCons (++-triangle xs' ys)

-- -- --       w5 : {xs ys zs ws : List A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) (bw : Uncons ws) → _
-- -- --       w5 (nil x) (nil x₁) (nil x₂) (nil x₃) = tt*
-- -- --       w5 {xs} {ys} {zs} {ws} (nil px) (nil py) (nil pz) (cons a ws' wp) = (refl , refl) ,
-- -- --         λ i j → 
-- -- --           hcomp
-- -- --             (λ k → λ {
-- -- --                (i = i0) → snd (w3 {ys = zs} {zs = ws} (u++ (nil px) (nil py)) (nil pz) (cons a ws' wp)) (~ k) j 
-- -- --               ;(i = i1) → snd (w3 {ys = ys} {zs = zs ++ ws} (nil px) (nil py) (u++ (nil pz) (cons a ws' wp))) k j
-- -- --               ;(j = i0) → [ a ] ++ ws'
-- -- --               ;(j = i1) → ++-pentagon-△ xs ys zs ws k i              
-- -- --              }) (snd (w3 {ys = zs} {zs = ws} (u++ (nil px) (nil py)) (nil pz) (cons a ws' wp)) i1 j )
         
-- -- --       w5 {xs} {ys} {zs} {ws} (nil px) (nil py) (cons a zs' pz) bw = (refl , refl) ,
-- -- --         λ i j → 
-- -- --           hcomp
-- -- --             (λ k → λ {
-- -- --                (i = i0) → snd (w3 {ys = zs} {zs = ws} (u++ (nil px) (nil py)) (cons a zs' pz) bw) (~ k) j 
-- -- --               ;(i = i1) → snd (w3 {ys = ys} {zs = zs ++ ws} (nil px) (nil py) (u++ (cons a zs' pz) bw)) k j
-- -- --               ;(j = i0) → a ∷ zs' ++ ws
-- -- --               ;(j = i1) → ++-pentagon-△ xs ys zs ws k i              
-- -- --              }) (snd (w3 {ys = zs} {zs = ws} (u++ (nil px) (nil py)) (cons a zs' pz) bw) i1 j )

-- -- --       w5 {xs} {ys} {zs} {ws} (nil x) (cons a ys' yp) bz bw =
-- -- --         (refl , ++-assoc ys' zs ws) , 
-- -- --          λ i j →
-- -- --            hcomp
-- -- --             (λ k → λ {
-- -- --                (i = i0) → snd (w3 {ys = zs} {zs = ws} (u++ (nil x) (cons a ys' yp)) bz bw) (~ k) j 
-- -- --               ;(i = i1) → snd (w3 {ys = ys} {zs = zs ++ ws} (nil x) (cons a ys' yp) (u++ bz bw)) k j
-- -- --               ;(j = i0) → a ∷ ++-assoc ys' zs ws ((~ k) ∨ i)
-- -- --               ;(j = i1) → ++-pentagon-△ xs ys zs ws k i              
-- -- --              }) (snd (w3 {ys = zs} {zs = ws} (u++ (nil x) (cons a ys' yp)) bz bw) i1 j)


-- -- --       w5 {xs} {ys} {zs} {ws} bx@(cons a xs' xp) by bz bw =
-- -- --         (refl , ++-pentagon-diag xs' ys zs ws ) ,
-- -- --          λ i j →
-- -- --            hcomp
-- -- --             (λ k → λ {
-- -- --                (i = i0) → snd (w3 {ys = zs} {zs = ws} (u++ bx by) bz bw) (~ k) j 
-- -- --               ;(i = i1) → snd (w3 {ys = ys} {zs = zs ++ ws} (cons a xs' xp) by (u++ bz bw)) k j
-- -- --               ;(j = i0) → a ∷ ++-pentagon-△ xs' ys zs ws (k) i
-- -- --               ;(j = i1) → ++-pentagon-△ xs ys zs ws k i              
-- -- --              }) (snd (w3 {ys = ys} {zs = zs ++ ws} (cons a xs' xp) by (u++ bz bw)) i0 j)
             
-- -- --       w6 : {xs ys zs ws : List A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) (bw : Uncons ws) → _
-- -- --       w6 (nil _) (nil _) (nil _) (nil _) = unconsSqNil
-- -- --       w6 (nil _) (nil _) (nil _) (cons _ ws _) = unconsSqCons λ _ _ → ws
-- -- --       w6 {_} {_} {_} {ws} (nil _) (nil _) (cons _ zs _) _ = unconsSqCons λ _ _ → zs ++ ws
-- -- --       w6 {_} {_} {zs} {ws} (nil x) (cons a ys x₁) _ _ = unconsSqCons λ i j → ++-assoc ys zs ws (j ∨ (~ i)) 
-- -- --       w6 (cons a xs x) _ _ _ = unconsSqCons (++-pentagon-△ _ _ _ _) 

-- -- --       w7 : {xs ys zs ws : List A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) (bw : Uncons ws) → _
-- -- --       w7 (nil x) (nil x₁) (nil x₂) (nil x₃) = unconsSqNil
-- -- --       w7 (nil _) (nil _) (nil _) (cons _ ws _) = unconsSqCons λ _ _ → ws
-- -- --       w7 {_} {_} {_} {ws} (nil _) (nil _) (cons _ zs' _) _ = unconsSqCons λ _ _ → zs' ++ ws
-- -- --       w7 {_} {_} {zs} {ws} (nil _) (cons _ ys' _) _ _ =
-- -- --                                   unconsSqCons λ i j → ++-assoc ys' zs ws (j ∧ (~ i))
-- -- --       w7 (cons _ _ _) _ _ _ = unconsSqCons (++-pentagon-□ _ _ _ _)

-- -- --   fromUncons : ∀ {x} → Uncons x → List A
-- -- --   fromUncons (nil x) = []
-- -- --   fromUncons (cons a xs x) = a ∷ xs

-- -- --   unconsIso : (isGrpA : isGroupoid A) → Iso (Σ _ Uncons) (List A)
-- -- --   Iso.fun (unconsIso isGrpA) = fromUncons ∘ snd
-- -- --   Iso.inv (unconsIso isGrpA) x = x , uncons isGrpA x
-- -- --   Iso.rightInv (unconsIso isGrpA) x =
-- -- --     Uncons-elim (λ u → fromUncons u ≡ x)
-- -- --       sym (λ _ _ p → p) (uncons isGrpA x) 
-- -- --   Iso.leftInv (unconsIso isGrpA) (_ , nil x) = ΣPathP ((sym x) , uncons≡ _ _ _ tt*)
-- -- --   Iso.leftInv (unconsIso isGrpA) (fst₁ , cons a xs x) =
-- -- --      ΣPathP (x , (uncons≡ _ _ _ ((refl , (++-unit-l xs)) ,
-- -- --        (leftright _ _ ◁ λ i j →
-- -- --          hcomp
-- -- --           (λ k → λ { (i = i1) → x (j ∧ k)
-- -- --                    ; (j = i0) → ++-triangle [ a ] xs i k
-- -- --                    ; (j = i1) → x (i ∧ k) })
-- -- --           (++-unit-r [ a ] (i ∨ j) ++ xs)))))


-- -- --   uncons-Iso-from : (Maybe (A × List A)) → List A
-- -- --   uncons-Iso-from nothing = []
-- -- --   uncons-Iso-from (just (a , xs)) = a ∷ xs



-- -- --   uncons-Iso : isGroupoid A → Iso (List A) (Maybe (A × List A))
-- -- --   Iso.fun (uncons-Iso isGrpA) x = Uncons→a,xs (uncons isGrpA x) 
-- -- --   Iso.inv (uncons-Iso isGrpA) = uncons-Iso-from    
-- -- --   Iso.rightInv (uncons-Iso isGrpA) nothing = refl
-- -- --   Iso.rightInv (uncons-Iso isGrpA) (just x) = cong (just ∘ (fst x ,_)) (++-unit-l (snd x))
-- -- --   Iso.leftInv (uncons-Iso isGrpA) a =
-- -- --     Uncons-elim (λ u → uncons-Iso-from (Uncons→a,xs u) ≡ a)
-- -- --                 (λ p → sym p) (λ _ _ x → x) (uncons isGrpA a)


-- -- --   -- length0-≡-IsEmpty : ∀ x → ((length x ≡ 0) , isSetℕ _ _) ≡ (IsEmpty x)
-- -- --   -- length0-≡-IsEmpty =
-- -- --   --      ElimProp.f
-- -- --   --       (λ _ → isSetHProp _ _)
-- -- --   --       (L.⇔toPath (λ _ → _) λ _ → refl)
-- -- --   --       (λ _ → L.⇔toPath snotz ⊥rec)
-- -- --   --       {!!}
       


-- -- --   length' : Maybe (A × List A) → ℕ
-- -- --   length' nothing = zero
-- -- --   length' (just x) = suc (length (snd x))

-- -- --   uncons-Iso-L' : isGroupoid A → ∀ k →
-- -- --                   Iso (Σ (List A) (λ xs → length xs ≡ k))
-- -- --                       (Σ (Maybe (A × List A)) (λ xs → length' xs ≡ k))
-- -- --   uncons-Iso-L' isGrpA _ =    
-- -- --         Σ-congProp-iso
-- -- --           (uncons-Iso isGrpA)
-- -- --           (λ _ → isSetℕ _ _)
-- -- --           (λ _ → isSetℕ _ _)
-- -- --           λ { (nothing ) → (λ x → x) , (λ x → x)
-- -- --             ; (just _) → (λ x → x) , (λ x → x) }


-- -- --   uncons-Iso-L : isGroupoid A → ∀ k →
-- -- --                   Iso (Σ (List A) (λ xs → length xs ≡ (suc k)))
-- -- --                       (A × (Σ (List A) (λ xs → length xs ≡ k)))
-- -- --   uncons-Iso-L isGrpA k =
-- -- --     compIso (uncons-Iso-L' isGrpA (suc k)) w

-- -- --      where
-- -- --        w : Iso _ _
-- -- --        Iso.fun w (nothing , p) = ⊥rec (znots p)
-- -- --        Iso.fun w (just (a , l) , p) = a , l , injSuc p
-- -- --        Iso.inv w (a , l , p) = just (a , l) , cong suc p
-- -- --        Iso.rightInv w _ = ΣPathP (refl , Σ≡Prop (λ _ → isSetℕ _ _) refl)
-- -- --        Iso.leftInv w (nothing , p) = ⊥rec (znots p)
-- -- --        Iso.leftInv w (just _ , _) = Σ≡Prop (λ _ → isSetℕ _ _) refl



-- -- --   List-Iso : isGroupoid A → ∀ k →
-- -- --                     Iso (Σ (List A) (λ xs → length xs ≡ k))
-- -- --                         (Σ (B.List A) (λ xs → B.length xs ≡ k))
-- -- --   Iso.fun (List-Iso isGrpA zero) _ = B.[] , refl
-- -- --   Iso.inv (List-Iso isGrpA zero) _ = [] , refl
-- -- --   Iso.rightInv (List-Iso isGrpA zero) (B.[] , p) = Σ≡Prop (λ _ → isSetℕ _ _) refl
-- -- --   Iso.rightInv (List-Iso isGrpA zero) (x B.∷ l , p) = ⊥rec (snotz p)
-- -- --   Iso.leftInv (List-Iso isGrpA zero) (_ , p) = Σ≡Prop (λ _ → isSetℕ _ _) (sym (length0≡[] p))
  
-- -- --   List-Iso isGrpA (suc k) =
-- -- --     compIso (uncons-Iso-L isGrpA k) w 
-- -- --     where
-- -- --       w' : _
-- -- --       w' = List-Iso isGrpA k 

-- -- --       w : Iso (A × Σ (List A) (λ xs → length xs ≡ k))
-- -- --             (Σ (B.List A) (λ xs → B.length xs ≡ suc k))
-- -- --       Iso.fun w (a , x) = a B.∷  fst (Iso.fun w' x)  , cong suc ((snd (Iso.fun w' x)))
-- -- --       Iso.inv w (B.[] , p) = ⊥rec (znots p)
-- -- --       Iso.inv w (a B.∷ l , p) = a , (Iso.inv w' (l , injSuc p))
-- -- --       Iso.rightInv w (B.[] , p) = ⊥rec (znots p)
-- -- --       Iso.rightInv w (a B.∷ l , p) =
-- -- --             Σ≡Prop (λ _ → isSetℕ _ _)
-- -- --              (cong (a B.∷_) (cong fst (Iso.rightInv w' (l , injSuc p))))

-- -- --       Iso.leftInv w _ = ΣPathP (refl ,  Iso.leftInv w' _)
