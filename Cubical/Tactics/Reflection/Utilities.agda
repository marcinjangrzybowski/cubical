{-# OPTIONS --safe #-}
module Cubical.Tactics.Reflection.Utilities where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)

open import Cubical.Reflection.Base
open import Cubical.Data.List as L
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.FinData using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; suc; _+_; zero; _∸_; discreteℕ; predℕ)

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables


finiteNumberAsTerm : Maybe ℕ → Term
finiteNumberAsTerm (just ℕ.zero) = con (quote fzero) []
finiteNumberAsTerm (just (ℕ.suc n)) = con (quote fsuc) (finiteNumberAsTerm (just n) v∷ [])
finiteNumberAsTerm _ = unknown

-- error message helper
errorOut : List (Arg Term) → TC (Template × Vars)
errorOut something = typeError (strErr "Don't know what to do with " ∷ map (λ {(arg _ t) → termErr t}) something)

errorOut' : Term → TC (Template × Vars)
errorOut' something = typeError (strErr "Don't know what to do with " ∷ termErr something ∷ [])


_==_ = primQNameEquality
{-# INLINE _==_ #-}

module _ {M : Functorω} {{_ : RawApplicative M}} {{_ : RawMonad M}} where 

 mapM : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
            → (A → M B) → List A → M (List B)
 mapM f [] = ⦇ [] ⦈
 mapM f (x ∷ xs) = ⦇ f x ∷ mapM f xs ⦈

 concatMapM : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
            → (A → M (List B)) → List A → M (List B)
 concatMapM f [] = ⦇ [] ⦈
 concatMapM f (x ∷ xs) = ⦇ f x ++ concatMapM f xs ⦈


 foldlM : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
            → (B → A → M B) → B → List A → M B
 foldlM f b [] = pure b
 foldlM f b (x ∷ xs) = f b x >>= (flip (foldlM f)) xs


 foldrM : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
            → (A → B → M B) → B → List A → M B
 foldrM f b [] = pure b
 foldrM f b (x ∷ xs) = foldrM f b xs >>= f x


State₀T : Type → Functorω → Functorω 
State₀T S F T = S → F (T × S)


get : {F : Functorω} {{FA : RawApplicative F }} {{FM : RawMonad F }} {S : Type}  → [ State₀T S RMT F ] S
unwrap get s = pure (s , s)

modify : {F : Functorω} {{FA : RawApplicative F }} {{FM : RawMonad F }} {S : Type}  →
  (S → S) → [ State₀T S RMT F ] Unit
unwrap (modify f) s = pure (_ , f s)


Plus₀T : Type → Functorω → Functorω 
Plus₀T E F T = F (E ⊎.⊎ T) 

module _ where
 open RawMonadTransformer

 instance
  rawMonadTransformerState₀ : ∀ {S} → RawMonadTransformer (State₀T S)
  (applicativeLiftT rawMonadTransformerState₀ RawApplicative.<$> x) = (map-fst x <$>_) ∘S_
  RawApplicative.pure (applicativeLiftT rawMonadTransformerState₀) x = pure ∘S (x ,_)
  (applicativeLiftT rawMonadTransformerState₀ RawApplicative.<*> f) x s = 
    f s >>= uncurry (_<$>_ ∘S map-fst) ∘S map-snd x
    
  (monadLiftT rawMonadTransformerState₀ RawMonad.>>= x) y s = x s >>= uncurry y
      
  (monadLiftT rawMonadTransformerState₀ RawMonad.>> x) y s = x s >>= y ∘S snd
  lifting rawMonadTransformerState₀ x s = (_, s) <$> x

  rawMonadTransformerPlus₀ : ∀ {S} → RawMonadTransformer (Plus₀T S)
  (applicativeLiftT rawMonadTransformerPlus₀ RawApplicative.<$> x) =
    (⊎.map (idfun _) x) <$>_
  RawApplicative.pure (applicativeLiftT rawMonadTransformerPlus₀) x = pure (⊎.inr x)
  (applicativeLiftT rawMonadTransformerPlus₀ RawApplicative.<*> f) x =
    f >>= ⊎.rec (pure ∘S ⊎.inl) λ f → ⊎.map (idfun _) f <$> x
  (monadLiftT rawMonadTransformerPlus₀ RawMonad.>>= x) y =
    x >>= ⊎.rec (pure ∘S ⊎.inl) y
  (monadLiftT rawMonadTransformerPlus₀ RawMonad.>> x) y =
    x >>= ⊎.rec (pure ∘S ⊎.inl) (const y)
  lifting rawMonadTransformerPlus₀ x = ⊎.inr <$> x

  
  ApplicativeSum : {E : Type} → RawApplicative (E ⊎.⊎_) 
  ApplicativeSum = applicativeLiftT rawMonadTransformerPlus₀ {{_}} {{RawMonadIdentityM}} 

  MonadSum : {E : Type} → RawMonad (E ⊎.⊎_) 
  MonadSum = monadLiftT rawMonadTransformerPlus₀ {{_}} {{RawMonadIdentityM}} 



instance
 ApplicativeMaybe : RawApplicative Maybe
 RawApplicative._<$>_ ApplicativeMaybe = map-Maybe
 RawApplicative.pure ApplicativeMaybe = just
 (ApplicativeMaybe RawApplicative.<*> nothing) x₁ = nothing
 (ApplicativeMaybe RawApplicative.<*> just x) nothing = nothing
 (ApplicativeMaybe RawApplicative.<*> just x) (just x₁) = just (x x₁)


 MonadMaybe : RawMonad Maybe
 RawMonad._>>=_ MonadMaybe = flip (Mb.rec nothing)
 RawMonad._>>_ MonadMaybe = flip (Mb.rec nothing ∘ const)

 ApplicativeList : RawApplicative List
 RawApplicative._<$>_ ApplicativeList = L.map
 RawApplicative.pure ApplicativeList = [_]
 (ApplicativeList RawApplicative.<*> fs) xs = L.map (uncurry _$_) (cart fs xs)
 

 MonadList : RawMonad List
 RawMonad._>>=_ MonadList xs f = L.join (map f xs)
 RawMonad._>>_ MonadList xs ys = L.join (map (λ _ → ys) xs)


when : ∀ {M : Functorω} {{_ : RawApplicative M}} → Bool → M Unit → M Unit
when {M} false x = pure _
when {M} true x = x

module atVarOrConOrDefMmp {M : Functorω}
              {{RA : RawApplicative M}} {{_ : RawMonad M {{RA}} }} 
              (f : ℕ → ℕ → (List (Arg Term)) → M (List (Arg Term)) → (List (M (Arg Term))) → (M Term))
              (h : ℕ → Name → (List (Arg Term)) → M (List (Arg Term)) → (List (M (Arg Term))) → (M Term))
              (g : ℕ → Name → (List (Arg Term)) → M (List (Arg Term)) → (List (M (Arg Term))) → (M Term))
              where
              
 ra : ℕ → List (Arg Term) → M (List (Arg Term))
 raT : ℕ → List (Arg Term) → (List (M (Arg Term)))
 rc : ℕ → List Clause → M (List Clause)
 rcl : ℕ → Clause → M Clause
 rtl : ℕ → Telescope → M Telescope
 rv : ℕ →  Term → M Term

 rpt : ℕ → Pattern → M Pattern
 rpts : ℕ → List (Arg Pattern) → M (List (Arg Pattern))
 rs : ℕ →  Sort → M Sort

 ra n [] = ⦇ [] ⦈
 ra n (arg i x ∷ x₂) = 
   ⦇ ⦇ (arg i) (rv n x) ⦈ ∷ ra n x₂ ⦈

 raT n [] = []
 raT n (arg i x ∷ x₂) = 
   ⦇ (arg i) (rv n x) ⦈ ∷ raT n x₂ 

 rv n (var x args) = f n x args (ra n args) (raT n args)
 rv n (con c args) = h n c args (ra n args) (raT n args)
 rv n (def f' args) = g n f' args (ra n args) (raT n args)  
 rv n (lam v₁ (abs s x)) =
   (lam v₁) <$> (abs s <$> (rv (suc n) x))
 rv n (pat-lam cs args) = ⦇ pat-lam (rc n cs) (ra n args) ⦈
 rv n (pi (arg i x) (abs s x₁)) =
  ⦇ pi ((arg i) <$> rv n x) (abs s <$> rv (suc n) x₁) ⦈
 rv n (agda-sort s) = ⦇ agda-sort (rs n s) ⦈
 rv n (lit l) = ⦇ (lit l) ⦈
 rv n (meta x x₁) = ⦇ meta ⦇ x ⦈ (ra n x₁) ⦈
 rv n unknown = ⦇ unknown ⦈


 rs n (set t) = ⦇ set (rv n t) ⦈
 rs n (lit n₁) = ⦇ (lit n₁) ⦈
 rs n (prop t) = ⦇ prop (rv n t) ⦈
 rs n (propLit n₁) = ⦇ (propLit n₁) ⦈
 rs n (inf n₁) = ⦇ (inf n₁) ⦈
 rs n unknown = ⦇ unknown ⦈

 rtl n [] = ⦇ [] ⦈
 rtl n ((v , arg i x) ∷ xs) =
    ⦇ ⦇ ⦇ v ⦈ , ⦇ arg ⦇ i ⦈ (rv n x) ⦈ ⦈ ∷ rtl (suc n) xs ⦈

 rc n [] = ⦇ [] ⦈
 rc n (cl ∷ cls) =
   ⦇ rcl n cl ∷ rc n cls ⦈


 rcl n (clause tel ps t) =
   ⦇ clause (rtl n tel) (rpts n ps) (rv (length tel + n) t) ⦈
 rcl n (absurd-clause tel ps) =
   ⦇ absurd-clause (rtl n tel) (rpts n ps) ⦈



 rpt n (con c ps) = con c <$> (rpts n ps)
 rpt n (dot t) = dot <$> (rv n t)
 rpt n (var x) = pure $ var x
 rpt n (lit l) = pure $ lit l
 rpt n (proj f) = pure $ proj f
 rpt n (absurd x) = pure $ absurd x

 rpts n [] = ⦇ [] ⦈
 rpts n ((arg i x) ∷ xs) = ⦇ ⦇ arg ⦇ i ⦈ (rpt n x) ⦈ ∷ rpts n xs ⦈

 rv0 = rv 0

atVarOrConOrDefMmp = atVarOrConOrDefMmp.rv0


module atVarOrDefMmp {M : Functorω}
              {{RA : RawApplicative M}} {{RM : RawMonad M {{RA}} }} 
              (f : ℕ → ℕ → (List (Arg Term)) → M (List (Arg Term)) → (List (M (Arg Term))) → (M Term))
              (g : ℕ → Name → (List (Arg Term)) → M (List (Arg Term)) → (List (M (Arg Term))) → (M Term))
              where
 open atVarOrConOrDefMmp {M} {{RA}} {{RM}}
         f
         (λ n c _ argsM _ → _<$>_ {M = M} (con c)  argsM)
         g public


atVarOrDefMmp = atVarOrDefMmp.rv0


module atVarOrDefM {M : Functorω}
              {{RA : RawApplicative M}} {{RM : RawMonad M {{RA}} }} 
              (f : ℕ → ℕ → (List (Arg Term)) → M (List (Arg Term)) → (M Term))
              (g : ℕ → Name → (List (Arg Term)) → M (List (Arg Term)) → (M Term))
              where
              
 open atVarOrDefMmp {M = M}
              {{RA}} {{RM }}
              (λ n k l l' _ → f n k l l')
              (λ n k l l' _ → g n k l l') public

atVarOrDefM = atVarOrDefM.rv0

atVarOrM : (ℕ → ℕ → List (Arg Term) → Maybe Term) → (ℕ → Name → List (Arg Term) → Maybe Term) → Term → Term
atVarOrM f g = rv zero
 where
 open atVarOrDefM {{_}} {{RawMonadIdentityM}}
    (λ n k _ args →  
          let t = var k args
              t' = (Mb.fromMaybe t (f n (k ∸ n) args))
          in (if (k <ℕ n) then t else t'))
   (λ n nm _ args →  
          let t = def nm args
          in  Mb.fromMaybe t (g n nm args))

atVarOrM' : (ℕ → ℕ → List (Arg Term) → Maybe Term) → (ℕ → Name → List (Arg Term) → Maybe Term) → Term → Term
atVarOrM' f g = rv zero
 where
 open atVarOrDefM {{_}} {{RawMonadIdentityM}}
    (λ n k args0 args →  
          let t = var k args
              t' = (Mb.fromMaybe t (f n (k ∸ n) args0))
          in (if (k <ℕ n) then t else t'))
   (λ n nm args0 args →  
          Mb.fromMaybe (def nm args) (g n nm args0))

atVarOrConM' : (ℕ → ℕ → List (Arg Term) → Maybe Term) →
 (ℕ → Name → List (Arg Term) → Maybe Term)
 → (ℕ → Name → List (Arg Term) → Maybe Term) → Term → Term
atVarOrConM' f h g = rv zero
 where
 open atVarOrConOrDefMmp {{_}} {{RawMonadIdentityM}}
    (λ n k args0 args _ →  
          let t = var k args
              t' = (Mb.fromMaybe t (f n (k ∸ n) args0))
          in (if (k <ℕ n) then t else t'))
   (λ n nm args0 args _ →  
          Mb.fromMaybe (con nm args) (h n nm args0))
   (λ n nm args0 args _ →  
          Mb.fromMaybe (def nm args) (g n nm args0))



module atVarM {M : Functorω}
              {{RA : RawApplicative M}} {{RM : RawMonad M {{RA}} }} 
              (f : ℕ → ℕ → List (Arg Term) → Maybe (M Term)) where


 open atVarOrDefM
      (λ n k _ args → RawMonad._>>=_ RM args λ args → 
          let t = var k args
          in (Mb.fromMaybe (RawApplicative.pure RA t) (if (k <ℕ n) then nothing else (f n (k ∸ n) args))))
      (λ n nm _ args → RawMonad._>>=_ RM args λ args → RawApplicative.pure RA (def nm args))
      public

module atVar (f : ℕ → ℕ → List (Arg Term) → Maybe (Term)) where
 
 open atVarM 
      {{_}}
      {{RawMonadIdentityM}} f
      public

atVarM : {M : Functorω}
              {{RA : RawApplicative M}} {{_ : RawMonad M {{RA}} }} 
              (f : ℕ → ℕ → List (Arg Term) → Maybe (M Term)) → Term → M Term
atVarM f = atVarM.rv f zero 


atVar : (ℕ → ℕ → List (Arg Term) → Maybe Term) → Term → Term
atVar f = atVar.rv f zero

remapVars : (ℕ → ℕ) → Term → Term 
remapVars f = atVar λ n k args → just (var (f k + n) args)


-- only for not applied vars!!
replaceVarWithCon : (ℕ → (Maybe Name)) → Term → Term
replaceVarWithCon f = atVar λ n k args → map-Maybe (λ nm → con nm []) (f k)

liftVars : Term → Term
liftVars = atVar λ n k args → just (var (n + suc k) args)

liftVarsFrom : ℕ → ℕ → Term → Term
liftVarsFrom m = atVar.rv (λ n k args → just (var (n + m + k) args))


module LiftFrom (m : ℕ) where
 open atVar (λ n k args → just (var (n + m + k) args)) public

 

dropVar : ℕ → Term → Term
dropVar = atVar.rv (λ n k args → just (var (n + predℕ k) args))



module dropVars (m : ℕ) where
 open atVar (λ n k args → just (var (n + (k ∸ m)) args)) public



invVar : ℕ → Term → Term
invVar m = atVar λ where
    n k [] → if (Dec→Bool (discreteℕ m k) )
              then just (def (quote ~_) v[ var (k + n) [] ])
              else nothing
    _ _ _ → nothing
   





hasVar : ℕ → Term → Bool
hasVar k' tm = snd $ runIdentity $ (unwrap (atVarM f tm) false)
  where
    f : ℕ → ℕ → List (Arg Term) → Maybe ([ State₀T Bool RMT IdentityF ] Term)
    f n k args = just (wrap (pure ∘S ((var (n + k) args ,_)) ∘S (λ where
        true → true
        false → k =ℕ k'
      )))

hasVarBy : (ℕ → Bool) → Term → Bool
hasVarBy g tm = snd $ runIdentity $ (unwrap (atVarM f tm) false)
  where
    f : ℕ → ℕ → List (Arg Term) → Maybe ([ State₀T Bool RMT IdentityF ] Term)
    f n k args = just (wrap (pure ∘S ((var (n + k) args ,_)) ∘S (λ where
        true → true
        false → g k
      )))



findInterval : ℕ → Term → Maybe Term
findInterval dim tm =
  snd $ runIdentity $ (unwrap {T = State₀T (Maybe Term)} (atVarOrDefM.rv
     (λ n k _ args' →
      let z =  (runIdentity (unwrap args' nothing))
      in wrap (identity ∘S (var k (fst z) ,_) ∘S
             (_mb>> snd z ∘S  _mb>> f n k (fst z))))
     (λ n nm _ args' →
      let z =  (runIdentity (unwrap args' nothing)) 
      in wrap
           (identity ∘S (def nm (fst z) ,_) ∘S 
              (_mb>> snd z
                ∘S _mb>> (map-Maybe (dropVars.rv n zero) (g nm (fst z) (def nm (fst z)))))))
     0 tm) nothing)
  where

    _mb>>_ : Maybe Term → Maybe Term → Maybe Term
    nothing mb>> x₁ = x₁
    just x mb>> _ = just x


    f : ℕ → ℕ → List (Arg Term) → Maybe Term
    f n x [] =
         if (n <ℕ (suc x)) and (x <ℕ (n + dim))
         then just (var (x ∸ n) [])
         else nothing
    f n k (x ∷ args) = nothing
      
    g :  Name → List (Arg Term) → Term → Maybe Term
    g (quote _∨_) a@(_ v∷ v[ _ ]) tm = just tm
    g (quote _∧_) a@(_ v∷ v[ _ ]) tm = just tm
    g (quote ~_) a@(v[ _ ]) tm = just tm
    g _ _ _ = nothing


replaceVarWithTerm : (ℕ → Maybe Term) → Term → Term
replaceVarWithTerm f = 
   atVar λ n k _ →
       map-Maybe (liftVarsFrom n zero) (f k)


substTms : List Term → Term →  Term
substTms xs = dropVars.rv (length xs) zero ∘S replaceVarWithTerm (lookup (map (liftVarsFrom (length xs) 0) xs))

replaceAtTrm : ℕ → Term → Term → Term
replaceAtTrm k t =
 dropVar k ∘ replaceVarWithTerm (z k)

 where
 z : ℕ → ℕ → Maybe Term
 z zero zero = just t 
 z zero (suc y) = nothing
 z (suc x) zero = nothing
 z (suc x) (suc y) = z x y
