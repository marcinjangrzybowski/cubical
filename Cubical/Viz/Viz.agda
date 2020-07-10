{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Viz.Viz where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything

variable

  A : Type₀
  x y z w : A
  p : x ≡ y
  q : y ≡ z


test0 : PathP (λ _ → A) x z 
test0 {A} i  = {!assoc !}



-- IOTCM "Viz.agda" NonInteractive Indirect (Cmd_load "Viz.agda" [])
-- IOTCM "Viz.agda" None Indirect (Cmd_show_module_contents_toplevel Simplified "")
