{-# OPTIONS --without-K --rewriting #-}
module 0909-S1 where
open import 0909-prelude public

postulate
  S1 : Type

  base : S1
  loop : base ≡ base

  S1-rec : (x : C) (p : x ≡ x) → S1 → C
  
  S1-rec-base : (x : C) (p : x ≡ x)
                  → S1-rec x p base ≡ x
                  
  {-# REWRITE S1-rec-base #-}

  S1-rec-loop : (x : C) (p : x ≡ x)
              → ap (S1-rec x p) loop ≡ p