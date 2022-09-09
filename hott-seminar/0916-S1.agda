{-# OPTIONS --without-K --rewriting #-}
module 0916-S1 where
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


-- S1 (6.4)
  -- ¬ (loop ≡ refl)
  -- (base ≡ base) ≃ int （やらない）
-- truncation , quotient type (6.9 , 6.10)
  -- well-definedness と除去則の関係