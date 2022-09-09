{-# OPTIONS --without-K --rewriting #-}
module 0916-Trunc where
open import 0909-prelude public

postulate
  ∥_∥ : Type ℓ → Type ℓ

  ∣_∣ : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y

  Trunc-rec :
    (A → C)
    → ((x y : C) → x ≡ y)
    → ∥ A ∥ → C
  
  Trunc-rec-in :
    (f : A → C)
    → (p : (x y : C) → x ≡ y)
    → (a : A) → Trunc-rec f p ∣ a ∣ ≡ f a

  {-# REWRITE Trunc-rec-in #-}

  Trunc-rec-squash :
    (f : A → C)
    → (p : (x y : C) → x ≡ y)
    → (x y : ∥ A ∥)
    → ap (Trunc-rec f p) (squash x y) ≡ p (Trunc-rec f p x) (Trunc-rec f p y)