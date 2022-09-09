{-# OPTIONS --without-K --rewriting #-}
module 0916-Quot where
open import 0909-prelude public

postulate
  _∥_ : (A : Type ℓ) → (A → A → Type ℓ) → Type ℓ

  inquot : {R : A → A → Type ℓ}
    → A → A ∥ R

  squashquot : {R : A → A → Type ℓ}
    → ∀ {x y} → R x y
    → inquot x ≡ inquot y [ A ∥ R ] 

  Quot-rec : {R : A → A → Type ℓ}
    → (f : A → C)
    → (∀ {x y} → R x y → f x ≡ f y)
    → A ∥ R → C
  
  -- quotient からの関数の well-definedness を確かめることは
  -- path constructor の行き先を定めることに相当する


  Quot-rec-in : {R : A → A → Type ℓ}
    → (f : A → C)
    → (p : ∀ {x y} → R x y → f x ≡ f y)
    → (a : A) → Quot-rec f p (inquot a) ≡ f a

  {-# REWRITE Quot-rec-in #-}

  Quot-rec-squash : {R : A → A → Type ℓ}
    → (f : A → C)
    → (p : ∀ {x y} → R x y → f x ≡ f y)
    → ∀ {x y} → (x∼y : R x y) → f x ≡ f y
    → ap (Quot-rec f p) (squashquot x∼y) ≡ p x∼y