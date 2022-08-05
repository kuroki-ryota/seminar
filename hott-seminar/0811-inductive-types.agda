{-# OPTIONS --without-K --safe #-}
module 0811-inductive-types where
open import Agda.Primitive renaming (Set to Type) public

variable
  ℓ : Level
  A B C : Type ℓ

infix 4 _,_
data _×_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  _,_ : (x : A) → (y : B) → A × B

data Unit : Type where
  star : Unit

-- inductive
data Σ' {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : A → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  _,_ : (x : A) → B x → Σ' A B

-- coinductive
record Σ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : A → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    x : A
    y : B x

open Σ public
syntax Σ A (λ x → Bx) = Σ x ꞉ A , Bx

data _+_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  inl : (x : A) → A + B
  inr : (y : B) → A + B

data Empty : Type where

data Bool : Type where
  tt ff : Bool

data ℕ : Type where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infix 4 _≡_
-- based identity type
data _≡_ {A : Type ℓ} (a : A) : A → Type ℓ where
  refl : a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}

module unbased-id where
  infix 4 _≡'_
  -- unbased identity type
  data _≡'_ {A : Type ℓ} : A → A → Type ℓ where
    refl : {a : A} → a ≡' a