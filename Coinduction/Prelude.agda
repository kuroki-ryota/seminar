{-# OPTIONS --cubical --guardedness --safe #-}
module Prelude where
open import Agda.Primitive public
open import Cubical.Foundations.Prelude public

variable
  ℓ : Level
  A B C : Type ℓ

id : A → A
id a = a

_∘_ : (g : B → C) (f : A → B) → A → C
_∘_ g f a = g (f a)

ap : (f : A → B) {a b : A} (p : a ≡ b) → f a ≡ f b
ap f p i = f (p i)


data ⊥ : Type where

¬ : Type ℓ → Type ℓ
¬ A = A → ⊥

absurd : ⊥ → A
absurd ()

data Unit : Type where
  star : Unit

infixr -1 _+_

data _+_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  inl : A → A + B
  inr : B → A + B

infixr -1 _×_
infixr 4 _,_

record _×_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : A
    snd : B

data Bool : Type where
  tt ff : Bool

Bool→Type : Bool → Type
Bool→Type tt = Unit
Bool→Type ff = ⊥

tt≠ff : ¬ (tt ≡ ff)
tt≠ff p = transport (λ i → Bool→Type (p i)) star

Σ' : (A : Type ℓ) (B : A → Type ℓ) → Type ℓ
Σ' = Σ
syntax Σ' B (λ x → Ex) = Σ x ꞉ B , Ex

data 1+ (A : Type) : Type where
  nothing : 1+ A
  just : A → 1+ A

1+→Type : 1+ A → Type
1+→Type nothing  = Unit
1+→Type (just x) = ⊥

nth≠just : {x : A} → ¬ (nothing ≡ just x)
nth≠just {x = x} p = transport (ap 1+→Type p) star
