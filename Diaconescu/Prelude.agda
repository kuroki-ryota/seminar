{-# OPTIONS --cubical --safe #-}
module Prelude where

open import Agda.Primitive
-- open import Agda.Builtin.Nat hiding (_+_) renaming (Nat to ℕ) public
open import Cubical.Core.Glue public
open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Isomorphism public

variable
  ℓ : Level
  A B C : Type ℓ

_∘_ : (f : B → C) (g : A → B) → (A → C)
(f ∘ g) x = f (g x)

data ⊥ : Type where

absurd : ⊥ → A
absurd ()

¬ : Type ℓ → Type ℓ
¬ A = A → ⊥



data Unit : Type where
  star : Unit

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}


data _+_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  inl : A → A + B
  inr : B → A + B


Σ' : (A : Type ℓ) (B : A → Type ℓ) → Type ℓ
Σ' = Σ
syntax Σ' B (λ x → E-x) = Σ x ꞉ B , E-x

pr₁ : {B : A → Type ℓ} → Σ x ꞉ A , B x → A
pr₁ (a , b) = a
pr₂ : {B : A → Type ℓ} → (p : Σ x ꞉ A , B x) → B (pr₁ p)
pr₂ (a , b) = b

--  homotopy fiber
_⁻¹_ : {A B : Type ℓ} (f : A → B) → B → Type ℓ
f ⁻¹ y = Σ x ꞉ _ , (f x ≡ y)

id : A → A
id a = a

_⁻¹ : {x y : A} → x ≡ y → y ≡ x
_⁻¹ = sym

ap : (f : A → B) {a b : A} (p : a ≡ b) → f a ≡ f b
ap f p i = f (p i)

apd : (B : A → Type) (f : (x : A) → B x) {x y : A} (p : x ≡ y)
  → (transport (ap B p) (f x)) ≡ f y
apd B f {x} {y} p i =
  comp (λ j → B (p j))
  (λ j → λ { (i = i0) → transport (ap B (λ k → p (k ∧ j))) (f x)
           ; (i = i1) → f (p j)})
  (transp (λ i → B x) i (f x))

apd' : (B : A → Type) (f : (x : A) → B x) {x y : A} (p : x ≡ y)
  → (transport (ap B p) (f x)) ≡ f y
apd' B f {x} {y} p = transport lemma₁ lemma₂ where
  lemma₁ : (transport (ap B refl) (f x) ≡ f x) ≡
    (transport (ap B p) (f x) ≡ f y)
  lemma₁ i = transport (ap B λ j → p (i ∧ j)) (f x) ≡ f (p i)
  lemma₂ : (transport (ap B refl) (f x)) ≡ f x
  lemma₂ i = transp (λ i → B x) i (f x)


dec : Type ℓ → Type ℓ
dec A = A + ¬ A