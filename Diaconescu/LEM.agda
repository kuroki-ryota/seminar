{-# OPTIONS --cubical --safe #-}
module LEM where
open import Bool public

-- 型でパラメトライズされた項 の型
param : (F : Type → Type) → Type₁
param F = (A : Type) → F A

-- impredicative encoding
⊥' = (A : Type) → A

⊤' = (A : Type) → (A → A)
star' : ⊤'
star' A = λ x → x

module _ (X Y : Type) where
  _+'_ = (A : Type) → ((X → A) → (Y → A) → A)
  _×'_ = (A : Type) → ((X → Y → A) → A)

module _ (X Y : Type) where
  inl' : X → X +' Y
  inl' x A = λ f g → f x
  inr' : Y → X +' Y
  inr' y A = λ f g → g y

Bool' = (A : Type) → (A → A → A)
tt' ff' : Bool'
tt' A = λ x y → x
ff' A = λ x y → y

ℕ' = (A : Type) → (A → (A → A) → A)
0' 1' 2' : ℕ'
0' A = λ x f → x
1' A = λ x f → f x
2' A = λ x f → f (f x)


⊥'-empty : ¬ ⊥'
⊥'-empty f = f ⊥

-- excluded middle

LEM∞ = (A : Type) → dec A

fixed : {A : Type} {F : Type → Type} (f : (X : Type) → F X)
  → (p : A ≡ A) → transport (ap F p) (f A) ≡ f A
fixed {A = A} {F} f p = apd F f p

¬LEM∞ : ¬ LEM∞
¬LEM∞ em∞ = tt≠ff (lemma₂ y lemma₁) where
  x y : dec Bool
  x = transport (ap dec notpath) (em∞ Bool)
  y = em∞ Bool
  lemma₁ : x ≡ y
  lemma₁ = fixed em∞ notpath

  inl⁻¹ : (a : A) → (A + B → A)
  inl⁻¹ a (inl x) = x
  inl⁻¹ a (inr x) = a
  lemma₂ : (y : dec Bool) → transport (ap dec notpath) y ≡ y
    → tt ≡ ff
  lemma₂ y with y
  ... | inl tt = λ p → ap (inl⁻¹ tt) (p ⁻¹)
  ... | inl ff = λ p → ap (inl⁻¹ ff) p
  ... | inr f = absurd (f tt)

LEM : Type₁
LEM = (A : Type) → isProp A → dec A