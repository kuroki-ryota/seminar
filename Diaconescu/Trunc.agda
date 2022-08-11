{-# OPTIONS --cubical --safe #-}
module Trunc where
open import Hlevel public


-- propositional truncation
data ∥_∥ (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ y


islv1proptrunc : isProp ∥ A ∥
islv1proptrunc x y = squash x y


issurj : {A B : Type ℓ} (f : A → B) → Type ℓ
issurj f = (y : _) → ∥ f ⁻¹ y ∥

