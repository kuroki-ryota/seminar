{-# OPTIONS --cubical --safe #-}
module Path where

open import Prelude hiding (_⁻¹ ; _∙_ ; hfill)

-- x y : A
-- i0 i1 : I
-- p : x ≡ y は、 p i0 = x, p i1 = y となる p : I → A
-- ~ : I → I
-- ~ i0 = i1 , ~ i1 = i0

-- γ : [0,1] → A と似ている
-- x を 1-x に写す [0,1] → [0,1]

infix 50 _⁻¹
_⁻¹ : {x y : A} → x ≡ y → y ≡ x
_⁻¹ p i = p (~ i)

-- homogeneous composition (hcomp)

infixr 30 _∙_
_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} {y} p q i =
  -- hcomp (λ j → λ { (i = i0) → p (~ j)
  --                ; (i = i1) → q j}) y
  hcomp (λ j → λ { (i = i0) → x
                 ; (i = i1) → q j}) (p i)

∙-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → Square p (p ∙ q) refl q
∙-filler {x = x} p q i j =
  hcomp (λ k → λ { (i = i0) → p j
                 ; (j = i0) → x
                 ; (j = i1) → q (i ∧ k)})
        (p j)

-- ∧ : I → I → I
-- ∨
-- min : [0,1] → [0,1] → [0,1] 

hfill : {A : Type ℓ}
        {φ : I}
        (u : ∀ i → Partial φ A)
        (u0 : A [ φ ↦ u i0 ])
        (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)

∙-filler' : {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → Square p (p ∙ q) refl q
∙-filler' {x = x} p q i j =
  hfill (λ k → λ { (j = i0) → x
                 ; (j = i1) → q k})
        (inS (p j)) i