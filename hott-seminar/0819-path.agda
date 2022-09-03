{-# OPTIONS --without-K --safe #-}
module 0819-path where
open import 0811-inductive-types public

private variable
  x y z w : A

comp : x ≡ y → y ≡ z → x ≡ z
comp refl p = p
inv : x ≡ y → y ≡ x
inv refl = refl

infix 9 _∙_
_∙_ = comp
! = inv

module GroupoidLaws where
  runit : (p : x ≡ y) → p ∙ refl ≡ p
  runit refl = refl
  lunit : (p : x ≡ y) → refl ∙ p ≡ p
  lunit refl = refl
  rinv : (p : x ≡ y) → p ∙ ! p ≡ refl
  rinv refl = refl
  linv : (p : x ≡ y) → ! p ∙ p ≡ refl
  linv refl = refl
  invol : (p : x ≡ y) → ! (! p) ≡ p
  invol refl = refl
  assoc : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
    → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
  assoc refl q r = refl