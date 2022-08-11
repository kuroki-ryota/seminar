{-# OPTIONS --cubical --safe #-}
module S1 where
open import LEM
open import Trunc

data S¹ : Type where
  base : S¹
  loop : base ≡ base

S¹2Type : S¹ → Type
S¹2Type base = Bool
S¹2Type (loop i) = ua (not , notIsEquiv) i

-- ループの偶奇
parity : base ≡ base → Bool
parity p = transport (λ i → S¹2Type (p i)) tt

_ : parity refl ≡ tt
_ = refl

_ : parity loop ≡ ff
_ = refl

_ : parity (sym loop) ≡ ff
_ = refl

_ : parity (loop ∙ loop) ≡ tt
_ = refl
-- これらが refl で示せるのは canonicity のおかげ

refl≠loop : ¬ (refl ≡ loop)
refl≠loop refl≡loop = tt≠ff (λ i → parity (refl≡loop i))

¬isSetS¹ : ¬ (isSet S¹)
¬isSetS¹ isSetS¹ = refl≠loop (isSetS¹ _ _ refl loop)


module LEM∞ where
  open Hedberg 
  ¬LEM∞' : ¬ LEM∞
  ¬LEM∞' lem∞ = ¬isSetS¹ (Hedberg (λ _ _ → lem∞ _))




-- （弧状）連結性 (0-connectedness)
iscnd : Type → Type
iscnd A = Σ a ꞉ A , ((x : A) → ∥ a ≡ x ∥)
-- 「set truncation を取ると可縮」という定義でも良い


S¹cnd-base : (x : S¹) → ∥ base ≡ x ∥
S¹cnd-base base     = ∣ refl ∣
S¹cnd-base (loop i) = squash ∣ (λ j → loop (i ∧ j)) ∣ ∣ (λ j → loop (i ∨ ~ j)) ∣ i

S¹cnd : iscnd S¹
S¹cnd = base , S¹cnd-base
 