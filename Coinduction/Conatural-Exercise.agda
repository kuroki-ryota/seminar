{-# OPTIONS --cubical --guardedness --safe #-}
module Conatural-Exercise where
open import Conatural public

infix 10 _≥_

_≥_ : ℕ∞ → ℕ → Bool
x ≥ zero  = tt
x ≥ suc n with prd∞ x
... | nothing = ff
... | just x' = x' ≥ n

_ : ∞ ≥ 3 ≡ tt
_ = refl

_ : 1∞ ≥ 1 ≡ tt
_ = refl

_ : 1∞ ≥ 2 ≡ ff
_ = refl

infixl 18 _+∞_

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
prd∞ (m +∞ n) with prd∞ n
... | nothing = prd∞ m
... | just n' = just (m +∞ n')

-- (m + n) - 1 = m + (n - 1)

⟨_⟩ = ℕ→ℕ∞

_ : ⟨ 3 ⟩ +∞ ⟨ 2 ⟩ ≥ 5 ≡ tt
_ = refl

_ : ⟨ 3 ⟩ +∞ ⟨ 2 ⟩ ≥ 6 ≡ ff
_ = refl


-- {-# TERMINATING #-}
-- _×∞'_ : ℕ∞ → ℕ∞ → ℕ∞
-- prd∞ (m ×∞' n) with prd∞ n
-- ... | nothing = nothing
-- ... | just n' = prd∞ ((m ×∞' n') +∞ m)

-- -- m × n - 1 = m × (n - 1) + m - 1

-- {-# TERMINATING #-}
-- _×∞''_ : ℕ∞ → ℕ∞ → ℕ∞
-- prd∞ (m ×∞'' n) with prd∞ n
-- ... | nothing = nothing
-- ... | just n' with prd∞ m
-- ... | nothing = nothing
-- ... | just m' = just (m' ×∞'' n' +∞ m' +∞ n')

-- -- m × n - 1 = (m - 1) × (n - 1) + (m - 1) + (n - 1)

-- _ : ⟨ 2 ⟩ ×∞' ⟨ 3 ⟩ ≥ 6 ≡ tt
-- _ = refl

-- _ : ⟨ 2 ⟩ ×∞' ⟨ 3 ⟩ ≥ 7 ≡ ff
-- _ = refl

-- 格子点の数え上げによる実装
_×∞_ : ℕ∞ → ℕ∞ → ℕ∞
m ×∞ n = f (m , n) where
  f : ℕ∞ × ℕ∞ → ℕ∞
  f = ℕ∞-corec' g where
    g : ℕ∞ × ℕ∞ → 1+ (ℕ∞ × ℕ∞)
    g (x , y) with prd∞ x
    ...       | nothing = nothing
    ...       | just x' with prd∞ x'
    ...                 | nothing with prd∞ y
    ...                   | nothing = nothing
    ...                   | just y' with prd∞ y'
    ...                     | nothing  = just (1∞ , 0∞)
    ...                     | just y'' = just (m , y')
    g (x , y) | just x' | just x'' = just (x' , y)

_ : ⟨ 3 ⟩ ×∞ ⟨ 5 ⟩ ≥ 15 ≡ tt
_ = refl

_ : ⟨ 3 ⟩ ×∞ ⟨ 5 ⟩ ≥ 16 ≡ ff
_ = refl

-- 格子点を数えるなら λ m n → (m + 1) × (n + 1) - 1 の実装が自然になる
_×∞₁_ : ℕ∞ → ℕ∞ → ℕ∞
m ×∞₁ n = f (m , n) where
  f : ℕ∞ × ℕ∞ → ℕ∞
  f = ℕ∞-corec' g where
    g : ℕ∞ × ℕ∞ → 1+ (ℕ∞ × ℕ∞)
    g (x , y) with prd∞ x
    ... | just x' = just (x' , y)
    ... | nothing with prd∞ y
    ...   | nothing = nothing
    ...   | just y' = just (m , y')

_ : ⟨ 2 ⟩ ×∞₁ ⟨ 4 ⟩ ≥ 14 ≡ tt
_ = refl

_ : ⟨ 2 ⟩ ×∞₁ ⟨ 4 ⟩ ≥ 15 ≡ ff
_ = refl
