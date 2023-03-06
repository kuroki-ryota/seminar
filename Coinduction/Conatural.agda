{-# OPTIONS --cubical --guardedness --safe #-}
module Conatural where
open import Natural public

record ℕ∞ : Type where
  coinductive
  field
    prd∞ : 1+ ℕ∞

open ℕ∞


ℕ∞-corec' :
  (C → 1+ C)
  → C → ℕ∞
prd∞ (ℕ∞-corec' f c) with f c
... | nothing = nothing
... | just x  = just (ℕ∞-corec' f x)

ℕ∞-corec :
  (C → 1+ (ℕ∞ + C))
  → C → ℕ∞
prd∞ (ℕ∞-corec f c) with f c
... | nothing      = nothing
... | just (inl n) = just n
... | just (inr x) = just (ℕ∞-corec f x)


∞ : ℕ∞
prd∞ ∞ = just ∞

-- eq : ℕ∞-corec' {C = Unit} (λ x → just x) star ≡ ∞
-- prd∞ (eq i) = just (eq i)

0∞ : ℕ∞
prd∞ 0∞ = nothing

-- eq₀ : ℕ∞-corec' {C = Unit} (λ _ → nothing) star ≡ 0∞
-- prd∞ (eq₀ i) = nothing

1∞ : ℕ∞
prd∞ 1∞ = just 0∞

-- eq₁ : ℕ∞-corec {C = Unit} (λ _ → just (inl 0∞)) star ≡ 1∞
-- prd∞ (eq₁ i) = just 0∞

suc∞ : ℕ∞ → ℕ∞
prd∞ (suc∞ x) = just x

-- eq₂ : ℕ∞-corec {C = ℕ∞} (λ n → just (inl n)) ≡ suc∞
-- prd∞ (eq₂ i x) = just x

ℕ→ℕ∞ : ℕ → ℕ∞
prd∞ (ℕ→ℕ∞ zero) = nothing
prd∞ (ℕ→ℕ∞ (suc n)) = just (ℕ→ℕ∞ n)

-- eq₃ : ℕ∞-corec' {C = ℕ} (λ {zero → nothing
--                           ; (suc n) → just n}) ≡ ℕ→ℕ∞
-- prd∞ (eq₃ i zero) = nothing
-- prd∞ (eq₃ i (suc x)) = just (eq₃ i x)


-- 解体したときの振る舞いが等しいなら、もとの項も等しい？

-- function extensionality が典型例
  
funext : {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
funext p i x = p x i

module Bisimulation where

  -- 振る舞いが等しいとはどういうことか
  -- bisimulation (extensional equality)

  isBisim : (ℕ∞ → ℕ∞ → Type) → Type
  isBisim R = ∀ {x y} → R x y →
    ((prd∞ x ≡ nothing) × (prd∞ y ≡ nothing))
    + (Σ x' ꞉ ℕ∞ , Σ y' ꞉ ℕ∞ , ((prd∞ x ≡ just x') × (prd∞ y ≡ just y') × R x' y'))

  coind-ℕ∞ : ∀ R → isBisim R → ∀ x y → R x y → x ≡ y
  prd∞ (coind-ℕ∞ R isbisR x y Rxy i)
    with isbisR Rxy
  ... | inl (p , q) = (p ∙ sym q) i
  ... | inr (p , q , r , s , t) with prd∞ x | prd∞ y
  ...                             | nothing | nothing = nothing
  ...                             | nothing | just y' = lemma i
    where
      lemma : nothing ≡ just y'
      lemma = absurd (nth≠just r)
  ...                             | just x' | nothing = lemma i
    where
      lemma : just x' ≡ nothing
      lemma = absurd (nth≠just s)
  ...                             | just x' | just y' = just (lemma₃ i)
    where
    just⁻¹ : 1+ ℕ∞ → ℕ∞
    just⁻¹ nothing = 0∞
    just⁻¹ (just x) = x
    
    lemma₁ : R p q ≡ R x' y'
    lemma₁ i = R (just⁻¹ (sym r i)) (just⁻¹ (sym s i))
    lemma₂ : R x' y'
    lemma₂ = transport lemma₁ t
    lemma₃ : x' ≡ y'
    lemma₃ = coind-ℕ∞ R isbisR x' y' lemma₂