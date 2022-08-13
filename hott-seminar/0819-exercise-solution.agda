{-# OPTIONS --without-K --safe #-}
module 0819-exercise-solution where
open import 0811-induction public

-- パターンマッチを使っても良いし、 induction を使っても良いかも

-- uniqueness
Bool-uniq : (x : Bool) → (x ≡ tt) + (x ≡ ff)
Bool-uniq = Bool-ind (inl refl) (inr refl)

ℕ-uniq : (n : ℕ) → (n ≡ 0) + (Σ x ꞉ ℕ , (n ≡ suc x))
ℕ-uniq = ℕ-ind (inl refl) (λ n _ → inr (n , refl))

≡-uniq : (a : A) → (pair : Σ x ꞉ A , (a ≡ x)) → pair ≡ (a , refl)
≡-uniq a = Σ-ind (≡-ind a refl)
-- p : a ≡ a に対して、
  -- Σ x ꞉ A , (a ≡ x) において (a , p) ≡ (a , refl) が成り立つ
  -- Σ x ꞉ A , (x ≡ x) において (a , p) ≡ (a , refl) が成り立つとは限らない

-- ap
ap : (f : A → B) → (x y : A) → x ≡ y → f x ≡ f y
ap f x = ≡-ind x refl

-- Peano

-- パターンマッチを使えば簡単
-- ≡-ind でやるのはちょっと難しいかも（ヒント：前者関数を定義しておく）
suc-inj : (m n : ℕ) → (suc m ≡ suc n) → (m ≡ n)
suc-inj m n = ap pred (suc m) (suc n)
  where
  pred : ℕ → ℕ
  pred = ℕ-ind 0 (λ n _ → n)

-- suc-inj m n = ≡-ind (suc m) {λ x p → m ≡ pred x} refl (suc n)


-- パターンマッチを使えば簡単
-- ≡-ind でやるのは難しいかも（ヒント：良い感じの関数 ℕ → Type を定義しておく）
suc-neq0 : (n : ℕ) → ¬ (suc n ≡ 0)
suc-neq0 n p = transport {B = F} _ _ p star
  where
  F : ℕ → Type
  F = ℕ-ind Empty (λ _ _ → Unit)
  transport : {B : A → Type} (x y : A) → x ≡ y → B x → B y
  transport x = ≡-ind x (λ b → b)

-- suc-neq0 n p = ≡-ind (suc n) {λ x p → (F (suc n) → F x)} (λ b → b) 0 p star