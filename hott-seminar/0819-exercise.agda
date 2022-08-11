{-# OPTIONS --without-K --allow-unsolved-metas #-}
module 0819-exercise where
open import 0811-induction public

-- 1行目の --allow-unsolved-metas を消して実行した方が良いかも

-- パターンマッチを使っても良いし、 induction を使っても良いかも

-- uniqueness
Bool-uniq : (x : Bool) → (x ≡ tt) + (x ≡ ff)
Bool-uniq x = {!   !}
ℕ-uniq : (n : ℕ) → (n ≡ 0) + (Σ x ꞉ ℕ , (n ≡ suc x))
ℕ-uniq n = {!   !}
≡-uniq : (a : A) → (pair : Σ x ꞉ A , (a ≡ x)) → pair ≡ (a , refl)
≡-uniq a pair = {!   !}
-- p : a ≡ a に対して、
  -- Σ x ꞉ A , (a ≡ x) において (a , p) ≡ (a , refl) が成り立つ
  -- Σ x ꞉ A , (x ≡ x) において (a , p) ≡ (a , refl) が成り立つとは限らない

-- ap
ap : (f : A → B) → (x y : A) → x ≡ y → f x ≡ f y
ap f x y p = {!   !}

-- Peano

-- パターンマッチを使えば簡単
-- ≡-ind でやるのはちょっと難しいかも（ヒント：前者関数を定義しておく）
suc-inj : (m n : ℕ) → (suc m ≡ suc n) → (m ≡ n)
suc-inj m n p = {!   !}

-- パターンマッチを使えば簡単
-- ≡-ind でやるのは難しいかも（ヒント：良い感じの関数 ℕ → Type を定義しておく）
suc-neq0 : (n : ℕ) → ¬ (suc n ≡ 0)
suc-neq0 n p = {!   !}
 