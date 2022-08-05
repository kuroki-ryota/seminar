{-# OPTIONS --without-K --safe #-}
module 0811-induction where
open import 0811-inductive-types public

-- induction (inductive type の elim. rule)の内容
  -- inductive type の項から他の型の項を作る方法
  -- 関数型の言葉を使うと、 inductive type から他の型への関数を作る方法

  -- constructor で作れる項の行き先さえ定めれば、関数が全域で定まる
    -- 個人的にはここが "帰納法" っぽいポイント

-- induction (elim. rule) の形は constructor (intro. rule) から自動的に決まる
-- W-type などを参照

-- MLTT, HoTTは induction が基本
-- Agdaはパターンマッチが基本
-- Agdaのパターンマッチは強力
  -- パターンマッチで短く書けても induction では短く書けない場合もある
-- パターンマッチを使って induction に相当する主張を示す

×-rec :
  (A → B → C)
  → (A × B → C)
×-rec f (x , y) = f x y

×-ind : {C : A × B → Type ℓ}
  → ((x : A) → (y : B) → C (x , y))
  → ((p : A × B) → C p)
×-ind f (x , y) = f x y

Unit-rec :
  C
  → (Unit → C)
Unit-rec c star = c

Unit-ind : {C : Unit → Type ℓ}
  → C star
  → ((x : Unit) → C x)
Unit-ind c star = c

Σ-rec : {B : A → Type ℓ}
  → ((x : A) → B x → C)
  → (Σ x ꞉ A , B x) → C
Σ-rec f (x , y) = f x y

Σ-ind : {B : A → Type ℓ} {C : (Σ x ꞉ A , B x) → Type ℓ}
  → ((x : A) → (y : B x) → C (x , y))
  → (p : Σ x ꞉ A , B x) → C p
Σ-ind f (x , y) = f x y

+-rec :
  (A → C)
  → (B → C)
  → (A + B → C)
+-rec f g (inl x) = f x
+-rec f g (inr y) = g y

+-ind : {C : A + B → Type ℓ}
  → ((x : A) → C (inl x))
  → ((y : B) → C (inr y))
  → ((z : A + B) → C z)
+-ind f g (inl x) = f x
+-ind f g (inr y) = g y

Empty-rec : 
  (Empty → C)
Empty-rec ()

Empty-ind : {C : Empty → Type ℓ}
  → ((x : Empty) → C x)
Empty-ind ()

Bool-rec :
  C
  → C
  → (Bool → C)
Bool-rec a b tt = a
Bool-rec a b ff = b

Bool-ind : {C : Bool → Type ℓ}
  → C tt
  → C ff
  → ((x : Bool) → C x)
Bool-ind a b tt = a
Bool-ind a b ff = b

ℕ-rec :
  C
  → (C → C)
  → (ℕ → C)
ℕ-rec c f zero = c
ℕ-rec c f (suc n) = f (ℕ-rec c f n)

ℕ-ind : {C : ℕ → Type ℓ}
  → C 0
  → ((n : ℕ) → C n → C (suc n))
  → ((n : ℕ) → C n)
ℕ-ind c f zero = c
ℕ-ind c f (suc n) = f n (ℕ-ind c f n)

≡-rec : (a : A)
  → C
  → ((x : A) → (a ≡ x) → C)
≡-rec a c .a refl = c
-- Unit-recとほぼ同じ
-- (x : A) → (a ≡ x) → C は (Σ x ꞉ A , (a ≡ x)) → C と思える

≡-ind : (a : A) {C : (x : A) → (a ≡ x) → Type ℓ}
  → C a refl
  → ((x : A) → (p : a ≡ x) → C x p)
≡-ind a c .a refl = c
-- Unit-ind とほぼ同じ
-- Σ x ꞉ A , (a ≡ x) は Unit と同じ普遍性を持つ
  -- Σ x ꞉ A , (a ≡ x) は型として Unit と同値になる

-- ≡-ind は一般の (x : A) , (p : a ≡ x) に対して C x p が定まっているときに使える
-- 特定の (b : A) に対して D : (p : a ≡ b) → Type ℓ が定まっているときに、
  -- 関数 f : (p : a ≡ b) → D p を作りたいときは、
  -- いったんゴールDを C : (x : A) (p : a ≡ x) → Type ℓ に一般化してから induction を使う
    -- g : (x : A) → (p : a ≡ x) → C x p が得られるので f p = g b p と定める
-- パターンマッチを使うときは多少ルーズでもok （okかどうかは慣れればある程度分かる）

Leibniz : (a : A) {C : A → Type ℓ}
  → C a
  → ((x : A) → a ≡ x → C x)
Leibniz a c .a refl = c

Leibniz' : (a b : A) {C : A → Type ℓ}
  → C a
  → (a ≡ b → C b)
Leibniz' a .a c refl = c
-- Leibniz' a b {C} c p = ≡-ind a {λ x _ → C x} c b p 

-- K : (a : A) {D : a ≡ a → Type ℓ}
--   → D refl
--   → (p : a ≡ a) → D p
-- K a c refl = c
-- -without-K を抜くと、パターンマッチが強くなってこれが示せる
  -- これによって強正規化や canonicity が崩れるわけではない
  -- K はちゃんと computational content を持っている
-- ただ、 univalence と矛盾するので HoTT をやるときは -without-K を入れる

open unbased-id

≡'-rec :
  (A → C)
  → ((x y : A) → (x ≡' y) → C)
≡'-rec f x .(x) refl = f x

≡'-ind : {C : (x y : A) → x ≡' y → Type ℓ}
  → ((x : A) → C x x refl)
  → ((x y : A) → (p : x ≡' y) → C x y p)
≡'-ind f x .(x) refl = f x