{-# OPTIONS --cubical --guardedness --safe #-}
module Natural where
open import Basic public

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-rec' : 
  C
  → (C → C)
  → ℕ → C
ℕ-rec' c f zero = c
ℕ-rec' c f (suc n) = f (ℕ-rec' c f n)

ℕ-rec :
  C
  → (ℕ → C → C)
  → ℕ → C
ℕ-rec c f zero = c
ℕ-rec c f (suc n) = f n (ℕ-rec c f n)



-- 1+ の initial algebra としての ℕ

data Nat : Type where
  succ : 1+ Nat → Nat

-- catamorphism
Nat-rec' :
  ((1+ C) → C)
  → Nat → C
Nat-rec' f (succ nothing)  = f nothing
Nat-rec' f (succ (just n)) = f (just (Nat-rec' f n))

-- paramorphism
Nat-rec :
  ((1+ (Nat × C)) → C)
  → Nat → C
Nat-rec f (succ nothing)  = f nothing
Nat-rec f (succ (just n)) = f (just (n , Nat-rec f n))