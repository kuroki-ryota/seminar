{-# OPTIONS --cubical --safe #-}
module Hlevel where
open import Bool public

islv : ℕ → Type ℓ → Type ℓ
islv 0 A = isContr A
islv (suc n) A = (x y : A) → islv n (x ≡ y)

islv0 islv1 islv2 : Type ℓ → Type ℓ
islv0 = islv 0
islv1 = islv 1
islv2 = islv 2

islv0Unit : islv0 Unit
islv0Unit = star , (λ {star → refl})

islv1⊥ : islv1 ⊥
islv1⊥ = λ x ()

sqfill : (a : A)
        → ((i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) (Σ x ꞉ A , (a ≡ x)))
        → (i j : I) → A
sqfill a s i j = hcomp (λ k → λ isone → pr₂ (s i j isone) k ) a

islv0→islv1 : islv0 A → islv1 A
islv0→islv1 (a , f) x y = (f x ⁻¹) ∙ f y , λ q → lemma₁ _ q
  where
  lemma₁ : (p q : x ≡ y) → p ≡ q
  lemma₁ p q i j =
    sqfill a (λ i j →
      λ { (j = i0) → x   , f x
        ; (j = i1) → y   , f y
        ; (i = i0) → p j , f (p j)
        ; (i = i1) → q j , f (q j)}) i j

islvSuc : (n : ℕ) → islv n A → islv (suc n) A
islvSuc 0 islv0A = islv0→islv1 islv0A
islvSuc (suc n) h a b = islvSuc n (h a b)

isOfHLevel : ℕ → Type ℓ → Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = (x y : A) → isOfHLevel (suc n) (x ≡ y)

islv→isOfHLevel : (n : ℕ) → islv n A → isOfHLevel n A
islv→isOfHLevel zero f = f
islv→isOfHLevel (suc zero) f x y = fst (f x y)
islv→isOfHLevel (suc (suc n)) f x y = islv→isOfHLevel (suc n) (f x y)

isOfHLevel→islv : (n : ℕ) → isOfHLevel n A → islv n A
isOfHLevel→islv zero f = f
isOfHLevel→islv (suc zero) isPropA x y = islv0→islv1 (x , (isPropA x)) x y
isOfHLevel→islv (suc (suc n)) f x y = isOfHLevel→islv (suc n) (f x y)

_ : isContr A ≡ isOfHLevel 0 A
_ = refl
_ : isProp A ≡ isOfHLevel 1 A
_ = refl
_ : isSet A ≡ isOfHLevel 2 A
_ = refl

islv1→isProp : islv1 A → isProp A
islv1→isProp islv1A x y = pr₁ (islv1A x y)

isProp→islv1 : isProp A → islv1 A
isProp→islv1 {A = A} isPropA x = lemma₂ x
  where
  lemma₁ : islv0 A
  lemma₁ = x , isPropA x
  lemma₂ : islv1 A
  lemma₂ = islvSuc _ lemma₁

isProp⊥ : isProp ⊥
isProp⊥ ()

module Hedberg where

  stable : Type ℓ → Type ℓ
  stable X = ¬ (¬ X) → X

  isconst : (f : A → B) → Type _
  isconst f = (x y : _) → (f x ≡ f y)

  has-const-endo : Type ℓ → Type ℓ
  has-const-endo X = Σ f ꞉ (X → X) , isconst f
  
  dec→stable : dec A → stable A
  dec→stable (inl x) = λ _ → x
  dec→stable (inr x) = λ f → absurd (f x)

  dfunisprop : {B : A → Type ℓ}
    → ((x : A) → isProp (B x))
    → isProp ((x : A) → B x)
  dfunisprop isPropB f g i x = isPropB x (f x) (g x) i

  funisprop : (isProp B) → isProp (A → B)
  funisprop isPropB f g i x = isPropB (f x) (g x) i

  stable→has-const-endo : stable A → has-const-endo A
  stable→has-const-endo st =
    (λ x → st (λ f → f x)) ,
    λ x y i → st (funisprop isProp⊥ (λ f → f x) (λ f → f y) i)

  localHedberg : (a : A) → ({x : A} → has-const-endo (a ≡ x))
    → (x : A) → isProp (a ≡ x)
  localHedberg a pc x p q i j =
    sqfill a (λ i j →
      λ { (j = i0) → a   , pc₁ refl
        ; (j = i1) → x   , pc₂ p q i
        ; (i = i0) → p j , pc₁ (λ k → p (j ∧ k))
        ; (i = i1) → q j , pc₁ (λ k → q (j ∧ k))}) i j
    where
    pc₁ : {y : _} → a ≡ y → a ≡ y
    pc₁ = fst pc
    pc₂ : {y : _} (p q : a ≡ y) → pc₁ p ≡ pc₁ q
    pc₂ = snd pc

  Hedberg' : ((x y : A) → has-const-endo (x ≡ y))
    → (x y : A) → isProp (x ≡ y)
  Hedberg' f x y = localHedberg x (f x _) y

  Hedberg : ((x y : A) → dec (x ≡ y))
    → (x y : A) → isProp (x ≡ y)
  Hedberg f x y = localHedberg x (stable→has-const-endo (dec→stable (f x _))) y

open Hedberg public

issetBool : islv2 Bool
issetBool x y = isProp→islv1 (Hedberg decBoolEq x y)