{-# OPTIONS --cubical --safe #-}
module Hlevel where
open import Prelude public

-- h-level の定義 (1)
islv : ℕ → Type ℓ → Type ℓ
islv 0 A = isContr A
islv (suc n) A = (x y : A) → islv n (x ≡ y)

-- isContr A = Σ a : A , ((x : A) → a ≡ x)
-- isConnected A = Σ a : A , (x : A) → || a ≡ x ||
-- isProp A = (x y : A) → x ≡ y
-- islv 1 A = (x y : A) → isContr (x ≡ y)


sqfill : (a : A)
        → ((i j : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j) (Σ x ꞉ A , (a ≡ x)))
        → (i j : I) → A
sqfill a s i j = hcomp (λ k → λ isone → pr₂ (s i j isone) k ) a

islv0→islv1 : islv 0 A → islv 1 A
islv0→islv1 (a , f) x y = ((f x ⁻¹) ∙ (f y))
  , λ p → lemma₁ _ p
  where
  lemma₁ : (p q : x ≡ y) → p ≡ q
  lemma₁ p q j i =
    hcomp (λ k → λ { (i = i0) → f x k
                   ; (i = i1) → f y k
                   ; (j = i0) → f (p i) k
                   ; (j = i1) → f (q i) k}) a

-- (λ i →
--   hcomp (λ j → λ { (i = i0) → f x (j)
--                  ; (i = i1) → f y j}) a)
--   , {!   !}
-- islv0→islv1 : islv 0 A → islv 1 A
-- islv0→islv1 (a , f) x y = (f x ⁻¹) ∙ f y , λ q → lemma₁ _ q
--   where
--   lemma₁ : (p q : x ≡ y) → p ≡ q
--   lemma₁ p q i j =
--     sqfill a (λ i j →
--       λ { (j = i0) → x   , f x
--         ; (j = i1) → y   , f y
--         ; (i = i0) → p j , f (p j)
--         ; (i = i1) → q j , f (q j)}) i j

islvSuc : (n : ℕ) → islv n A → islv (suc n) A
islvSuc 0 islv0A = islv0→islv1 islv0A
islvSuc (suc n) h x y = islvSuc n (h x y)
  -- islvSuc n (h a b)

-- h-level の定義 (2)

isOfHLevel : ℕ → Type ℓ → Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = (x y : A) → isOfHLevel (suc n) (x ≡ y)

-- 命題としての同値性

islv1→isProp : islv 1 A → isProp A
islv1→isProp f x y = fst (f x y)

isProp→islv1 : isProp A → islv 1 A
isProp→islv1 isPropA x y = islv0→islv1 (x , (isPropA x)) x y

islv→isOfHLevel : (n : ℕ) → islv n A → isOfHLevel n A
islv→isOfHLevel 0 f = f
islv→isOfHLevel 1 = islv1→isProp
islv→isOfHLevel (suc (suc n)) f x y = islv→isOfHLevel (suc n) (f x y)

isOfHLevel→islv : (n : ℕ) → isOfHLevel n A → islv n A
isOfHLevel→islv 0 f = f
isOfHLevel→islv 1 = isProp→islv1
isOfHLevel→islv (suc (suc n)) f x y = isOfHLevel→islv (suc n) (f x y)

_ : isContr A ≡ isOfHLevel 0 A
_ = refl
_ : isProp A ≡ isOfHLevel 1 A
_ = refl
_ : isSet A ≡ isOfHLevel 2 A
_ = refl

isOfHLevelSuc : (n : ℕ) → isOfHLevel n A → isOfHLevel (suc n) A
isOfHLevelSuc n ALeveln =
  islv→isOfHLevel (suc n) ( islvSuc n (isOfHLevel→islv n ALeveln))

isProp⊥ : isProp ⊥
isProp⊥ () y

module Hedberg where

  -- dec , stable , has-const-endo

  -- dec A = A + ¬ A

  stable : Type ℓ → Type ℓ
  stable X = ¬ (¬ X) → X

  isconst : (f : A → B) → Type _
  isconst f = (x y : _) → (f x ≡ f y)

  has-const-endo : Type ℓ → Type ℓ
  has-const-endo X = Σ f ꞉ (X → X) , isconst f
  
  -- dec → stable

  dec→stable : dec A → stable A
  dec→stable (inl x) = λ _ → x
  dec→stable (inr x) = λ f → absurd (f x)

  -- stable → has-const-endo

  funext : {B : A → Type ℓ} (f g : (x : A) → B x)
    → ((x : A) → f x ≡ g x)
    → f ≡ g
  funext f g eq i x = eq x i


  -- f ≡ g は I → ((x : A) → B x) 
  -- funext f g eq i x = eq x i
  
  dfunisprop : {B : A → Type ℓ}
    → ((x : A) → isProp (B x))
    → isProp ((x : A) → B x)
  dfunisprop isPropB f g i x = isPropB x (f x) (g x) i

  funisprop : (isProp B) → isProp (A → B)
  funisprop isPropB f g = funext f g (λ x → isPropB (f x) (g x))
  -- funisprop isPropB f g i x = isPropB (f x) (g x) i

  -- A → A
  -- A → ¬ (¬ A)  , st : ¬ (¬ A) → A を合成

  stable→has-const-endo : stable A → has-const-endo A
  stable→has-const-endo st = (λ x → st (λ f → f x)) , λ x y i → st (funisprop isProp⊥ (λ f → f x) (λ f → f y) i)
    -- (λ x → st (λ f → f x)) ,
    -- λ x y i → st (funisprop isProp⊥ (λ f → f x) (λ f → f y) i)

  -- Hedberg

  localHedberg : (a : A) → ({x : A} → has-const-endo (a ≡ x))
    → (x : A) → isProp (a ≡ x)
  localHedberg a pc b p q j i =
    hcomp (λ k → λ { (i = i0) → f refl k
                   ; (i = i1) → fisconst p q j k
                   ; (j = i0) → f (λ i' → p (i' ∧ i)) k
                   ; (j = i1) → f (λ i' → q (i' ∧ i)) k}) a  where
    f : {x : _} → (a ≡ x) → (a ≡ x)
    f = pr₁ pc
    fisconst : {x : _} (p q : a ≡ x) → f p ≡ f q
    fisconst = pr₂ pc

  

    -- sqfill a (λ i j →
    --   λ { (j = i0) → a   , pc₁ refl
    --     ; (j = i1) → x   , pc₂ p q i
    --     ; (i = i0) → p j , pc₁ (λ k → p (j ∧ k))
    --     ; (i = i1) → q j , pc₁ (λ k → q (j ∧ k))}) i j
    -- where
    -- pc₁ : {y : _} → a ≡ y → a ≡ y
    -- pc₁ = fst pc
    -- pc₂ : {y : _} (p q : a ≡ y) → pc₁ p ≡ pc₁ q
    -- pc₂ = snd pc

  Hedberg' : ((x y : A) → has-const-endo (x ≡ y))
    → (x y : A) → isProp (x ≡ y)
  Hedberg' f x y = localHedberg x (f x _) y

  Hedberg : ((x y : A) → dec (x ≡ y))
    → (x y : A) → isProp (x ≡ y)
  Hedberg f x y = localHedberg x (stable→has-const-endo (dec→stable (f x _))) y
