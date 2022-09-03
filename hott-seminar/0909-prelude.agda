{-# OPTIONS --without-K --rewriting #-}
module 0909-prelude where
open import 0811-inductive-types hiding (_×_) public

-- × を coinductive にする
_×_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
A × B = Σ A (λ _ → B)

infixr 2 _×_

{-# BUILTIN REWRITE _≡_ #-}

-- どの型における identity type かを明示
Path : (A : Type ℓ) → A → A → Type ℓ
Path A x y = x ≡ y

syntax Path A x y = x ≡ y [ A ] 

id : A → A
id x = x

-- 関数の合成
_∘_ : {C : B → Type ℓ}
    → ((y : B) → C y)
    → (f : A → B)
    → (x : A) → C (f x)
g ∘ f = λ x → g (f x)

_∙_ : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ p = p

infixl 7 _∙_

! : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
! refl = refl

module GroupoidLaws where
  private variable
    x y z w : A
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


ap : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

transport : (B : A → Type ℓ)
          → {x y : A} → x ≡ y → B x → B y
transport B refl a = a

-- transportconst : {x y : A} (p : x ≡ y) (b : B)
--   → transport (λ _ → B) p b ≡ b
-- transportconst refl b = refl

_∼_ : {B : A → Type ℓ} → ((x : A) → B x) → ((x : A) → B x) → Type _
f ∼ g = ∀ x → f x ≡ g x

infix 0 _∼_

_≡⟨_⟩_ : (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : (x : A) → x ≡ x
x ∎ = refl

infixr  0 _≡⟨_⟩_
infix   1 _∎

pair≡ : {x x' : A} {y y' : B}
      → x ≡ x'
      → y ≡ y'
      → (x , y) ≡ (x' , y') [ A × B ]
pair≡ refl refl = refl

postulate
  dfunext : {B : A → Type ℓ} {f g : (x : A) → B x} → f ∼ g → f ≡ g

record is-equiv {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) : Type (ℓ₁ ⊔ ℓ₂) where
 constructor
  Inverse
 field
  linv : B → A
  linveq : linv ∘ f ∼ id
  rinv : B → A
  rinveq : f ∘ rinv ∼ id
open is-equiv public

record _≃_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
 constructor
  Equiv
 field
  map : A → B
  is-equivalence : is-equiv map

open _≃_ public

-- univalence

idiseqv : is-equiv (id {A = A})
idiseqv = Inverse id (λ _ → refl) id (λ _ → refl)

idtoeqv : (A ≡ B) → (A ≃ B)
idtoeqv p = Equiv (transport id p) (lemma p) where
  lemma : (p : A ≡ B) → is-equiv (transport id p)
  lemma refl = idiseqv
-- idtoeqv refl = Equiv id idiseqv


postulate
  univ : is-equiv (idtoeqv {A = A} {B})

module _ {A B : Type ℓ} where

  ua ua' : (A ≃ B) → (A ≡ B)
  ua  = univ .linv
  ua' = univ .rinv

  univ-comp' : (f : A ≃ B) → idtoeqv (ua' f) ≡ f
  univ-comp' f = rinveq univ f
  
  univ-uniq : (p : A ≡ B) → ua (idtoeqv p) ≡ p
  univ-uniq p = linveq univ p

  ua∼ua' : ua ∼ ua'
  ua∼ua' f =
    ua f                 ≡⟨ ! (ap ua (univ-comp' f)) ⟩
    ua (idtoeqv (ua' f)) ≡⟨ univ-uniq (ua' f) ⟩
    ua' f                ∎
  
  univ-comp : (f : A ≃ B) → idtoeqv (ua f) ≡ f
  univ-comp f =
    idtoeqv (ua f)  ≡⟨ ap idtoeqv (ua∼ua' f) ⟩
    idtoeqv (ua' f) ≡⟨ univ-comp' f ⟩
    f ∎
  
  uaβ : (f : A → B) (eqv : is-equiv f) (x : A)
    → (idtoeqv (ua (Equiv f eqv))).map x ≡ f x
  uaβ f eqv x = ap (λ f → f .map x) lemma
    where
    lemma : idtoeqv (ua (Equiv f eqv)) ≡ Equiv f eqv
    lemma = (univ-comp (Equiv f eqv))