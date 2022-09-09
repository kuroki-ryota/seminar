{-# OPTIONS --without-K --rewriting #-}
module 0916-Trunc-properties where
open import 0916-Trunc public

-- ∞-image
Im? : {A B : Type ℓ} (f : A → B) → Type ℓ
Im? {A = A} {B} f = Σ b ꞉ B , Σ x ꞉ A , (f x ≡ b)

-- どこから来たかという情報を取り出せる
Im?→A : (f : A → B) → (Im? f → A)
Im?→A f (b , (a , p)) = a

Im?≃A : (f : A → B) → (Im? f ≃ A)
Im?≃A f = Equiv (Im?→A f)
  (Inverse (λ x → (f x) , (x , refl)) (λ {(b , (a , p)) → lemma p})
    (λ x → (f x) , (x , refl)) (λ x → refl))
  where
    lemma : ∀ {a b} → (p : f a ≡ b) → (f a , (a , refl)) ≡ (b , (a , p)) [ (Σ b ꞉ _ , Σ x ꞉ _ , (f x ≡ b)) ]
    lemma refl = refl

-- (-1)-image
Im : {A B : Type ℓ} (f : A → B) → Type ℓ
Im {A = A} {B} f = Σ b ꞉ B , ∥ Σ x ꞉ A , (f x ≡ b) ∥

