{-# OPTIONS --without-K --rewriting #-}
module 0916-I-properties where
open import 0916-I public

fun→path : (f : I → A) → f i0 ≡ f i1
fun→path f = ap f seg

funextI : (f g : A → B) → f ∼ g → f ≡ g
funextI {A = A} {B = B} f g H = fun→path h where
  h : I → A → B
  h i x = I-rec (f x) (g x) (H x) i

isContrI : isContr I
isContrI = i0 , I-ind refl seg (lemma i1 seg)
  where
  lemma : (x : I) (p : i0 ≡ x)
    → transport (λ z → i0 ≡ z) p refl ≡ p
  lemma .i0 refl = refl

I≃Unit : I ≃ Unit
I≃Unit = isContr→≃Unit isContrI