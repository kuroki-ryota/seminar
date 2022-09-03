{-# OPTIONS --without-K --rewriting #-}
module 0909-univalence-examples where
open import 0909-prelude public

¬tt≡ff : ¬ (tt ≡ ff)
¬tt≡ff ()

flip : Bool → Bool
flip tt = ff
flip ff = tt

flip-invol : flip ∘ flip ∼ id
flip-invol tt = refl
flip-invol ff = refl

flip-eqv : is-equiv flip
flip-eqv = Inverse flip flip-invol flip flip-invol

flippath : Bool ≡ Bool
flippath = ua (Equiv flip flip-eqv)

¬flippath≡refl : ¬ (flippath ≡ refl)
¬flippath≡refl flippath≡refl = ¬tt≡ff lemma
  where
  lemma : tt ≡ ff
  lemma =
    tt                        ≡⟨ ! (uaβ flip flip-eqv ff) ⟩
    (idtoeqv flippath).map ff ≡⟨ ap (λ p → (idtoeqv p).map ff) flippath≡refl ⟩
    (idtoeqv refl).map ff     ≡⟨ refl ⟩
    ff ∎