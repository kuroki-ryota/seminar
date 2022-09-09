{-# OPTIONS --without-K --rewriting #-}
module 0916-S1-properties where
open import 0909-univalence-examples public
open import 0916-S1 public

DoubleCover : S1 → Type
DoubleCover = S1-rec Bool flippath

¬loop≡refl : ¬ (loop ≡ refl)
¬loop≡refl loop≡refl = ¬flippath≡refl lemma
  where
  lemma : flippath ≡ refl
  lemma =
    flippath                         ≡⟨ ! (S1-rec-loop Bool flippath) ⟩
    ap DoubleCover loop              ≡⟨ ap (λ p → ap DoubleCover p) loop≡refl ⟩
    ap DoubleCover (refl {a = base}) ≡⟨ refl ⟩
    refl ∎