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

-- f : (X : Type) → (Bool ≡ X) → C
-- f Bool refl = c
-- こんな感じで path induction で関数 f を定義したとき、
-- f Bool flippath はこれ以上簡約できない。

-- ZFC だと {1} と {2} は等しいとは言えない。

-- material な集合論と structural な集合論

-- tt : S

-- ff : S'

-- F : Type → Type であって ¬ (F S ≡ F S') となるものは作れない
-- S ≡ S' は MLTT だと言えないが、
-- (Bool ≃ Bool) ≃ Bool が言える

-- G , H : Grp で G ≃ H のとき、
-- P : Grp → Type に対して、 P G ならば P H か？
-- univalence があれば、言える (structure identity principle (SIP))


¬flippath≡refl : ¬ (flippath ≡ refl)
¬flippath≡refl flippath≡refl = ¬tt≡ff lemma
  where
  lemma : tt ≡ ff
  lemma =
    tt                       ≡⟨ ! (uaβ flip flip-eqv ff) ⟩
    transport id flippath ff ≡⟨ ap (λ p → transport id p ff ) flippath≡refl ⟩
    transport id refl ff     ≡⟨ refl ⟩
    ff ∎

-- HoTT = MLTT + univalence + HIT
-- Cubical Type Theory (CTT) は MLTT の規則を改造したもの。
  -- univalence が公理なしで示せる。
  -- HIT を作る規則がある。
  -- 規則がちょっと複雑。
-- Higher Observational Type Theory (HOTT)
  -- cubical よりも自然？
  -- 未完成