{-# OPTIONS --cubical --safe #-}
module Univalence where
open import Prelude public

-- univalence を示す準備

-- id は equivalence
  -- fiber が contractible であることを示せばよい

pathspContr : (a : A) → isContr (Σ x ꞉ A , (x ≡ a))
pathspContr a = (a , refl) , λ {(x , p) i → p (~ i) , λ j → p (~ i ∨ j)}
-- id による a の fiber Σ x ꞉ A , (x ≡ a) の点として (a , refl) が取れて、
-- fiber に属する任意の点 (x , p) は (a , refl) と等しい

idIsEquiv : isEquiv (id {A = A})
idIsEquiv .equiv-proof a = pathspContr a

-- library で定義されている isoToIsEquiv を使っても示せる
  -- 逆写像を作れば iso が示せて equiv も示せる
_ : isEquiv (id {A = A})
_ = isoToIsEquiv (iso id id (λ x → refl) (λ x → refl))

-- univalence の証明
ua : A ≃ B → A ≡ B
ua {A = A} {B} eqv i = Glue B λ { (i = i0) → A , eqv
                                ; (i = i1) → B , id , idIsEquiv}