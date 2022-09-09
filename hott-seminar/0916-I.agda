{-# OPTIONS --without-K --rewriting #-}
module 0916-I where
open import 0909-prelude public

postulate
  I : Type

  i0 i1 : I
  seg : i0 ≡ i1

  I-rec : (x y : C) (p : x ≡ y) → I → C
  
  I-rec-i0 : (x y : C) (p : x ≡ y)
    → I-rec x y p i0 ≡ x
  I-rec-i1 : (x y : C) (p : x ≡ y)
    → I-rec x y p i1 ≡ y

  {-# REWRITE I-rec-i0 I-rec-i1 #-}

  I-rec-seg : (x y : C) (p : x ≡ y)
    → ap (I-rec x y p) seg ≡ p

  
  I-ind : {C : I → Type ℓ}
    (x : C i0) (y : C i1)
    (p : transport C seg x ≡ y)
    → (i : I) → C i
  
  I-ind-i0 : {C : I → Type ℓ}
    (x : C i0) (y : C i1)
    (p : transport C seg x ≡ y)
    → I-ind x y p i0 ≡ x

  I-ind-i1 : {C : I → Type ℓ}
    (x : C i0) (y : C i1)
    (p : transport C seg x ≡ y)
    → I-ind x y p i1 ≡ y

  {-# REWRITE I-ind-i0 I-ind-i1 #-}

  I-ind-seg : {C : I → Type ℓ}
    (x : C i0) (y : C i1)
    (p : transport C seg x ≡ y)
    → apd (I-ind x y p) seg ≡ p 