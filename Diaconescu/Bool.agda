{-# OPTIONS --cubical --safe #-}
module Bool where
open import Hlevel public
open import Univalence public

data Bool : Type where
  tt ff : Bool

Bool→Type : Bool → Type
Bool→Type tt = Unit
Bool→Type ff = ⊥

tt≠ff : ¬ (tt ≡ ff)
tt≠ff p = transport (λ i → Bool→Type (p i)) star

ff≠tt : ¬ (ff ≡ tt)
ff≠tt p = transport (λ i → Bool→Type (p (~ i))) star

decBoolEq : (x y : Bool) → dec (x ≡ y)
decBoolEq tt tt = inl refl
decBoolEq tt ff = inr tt≠ff
decBoolEq ff tt = inr ff≠tt
decBoolEq ff ff = inl refl

not : Bool → Bool
not tt = ff
not ff = tt

notinvol : (x : Bool) → not (not x) ≡ x
notinvol tt = refl
notinvol ff = refl

notIsEquiv : isEquiv not
notIsEquiv = isoToIsEquiv (iso not not notinvol notinvol)

notpath : Bool ≡ Bool
notpath = ua (not , notIsEquiv)

open Hedberg

issetBool : isSet Bool
issetBool x y = Hedberg decBoolEq x y