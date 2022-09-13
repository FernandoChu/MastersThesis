{-# OPTIONS --without-K --exact-split #-}

open import Agda.Primitive public

variable
  𝒾 𝒿 : Level

data Id (X : Set 𝒾) : X → X → Set 𝒾 where
  refl : (x : X) → Id X x x
infix   0 Id

_≡_ : {X : Set 𝒾} → X → X → Set 𝒾
x ≡ y = Id _ x y
infix   0 _≡_
{-# BUILTIN EQUALITY _≡_ #-}

_∙_ : {X : Set 𝒾} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
(refl x) ∙ (refl x) = (refl x)
infixl 30 _∙_

ap : {X : Set 𝒾} {Y : Set 𝒿} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f {x} {x'} (refl x) = refl (f x)

module Interval where
  private
    data I' : Set₀ where
      Zero : I'

  I : Set₀
  I = I'

  zeroI : I
  zeroI = Zero

  oneI : I
  oneI = Zero

  I-rec : {C : Set 𝒾}
        → (a b : C)
        → (p : a ≡ b)
        → I → C
  I-rec a b _ Zero = a

  postulate
    segI : zeroI ≡ oneI
    -- βseg : {C : Set 𝒾}
    --      → (a b : C)
    --      → (p : a ≡ b)
    --      → ap (I-rec a b p) segI ≡ p

open Interval

postulate 𝕊¹ : Set₀
postulate base : 𝕊¹
postulate loop : base ≡ base

1loop : I → 𝕊¹
1loop = I-rec base base loop

2loops : I → 𝕊¹
2loops = I-rec base base (loop ∙ loop)

1≡2 : 1loop ≡ 2loops
1≡2 = refl _
