---
title: Capítulo 2. Teoría de Tipos Dependientes
---

# Capítulo 2. Teoría de Tipos Dependientes

<!--
```agda
module Capitulo2 where

open import Agda.Primitive public
  renaming (
            Set to Universe
          ; lsuc to infix 1 _⁺)

variable
  𝒾 𝒿 𝓀 : Level

𝒰 : (ℓ : Level) → Universe (ℓ ⁺)
𝒰 ℓ = Universe ℓ

𝒰₀ = Universe lzero
```
-->


## Sección 2.5. El tipo de funciones

```agda
-- Definición 2.5.5.
idA : {A : 𝒰 𝒾} → A → A
idA x = x

-- Definición 2.5.8.
cnst : (A : 𝒰 𝒾) (B : 𝒰 𝒿) (x : A) (y : B) → A
cnst A B x y = x

-- Definición 2.5.8.
comp : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
    → (B → C)
    → (A → B)
    → (A → C)
comp g f x = g (f x)
```

## Sección 2.6. El tipo de funciones dependientes

```agda
-- Definición 2.6.9.
id : {A : 𝒰 𝒾} → A → A
id x = x

𝑖𝑑 : (A : 𝒰 𝒾) → A → A
𝑖𝑑 A x = x

-- Ejemplo 2.6.11.
swap : (A : 𝒰 𝒾) (B : 𝒰 𝒿) (C : 𝒰 𝓀) → ((A → B → C) → (B → A → C))
swap A B C g b a = g a b


-- Definición 2.6.12.
_∘_ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {Z : Y → 𝒰 𝓀}
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)
infixl 70 _∘_

-- Helpers
domain : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 𝒾
domain {𝒾} {𝒿} {X} {Y} f = X

codomain : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 𝒿
codomain {𝒾} {𝒿} {X} {Y} f = Y
```

## Sección 2.7. El tipo de pares dependientes

```agda
-- Definición del tipo de pares dependientes
record Σ {X : 𝒰 𝒾} (Y : X → 𝒰 𝒿) : 𝒰 (𝒾 ⊔ 𝒿) where
  constructor
    _,_
  field
    x : X
    y : Y x
infixr 50 _,_

-Σ : (X : 𝒰 𝒾) (Y : X → 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
-Σ X Y = Σ Y
infixr -1 -Σ

syntax -Σ X (λ x → y) = Σ x ꞉ X , y

_×_ : (X : 𝒰 𝒾) (Y : 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
X × Y = Σ x ꞉ X , Y
infixr 30 _×_

-- Teorema 2.7.5.
Σ-induction : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} {A : Σ Y → 𝒰 𝓀}
            → ((x : X) (y : Y x) → A (x , y))
            → ((x , y) : Σ Y) → A (x , y)
Σ-induction g (x , y) = g x y

-- Teorema 2.7.6.
pr₁ : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y
```

## Sección 2.8. 0, 1, 2 y el tipo del coproducto

```agda
-- Definición del tipo de pares dependientes
data 𝟘 : 𝒰₀ where

-- Teorema 2.8.2.
𝟘-induction : (A : 𝟘 → 𝒰 𝒾) → (x : 𝟘) → A x
𝟘-induction A ()

-- Helper
!𝟘 : (A : 𝒰 𝒾) → 𝟘 → A
!𝟘 A = 𝟘-induction (λ _ → A)

-- Definición del tipo de pares dependientes
data 𝟙 : 𝒰₀ where
  ⋆ : 𝟙

-- Teorema 2.8.4.
𝟙-induction : (A : 𝟙 → 𝒰 𝒾) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

!𝟙 : (C : 𝒰 𝒾) → (C → 𝟙)
!𝟙 C c = ⋆

-- Definición del tipo del coproducto
data _⊎_ (X : 𝒰 𝒾) (Y : 𝒰 𝒿) : 𝒰 (𝒾 ⊔ 𝒿) where
 inl : X → X ⊎ Y
 inr : Y → X ⊎ Y
infixr 20 _⊎_

-- Teorema 2.8.8.
⊎-ind : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (C : A ⊎ B → 𝒰 𝓀)
      → ((x : A) → C (inl x))
      → ((y : B) → C (inr y))
      → (z : A ⊎ B) → C z
⊎-ind C f g (inl x) = f x
⊎-ind C f g (inr y) = g y

-- Definición del tipo 2
𝟚 : 𝒰₀
𝟚 = 𝟙 ⊎ 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

-- Teorema 2.8.10.
𝟚-induction : (A : 𝟚 → 𝒰 𝒾) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁
```

## Sección 2.9. El tipo de los naturales

```agda
-- Definición del tipo de los naturales
data ℕ : 𝒰₀ where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

-- Teorema 2.9.3.
ℕ-induction : (A : ℕ → 𝒰 𝒾)
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction A a₀ f = h
  where
    h : (n : ℕ) → A n
    h 0        = a₀
    h (succ n) = f n (h n)

-- Ejemplo 2.9.5.
double : ℕ → ℕ
double 0 = 0
double (succ n) = succ (succ (double n))

-- Ejemplo 2.9.6.
add : ℕ → ℕ → ℕ
add 0 = id
add (succ n) = λ m → succ (add n m)
```

## Sección 2.10. Proposiciones como tipos

```agda
-- Definición 2.10.1.
logeq : (A : 𝒰 𝒾) (B : 𝒰 𝒿) → 𝒰 (𝒾 ⊔ 𝒿)
logeq A B = (A → B) × (B → A)

-- Ejemplo 2.10.2.
ej-1-10-2 : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A → 𝟘) ⊎ (B → 𝟘) → ((A × B) → 𝟘)
ej-1-10-2 (inl f1) (a , b) = f1 a
ej-1-10-2 (inr f2) (a , b) = f2 b

-- Ejemplo 2.10.3.
ej-1-10-3 : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿}
          → Σ x ꞉ A , (P x → 𝟘)
          → ((x : A) → P x)
          → 𝟘
ej-1-10-3 (a , g) h = g (h a)

-- Ejemplo 2.10.4.
ac : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {R : A → B → 𝒰 𝓀}
   → ((x : A) → Σ y ꞉ B , R x y)
   → Σ f ꞉ (A → B) , ((x : A) → R x (f x))
ac g = ((λ x → pr₁ (g x)) , (λ x → pr₂ (g x)))
```

## Sección 2.11. El tipo de identidades

```agda
-- Definición del tipo de identidades
data Id (X : 𝒰 𝒾) : X → X → 𝒰 𝒾 where
  refl : (x : X) → Id X x x
infix   0 Id

_≡_ : {X : 𝒰 𝒾} → X → X → 𝒰 𝒾
x ≡ y = Id _ x y
infix   0 _≡_
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

-- Ejemplo 2.11.2.
ej-1-11-2 : (n : ℕ) → (add 0 n ≡ n)
ej-1-11-2 n = refl n

-- Teorema 2.11.4.
𝕁 : (A : 𝒰 𝒾) (D : (x y : A) → x ≡ y → 𝒰 𝒿)
  → ((x : A) → D x x (refl x))
  → (x y : A) (p : x ≡ y) → D x y p
𝕁 A D d x x (refl x) = d x
```
