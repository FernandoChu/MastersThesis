# Preliminares

Este módulo sirve para cambiar la notación de Agda
para utilizar una más similar a la de mi tesis.
Este módulo puede ser ignorado sin ningún problema.

```agda

module Preliminares where

open import Agda.Primitive public
  renaming (
            Set to Universe
          ; lsuc to infix 1 _⁺
          ; Setω to 𝓤ω)

variable
  𝒾 𝒿 𝓀 : Level

𝒰 : (ℓ : Level) → Universe (ℓ ⁺)
𝒰 ℓ = Universe ℓ

𝒰₀ = Universe lzero
𝒰₁ = Universe (lzero ⁺)
𝒰₂ = Universe (lzero ⁺ ⁺)
𝒰₃ = Universe (lzero ⁺ ⁺ ⁺)

_⁺⁺ : (ℓ : Level) → Level
ℓ ⁺⁺ = (ℓ ⁺) ⁺
```
