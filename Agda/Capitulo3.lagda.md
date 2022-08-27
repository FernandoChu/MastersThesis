# Capítulo 3. Teoría Homotópica de Tipos

<!--
```agda
module Capitulo3 where
open import Capitulo2 public
```
-->

## Sección 2.2. Los tipos son 1-grupoides

```agda

-- Proposición 3.1.1.
pr₁-is-fibration : (B : 𝒰 𝒾) (P : B → 𝒰 𝒿) (X : 𝒰 𝓀)
                   (f g : X → B) (h : f ∼ g)
                   (f' : (x : X) → P (f x))
                 → Σ h' ꞉ ((x : X) → Id (Σ P) (f x , f' x) (g x , tr P (h x) (f' x))),
                     ((x : X) → ap pr₁ (h' x) ≡ h x)
pr₁-is-fibration B P X f g h f' =
  h' , h'-lifts-h
 where
  h' : (x : X) → Id (Σ P) (f x , f' x) (g x , tr P (h x) (f' x))
  h' x = pair⁼(h x , refl _)

  lema : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} {w w' : Σ Y}
          (p : (pr₁ w ≡ pr₁ w')) → (q : tr Y p (pr₂ w) ≡ (pr₂ w'))
        → ap pr₁ (pair⁼(p , q)) ≡ p
  lema (refl _) (refl _) = refl _

  h'-lifts-h : (x : X) → ap pr₁ (h' x) ≡ h x
  h'-lifts-h x = lema (h x) (refl _)

-- Definición 3.1.2.
has-section : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 (𝒾 ⊔ 𝒿)
has-section r = Σ s ꞉ (codomain r → domain r), r ∘ s ∼ id

_◁_ : 𝒰 𝒾 → 𝒰 𝒿 → 𝒰 (𝒾 ⊔ 𝒿)
X ◁ Y = Σ r ꞉ (Y → X), has-section r

retraction : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ◁ Y → Y → X
retraction (r , s , ε) = r

section : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ◁ Y → X → Y
section (r , s , ε) = s

-- Helpers
retract-equation : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (ρ : X ◁ Y)
                 → retraction ρ ∘ section ρ ∼ 𝑖𝑑 X
retract-equation (r , s , ε) = ε

retraction-has-section : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (ρ : X ◁ Y)
                       → has-section (retraction ρ)
retraction-has-section (r , h) = h
```
