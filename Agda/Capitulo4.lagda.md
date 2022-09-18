---
title: Capítulo 4. Teoría Homotópica de Tipos
---

# Capítulo 4. Teoría Homotópica de Tipos

<!--
```agda
module Capitulo4 where
open import Capitulo3 public
```
-->

## Sección 4.1. Introducción

```agda
-- Proposición 4.1.1.
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

-- Definición 4.1.2.
has-section : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → (X → Y) → 𝒰 (𝒾 ⊔ 𝒿)
has-section r = Σ s ꞉ (codomain r → domain r), r ∘ s ∼ id

-- Helpers
_◁_ : 𝒰 𝒾 → 𝒰 𝒿 → 𝒰 (𝒾 ⊔ 𝒿)
X ◁ Y = Σ r ꞉ (Y → X), has-section r

retraction : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ◁ Y → Y → X
retraction (r , s , ε) = r

section : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ◁ Y → X → Y
section (r , s , ε) = s

retract-equation : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (ρ : X ◁ Y)
                 → retraction ρ ∘ section ρ ∼ 𝑖𝑑 X
retract-equation (r , s , ε) = ε
```

## Sección 4.2. $n$-tipos

```agda
-- Definición 4.2.1.
isContr : 𝒰 𝒾 → 𝒰 𝒾
isContr A = Σ a ꞉ A , ((x : A) → a ≡ x)

-- Ejemplo 4.2.2.
isContr-𝟙 : isContr 𝟙
isContr-𝟙 = (⋆ , contr)
  where
    contr : (x : 𝟙) → ⋆ ≡ x
    contr ⋆ = refl ⋆

-- Proposition 4.2.3.
isTerminal-𝟙 : (C : 𝒰 𝒾) (f : C → 𝟙) → f ≡ !𝟙 C
isTerminal-𝟙 C f = (funext (λ x → pr₂ isContr-𝟙 (f x)))⁻¹

-- Proposición 4.2.4.
isContr→≃𝟙 : (A : 𝒰 𝒾) → isContr A → A ≃ 𝟙
isContr→≃𝟙 A (c , p) = f , invs-are-equivs f (g , ε , η)
  where
    f = λ x → ⋆
    g = λ x → c
    ε : (x : 𝟙) → f (g x) ≡ x
    ε ⋆ = refl ⋆
    η = λ x → p x

≃𝟙→isContr : (A : 𝒰 𝒾) → A ≃ 𝟙 → isContr A
≃𝟙→isContr A eqv = ≃-← eqv ⋆ , res
  where
    eq-el-𝟙 : (x : 𝟙) → ⋆ ≡ x
    eq-el-𝟙 ⋆ = refl ⋆
    res : (x : A) → ≃-← eqv ⋆ ≡ x
    res x = begin
      ≃-← eqv ⋆ ≡⟨ ap (≃-← eqv) (eq-el-𝟙 (≃-→ eqv x)) ⟩
      ≃-← eqv (≃-→ eqv x) ≡⟨ ≃-η eqv x ⟩
      x ∎

-- Proposición 4.2.5.
Σ-preserves-isContr : (A : 𝒰 𝒾) (B : A → 𝒰 𝒿)
                    → isContr A
                    → ((a : A) → isContr (B a))
                    → isContr (Σ B)
Σ-preserves-isContr A B (a₀ , pf) f = (a₀ , b₀) , res
 where
  b₀ : B (a₀)
  b₀ = pr₁ (f a₀)
  q : (b : B a₀) → b₀ ≡ b
  q = pr₂ (f a₀)
  res : (x : Σ B) → a₀ , b₀ ≡ x
  res (a , b) = pair⁼(p , pr₂=)
   where
    p : a₀ ≡ a
    p = pf a
    pr₂= : tr B p b₀ ≡ b
    pr₂= = begin
     tr B p b₀ ≡⟨ ap (tr B p) (q _) ⟩
     tr B p (tr B (p ⁻¹) b) ≡⟨ happly (tr-∘ B (p ⁻¹) p) b ⟩
     tr B (p ⁻¹ ∙ p) b ≡⟨ ap (λ - → tr B - b) (⁻¹-left∙ p) ⟩
     tr B (refl a) b ≡⟨⟩
     b ∎

-- Corolario 4.2.6.
×-preserves-isContr : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
                    → isContr A
                    → isContr B
                    → isContr (A × B)
×-preserves-isContr A B f g = Σ-preserves-isContr A (λ - → B) f (λ - → g)

-- Proposición 4.2.7.
retrac-preserves-isContr : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
                         → A ◁ B
                         → isContr B
                         → isContr A
retrac-preserves-isContr A B s (b₀ , pf) =
  retraction s b₀ , λ a → begin
    retraction s b₀ ≡⟨ ap (retraction s) (pf (section s a)) ⟩
    retraction s (section s a) ≡⟨ retract-equation s a ⟩
    a ∎


-- Lema 4.2.8.
trHomc- : {A : 𝒰 𝒾} (a : A) {x₁ x₂ : A} (p : x₁ ≡ x₂) (q : a ≡ x₁)
          → tr (λ x → a ≡ x) p q ≡ q ∙ p
trHomc- a (refl _) (refl _) = refl (refl a)

-- Proposición 4.2.9.
isContr-Paths→isProp : (A : 𝒰 𝒾)
                     → ((x y : A)
                     → isContr (x ≡ y))
                     → ((x y : A) → x ≡ y)
isContr-Paths→isProp A f x y = pr₁ (f x y)

isProp→isContr-Paths : (A : 𝒰 𝒾)
                     → ((x y : A) → x ≡ y)
                     → ((x y : A) → isContr (x ≡ y))
isProp→isContr-Paths A f x y = (g x ⁻¹ ∙ g y) , res
  where
    g : (z : A) → x ≡ z
    g z = f x z
    res : (p : x ≡ y) → (g x)⁻¹ ∙ g y ≡ p
    res p = begin
      (g x)⁻¹ ∙ g y               ≡˘⟨ ap (λ - → (g x)⁻¹ ∙ -) (apd g p) ⟩
      (g x)⁻¹ ∙ tr (x ≡_) p (g x) ≡⟨ ap (λ - → (g x)⁻¹ ∙ -) (trHomc- x p (g x)) ⟩
      (g x)⁻¹ ∙ (g x ∙ p)         ≡˘⟨ ∙-assoc ((g x)⁻¹) ⟩
      ((g x)⁻¹ ∙ g x) ∙ p         ≡⟨ ap (λ - → - ∙ p) (⁻¹-left∙ (g x)) ⟩
      (refl x) ∙ p                ≡⟨ refl-left ⟩
      p  ∎

-- Definción 4.2.10.
isProp : (A : 𝒰 𝒾) → 𝒰 𝒾
isProp A = (x y : A) → x ≡ y

-- Ejemplo 4.2.11.
isContr→isProp : (A : 𝒰 𝒾) → isContr A → isProp A
isContr→isProp A (c , p) = λ x y → (p x)⁻¹ ∙ p y

isProp-𝟙 : (x y : 𝟙) → x ≡ y
isProp-𝟙 ⋆ ⋆ = refl ⋆

-- Ejemplo 4.2.12.
isProp-𝟘 : (x y : 𝟘) → x ≡ y
isProp-𝟘 ()

-- Ejemplo 4.2.14.
isProp-ℕ-paths : (m n : ℕ) (p q : m ≡ n) → p ≡ q
isProp-ℕ-paths m n p q = begin
  p                             ≡˘⟨ ≃-η (ℕ-≡-≃ m n) p ⟩
  decode-ℕ m n (encode-ℕ m n p) ≡⟨ ap (decode-ℕ m n) (lema m n _ _) ⟩
  decode-ℕ m n (encode-ℕ m n q) ≡⟨ ≃-η (ℕ-≡-≃ m n) q ⟩
  q ∎
  where
    lema : (m n : ℕ) (p q : code-ℕ m n) → p ≡ q
    lema zero zero p q         = isProp-𝟙 p q
    lema (succ m) zero p q     = isProp-𝟘 p q
    lema zero (succ n) p q     = isProp-𝟘 p q
    lema (succ m) (succ n) p q = lema m n p q

-- Definción 4.2.15.
isSet : 𝒰 𝒾 → 𝒰 𝒾
isSet X = {x y : X} (p q : x ≡ y) → (p ≡ q)

-- Ejemplo 4.2.16.
isSet-𝟘 : isSet 𝟘
isSet-𝟘 {}

-- Ejemplo 4.2.17.
isSet-ℕ : isSet ℕ
isSet-ℕ {m} {n} = isProp-ℕ-paths m n

-- Definción 4.2.18.
is-n-2-type : (n : ℕ) (A : 𝒰 𝒾) → 𝒰 𝒾
is-n-2-type 0 A        = isContr A
is-n-2-type (succ n) A = (x y : A) → is-n-2-type n (x ≡ y)

-- Proposición 4.2.19.
n-type-cumul : (n : ℕ) (A : 𝒰 𝒾)
             → is-n-2-type n A
             → is-n-2-type (succ n) A
n-type-cumul 0 A (c , p) x y = ((p x)⁻¹ ∙ (p y)) , contraction
  where
    contraction : (q : x ≡ y) → p x ⁻¹ ∙ p y ≡ q
    contraction (refl x) = ⁻¹-left∙ _
n-type-cumul (succ n) A f x y = n-type-cumul n (x ≡ y) (f x y)

-- Proposición 4.2.20.
retract-preserves-n-type : (n : ℕ) (A : 𝒰 𝒾) (B : 𝒰 𝒿) → (A ◁ B)
                         → is-n-2-type n B
                         → is-n-2-type n A
retract-preserves-n-type 0 A B s f = retrac-preserves-isContr A B s f
retract-preserves-n-type (succ n) A B rs f a₁ a₂ =
  retract-preserves-n-type n (a₁ ≡ a₂) (s a₁ ≡ s a₂) ret (f (s a₁) (s a₂))
 where
  r = retraction rs
  s = section rs
  ε = retract-equation rs
  t : (s a₁ ≡ s a₂) → (a₁ ≡ a₂)
  t q = (ε a₁)⁻¹ ∙ ap r q ∙ ε a₂
  ret : (a₁ ≡ a₂) ◁ (s a₁ ≡ s a₂)
  ret = t , ap s , htpy
   where
    htpy : t ∘ ap s ∼ id
    htpy p = begin
     ((ε a₁)⁻¹ ∙ ap r (ap s p)) ∙ ε a₂  ≡⟨ ∙-assoc _ ⟩
     (ε a₁)⁻¹ ∙ (ap r (ap s p) ∙ ε a₂)  ≡˘⟨ ap (λ - → (ε a₁)⁻¹ ∙ (- ∙ ε a₂)) (ap-∘ _ _ _) ⟩
     (ε a₁)⁻¹ ∙ ((ap (r ∘ s) p) ∙ ε a₂) ≡˘⟨ ap ((ε a₁)⁻¹ ∙_) (∼-naturality _ _ ε) ⟩
     (ε a₁)⁻¹ ∙ (ε a₁ ∙ ap id p)        ≡⟨ ap (λ - → (ε a₁)⁻¹ ∙ (ε a₁ ∙ -)) (ap-id _) ⟩
     (ε a₁)⁻¹ ∙ (ε a₁ ∙ p)              ≡˘⟨ ∙-assoc _ ⟩
     ((ε a₁)⁻¹ ∙ ε a₁) ∙ p              ≡⟨ ap (_∙ p) (⁻¹-left∙ _) ⟩
     (refl a₁) ∙ p                      ≡⟨ refl-left ⟩
     p ∎

-- Corolario 4.2.21.
≃-preserves-n-type : (n : ℕ) (A : 𝒰 𝒾) (B : 𝒰 𝒿) → (A ≃ B)
                   → is-n-2-type n B
                   → is-n-2-type n A
≃-preserves-n-type n A B eqv f =
  retract-preserves-n-type n A B (≃-← eqv , ≃-→ eqv , ≃-η eqv) f

-- Proposición 4.2.22.
Σ-preserves-n-type : (A : 𝒰 𝒾) (B : A → 𝒰 𝒿) (n : ℕ)
                   → is-n-2-type n A
                   → ((a : A) → is-n-2-type n (B a))
                   → is-n-2-type n (Σ B)
Σ-preserves-n-type {𝒾} {𝒿} A B 0 f g = Σ-preserves-isContr A B f g
Σ-preserves-n-type {𝒾} {𝒿} A B (succ n) f g (a₁ , b₁) (a₂ , b₂) =
  ≃-preserves-n-type n _ _ paths≃ Σ-is-ntype
  where
    paths≃ : ((a₁ , b₁) ≡ (a₂ , b₂)) ≃ (Σ p ꞉ (a₁ ≡ a₂) , tr B p b₁ ≡ b₂)
    paths≃ = Σ-≡-≃
    Σ-is-ntype : is-n-2-type n (Σ p ꞉ (a₁ ≡ a₂) , tr B p b₁ ≡ b₂)
    Σ-is-ntype = Σ-preserves-n-type (a₁ ≡ a₂) (λ p → tr B p b₁ ≡ b₂) n (f a₁ a₂) lema
      where
        lema : (a : a₁ ≡ a₂) → is-n-2-type n (tr B a b₁ ≡ b₂)
        lema (refl _) = g a₁ b₁ b₂
```

## Sección 4.3. Tipos Inductivos Superiores

En agda, los HITs se tienen que definir de una forma indirecta; esta es una limitación de agda, no de la teoría actual.
En todo caso, las definiciones en agda pueden ser omitidas de la lectura sin ningún inconveniente.

```agda
-- Definición 4.3.1.
postulate
  𝕀 : 𝒰₀
  0ᵢ : 𝕀
  1ᵢ : 𝕀
  seg : 0ᵢ ≡ 1ᵢ
  𝕀-rec : (B : 𝒰 𝒾)
        → (b₀ b₁ : B)
        → (s : b₀ ≡ b₁)
        → 𝕀 → B
  𝕀-rec-comp-0ᵢ : (B : 𝒰 𝒾)
                → (b₀ b₁ : B)
                → (s : b₀ ≡ b₁)
                → 𝕀-rec B b₀ b₁ s 0ᵢ ≡ b₀
  𝕀-rec-comp-1ᵢ : (B : 𝒰 𝒾)
                → (b₀ b₁ : B)
                → (s : b₀ ≡ b₁)
                → 𝕀-rec B b₀ b₁ s 1ᵢ ≡ b₁
  {-# REWRITE 𝕀-rec-comp-0ᵢ 𝕀-rec-comp-1ᵢ #-}
  𝕀-rec-comp : (B : 𝒰 𝒾)
             → (b₀ b₁ : B)
             → (s : b₀ ≡ b₁)
             → (ap (𝕀-rec B b₀ b₁ s) seg ≡ s)
  𝕀-ind : (P : 𝕀 → 𝒰 𝒾)
        → (b₀ : P 0ᵢ)
        → (b₁ : P 1ᵢ)
        → (s : tr P seg b₀ ≡ b₁)
        → ((x : 𝕀) → P x)
  𝕀-ind-comp-0ᵢ : (P : 𝕀 → 𝒰 𝒾)
                → (b₀ : P 0ᵢ)
                → (b₁ : P 1ᵢ)
                → (s : tr P seg b₀ ≡ b₁)
                → 𝕀-ind P b₀ b₁ s 0ᵢ ≡ b₀
  𝕀-ind-comp : (P : 𝕀 → 𝒰 𝒾)
             → (b₀ : P 0ᵢ)
             → (b₁ : P 1ᵢ)
             → (s : tr P seg b₀ ≡ b₁)
             → 𝕀-ind P b₀ b₁ s 1ᵢ ≡ b₁

-- Proposición 4.3.2.
𝕀-isContr : isContr 𝕀
𝕀-isContr = (0ᵢ , λ x → contr x)
 where
  contr : (x : 𝕀) → (0ᵢ ≡ x)
  contr = 𝕀-ind (0ᵢ ≡_) (refl 0ᵢ) seg treq
   where
    treq : tr (0ᵢ ≡_) seg (refl 0ᵢ) ≡ seg
    treq = trHomc- 0ᵢ seg (refl 0ᵢ) ∙ refl-left

-- Proposición 4.3.3.
funext' : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
        → (f g : A → B)
        → ((x : A) → (f x ≡ g x))
        → f ≡ g
funext' A B f g p = ap β seg
  where
    α : A → 𝕀 → B
    α x = 𝕀-rec B (f x) (g x) (p x)
    β : 𝕀 → (A → B)
    β i x = α x i

-- Definición 4.3.4.
postulate
  𝕊¹ : 𝒰₀
  base : 𝕊¹
  loop : base ≡ base
  𝕊¹-rec : (B : 𝒰 𝒾)
         → (b : B)
         → (l : b ≡ b)
         → ((x : 𝕊¹) → B)
  𝕊¹-rec-comp-base : (B : 𝒰 𝒾)
                   → (b : B)
                   → (l : b ≡ b)
                   → 𝕊¹-rec B b l base ≡ b
  {-# REWRITE 𝕊¹-rec-comp-base #-}
  𝕊¹-rec-comp : (B : 𝒰 𝒾)
              → (b : B)
              → (l : b ≡ b)
              → ap (𝕊¹-rec B b l) loop ≡ l
  𝕊¹-ind : (P : 𝕊¹ → 𝒰 𝒾)
         → (b : P base)
         → (l : tr P loop b ≡ b)
         → ((x : 𝕊¹) → P x)
  𝕊¹-ind-comp-base : (P : 𝕊¹ → 𝒰 𝒾)
                   → (b : P base)
                   → (l : tr P loop b ≡ b)
                   → 𝕊¹-ind P b l base ≡ b
  {-# REWRITE 𝕊¹-ind-comp-base #-}
  𝕊¹-ind-comp : (P : 𝕊¹ → 𝒰 𝒾)
              → (b : P base)
              → (l : tr P loop b ≡ b)
              → (apd (𝕊¹-ind P b l) loop ≡ l)

-- Definición 4.3.5.
postulate
  𝕊² : 𝒰₀
  base' : 𝕊²
  surf : refl base' ≡ refl base'

-- Definición 4.3.6.
postulate
  T² : 𝒰₀
  bT² : T²
  pT² : bT² ≡ bT²
  qT² : bT² ≡ bT²
  tT² : pT² ∙ qT² ≡ qT² ∙ pT²

-- Definición 4.3.7.
postulate
  ∥_∥₀ : {𝒾 : Level} → (A : 𝒰 𝒾) → 𝒰 𝒾
  ∣_∣ : {𝒾 : Level} → {A : 𝒰 𝒾} → A → ∥ A ∥₀
  ∥∥₀-rec : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
          → isSet B
          → (g : A → B)
          → ∥ A ∥₀ → B
  ∥∥₀-rec-comp : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
               → (p : isSet B)
               → (g : A → B)
               → (a : A)
               → ∥∥₀-rec A B p g (∣ a ∣) ≡ g a
  {-# REWRITE ∥∥₀-rec-comp #-}
  ∥∥₀-rec-unique : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
                 → (p : isSet B)
                 → (g : A → B)
                 → (h : (∥ A ∥₀ → B))
                 → (h ∘ ∣_∣ ≡ g)
                 → ∥∥₀-rec A B p g ≡ h
  ∥∥₀-isSet : {X : 𝒰 𝒾} → isSet (∥ X ∥₀)


-- Proposición 4.3.8.
∥∥₀-set-is-id : (A : 𝒰 𝒾)
              → isSet A
              → ∥ A ∥₀ ≡ A
∥∥₀-set-is-id A p = ua (f , invs-are-equivs f (g , ε , η))
  where
    f = ∥∥₀-rec A A p id
    g = ∣_∣
    ε = λ x → refl x
    η = λ x → happly g∘f≡id x
      where
        rec∣_∣≡id : ∥∥₀-rec A (∥ A ∥₀) ∥∥₀-isSet ∣_∣ ≡ id
        rec∣_∣≡id = ∥∥₀-rec-unique A (∥ A ∥₀) ∥∥₀-isSet
                       ∣_∣ id (funext (λ _ → refl _))
        rec∣_∣≡g∘f : ∥∥₀-rec A (∥ A ∥₀) ∥∥₀-isSet ∣_∣ ≡ (g ∘ f)
        rec∣_∣≡g∘f = ∥∥₀-rec-unique A (∥ A ∥₀) ∥∥₀-isSet
                        ∣_∣ (g ∘ f) (funext (λ _ → refl _))
        g∘f≡id : g ∘ f ≡ id
        g∘f≡id = (rec∣_∣≡g∘f)⁻¹ ∙ rec∣_∣≡id

-- Definición 4.3.9.
postulate
  ℤ : 𝒰₀
  0ℤ : ℤ
  succℤ : ℤ ≃ ℤ
  ℤ-rec : (X : 𝒰 𝒾)
          (b : X)
          (s : X ≃ X)
        → ℤ → X
  ℤ-rec-comp : (X : 𝒰 𝒾)
               (b : X)
               (s : X ≃ X)
             → ℤ-rec X b s 0ℤ ≡ b
  {-# REWRITE ℤ-rec-comp #-}
  ℤ-rec-succℤ : (X : 𝒰 𝒾)
                (b : X)
                (s : X ≃ X)
                (a : ℤ)
              → ℤ-rec X b s (≃-→ succℤ a) ≡ ≃-→ s (ℤ-rec X b s a)
  ℤ-rec-unique : (X : 𝒰 𝒾)
                 (f : ℤ → X)
                 (z : X)
                 (s : X ≃ X)
               → f 0ℤ ≡ z
               → ((f ∘ ≃-→ succℤ) ∼ (≃-→ s ∘ f))
               → (x : ℤ) → f x ≡ ℤ-rec X z s x
  hSetℤ : isSet ℤ

```

## Sección 4.4. El grupo fundamental del círculo

```agda
-- Definición 4.4.1.
Ωn : (n : ℕ) (A : 𝒰 𝒾) (a : A) → (Σ X ꞉ 𝒰 𝒾 , X)
Ωn 0 A a        = (A , a)
Ωn (succ n) A a = Ωn n (a ≡ a) (refl a)

-- Definición 4.4.2.
πₙ : (n : ℕ) (A : 𝒰 𝒾) (a : A) → _
πₙ n A a = ∥ pr₁ (Ωn n A a) ∥₀

-- Lema 4.4.3.
loop^ : ℤ → base ≡ base
loop^ = ℤ-rec (base ≡ base) (refl base) (f , invs-are-equivs f (g , ε , η))
  where
    f = _∙ loop
    g = _∙ (loop ⁻¹)
    ε = λ p → begin
      p ∙ (loop)⁻¹ ∙ loop   ≡⟨ ∙-assoc p ⟩
      p ∙ ((loop)⁻¹ ∙ loop) ≡⟨ ap (p ∙_) (⁻¹-left∙ loop) ⟩
      p ∙ refl _            ≡⟨ refl-right ⟩
      p ∎
    η = λ p → begin
      p ∙ loop ∙ (loop)⁻¹   ≡⟨ ∙-assoc p ⟩
      p ∙ (loop ∙ (loop)⁻¹) ≡⟨ ap (p ∙_) (⁻¹-right∙ loop) ⟩
      p ∙ refl _            ≡⟨ refl-right ⟩
      p ∎

-- Definición 4.4.4.
Cover : 𝕊¹ → 𝒰₀
Cover = 𝕊¹-rec 𝒰₀ ℤ (ua succℤ)

-- Lema 4.4.5.
tr-Cover-loop : (x : ℤ) → tr Cover loop x ≡ ≃-→ succℤ x
tr-Cover-loop x = begin
  tr Cover loop x                ≡⟨⟩
  tr (id ∘ Cover) loop x         ≡˘⟨ happly (tr-ap-assoc Cover loop) x ⟩
  tr (λ x → x) (ap Cover loop) x ≡⟨ ap (λ - → tr id - x) (𝕊¹-rec-comp _ _ _) ⟩
  tr (λ x → x) (ua succℤ) x      ≡⟨⟩
  pr₁ (idtoeqv (ua succℤ)) x     ≡⟨ happly (ap pr₁ (id∼idtoeqv∘ua succℤ)⁻¹) x ⟩
  pr₁ succℤ x                    ∎

-- Lema 4.4.6.
encode : (x : 𝕊¹) → (base ≡ x) → Cover x
encode x p = tr Cover p 0ℤ

-- Lema 4.4.7.
decode : (x : 𝕊¹) → Cover x → (base ≡ x)
decode = 𝕊¹-ind (λ x → Cover x → base ≡ x) loop^ ≡tr
 where
  ≡tr : tr (λ x → Cover x → base ≡ x) loop loop^ ≡ loop^
  ≡tr = begin
    tr (λ x → Cover x → base ≡ x) loop loop^       ≡⟨ i ⟩
    tr (base ≡_) loop ∘ loop^ ∘ tr Cover (loop ⁻¹) ≡⟨ ii ⟩
    (_∙ loop) ∘ loop^ ∘ tr Cover (loop ⁻¹)         ≡˘⟨ iii ⟩
    loop^ ∘ (≃-→ succℤ) ∘ tr Cover (loop ⁻¹)       ≡˘⟨ iv ⟩
    loop^ ∘ tr Cover loop ∘ tr Cover (loop ⁻¹)     ≡⟨⟩
    loop^ ∘ (tr Cover loop ∘ tr Cover (loop ⁻¹))   ≡⟨ v ⟩
    loop^ ∘ (tr Cover ((loop)⁻¹ ∙ loop))           ≡⟨ vi ⟩
    loop^ ∘ (tr Cover (refl base))                 ≡⟨⟩
    loop^ ∎
   where
    i   = funext (λ - → PathOver-→ {p = loop})
    ii  = ap (λ - → - ∘ loop^ ∘ tr Cover (loop ⁻¹))
             (funext (λ - → trHomc- base loop -))
    iii = ap (_∘ tr Cover (loop ⁻¹)) (funext (λ - → ℤ-rec-succℤ _ _ _ -))
    iv  = ap (λ - → loop^ ∘ - ∘ tr Cover (loop ⁻¹)) (funext tr-Cover-loop)
    v   = ap (λ - → loop^ ∘ -) (tr-∘ Cover (loop ⁻¹) loop)
    vi  = ap (λ - → loop^ ∘ (tr Cover -)) (⁻¹-left∙ loop)

-- Lema 4.4.8.
encode-decode : (x : 𝕊¹) (p : base ≡ x) → decode x (encode x p) ≡ p
encode-decode x (refl base) = refl _

-- Lema 4.4.9.
endo-ℤ-is-id : (f : ℤ → ℤ)
             → f 0ℤ ≡ 0ℤ
             → (f ∘ ≃-→ succℤ) ∼ (≃-→ succℤ ∘ f)
             → f ∼ id
endo-ℤ-is-id f f0 fsucc x = begin
  f x                 ≡⟨ ℤ-rec-unique _ f 0ℤ succℤ f0 fsucc x ⟩
  ℤ-rec ℤ 0ℤ succℤ x  ≡˘⟨ ℤ-rec-unique _ id 0ℤ succℤ (refl _) (\ _ → refl _) x ⟩
  x                   ∎

-- Lema 4.4.10.
tr-Cover-then-loop : {x : 𝕊¹} (p : x ≡ base) (y : Cover x)
                          → tr Cover (p ∙ loop) y ≡ ≃-→ succℤ (tr Cover p y)
tr-Cover-then-loop (refl _) y = begin
  tr Cover (refl base ∙ loop) y ≡⟨ ap (λ - → tr Cover - y)
                                      (refl-left {p = loop}) ⟩
  tr Cover loop y               ≡⟨ tr-Cover-loop y ⟩
  ≃-→ succℤ y                   ∎

-- Lema 4.4.11.
decode-encode-base : (x : ℤ) → encode base (loop^ x) ≡ x
decode-encode-base x =
  endo-ℤ-is-id encode-loop^ encode-loop^-zero encode-loop^-succ x
 where
  encode-loop^ : ℤ → ℤ
  encode-loop^ x = encode base (loop^ x)

  encode-loop^-zero : encode-loop^ 0ℤ ≡ 0ℤ
  encode-loop^-zero = refl _

  encode-loop^-succ : (encode-loop^ ∘ ≃-→ succℤ) ∼ (≃-→ succℤ ∘ encode-loop^)
  encode-loop^-succ x = begin
    (encode-loop^ ∘ ≃-→ succℤ) x ≡⟨ ap (encode base)
                                       (ℤ-rec-succℤ _ _ _ x) ⟩
    tr Cover (loop^ x ∙ loop) 0ℤ ≡⟨ tr-Cover-then-loop (loop^ x) 0ℤ ⟩
    (≃-→ succℤ ∘ encode-loop^) x ∎

-- Lema 4.4.12.
decode-encode : (x : 𝕊¹) (p : Cover x) → encode x (decode x p) ≡ p
decode-encode = 𝕊¹-ind _
                       decode-encode-base
                       (PathOver-Π {p = loop}
                                   {f = decode-encode-base}
                                   {g = decode-encode-base}
                                   (λ q → hSetℤ _ _))

-- Proposición 4.4.13.
≃-Cover : (x : 𝕊¹) → (base ≡ x) ≃ Cover x
≃-Cover x = encode x , invs-are-equivs (encode x)
                        (decode x , decode-encode x , encode-decode x)

-- Corolario 4.4.14.
Ω𝕊¹≡ℤ : (base ≡ base) ≡ ℤ
Ω𝕊¹≡ℤ = ua (≃-Cover base)

-- Corolario 4.4.15.
π₁𝕊¹≡ℤ : πₙ 1 𝕊¹ base ≡ ℤ
π₁𝕊¹≡ℤ = tr (λ - → ∥ - ∥₀ ≡ ℤ) (Ω𝕊¹≡ℤ ⁻¹) (∥∥₀-set-is-id ℤ hSetℤ)
```
