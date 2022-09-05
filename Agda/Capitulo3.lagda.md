# Capítulo 3. Teoría Homotópica de Tipos

<!--
```agda
module Capitulo3 where
open import Capitulo2 public
```
-->

## Sección 3.1. Introducción

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


## Sección 3.2. $n$-tipos

```agda

-- Definición 3.2.1.
isContr : 𝒰 𝒾 → 𝒰 𝒾
isContr A = Σ a ꞉ A , ((x : A) → a ≡ x)

-- Proposición 3.2.2.
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

×-preserves-isContr : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
                    → isContr A
                    → isContr B
                    → isContr (A × B)
×-preserves-isContr A B f g = Σ-preserves-isContr A (λ - → B) f (λ - → g)

retrac-preserves-isContr : (A : 𝒰 𝒾) (B : 𝒰 𝒿)
                         → A ◁ B
                         → isContr B
                         → isContr A
retrac-preserves-isContr A B s (b₀ , pf) =
  retraction s b₀ , λ a → begin
    retraction s b₀ ≡⟨ ap (retraction s) (pf (section s a)) ⟩
    retraction s (section s a) ≡⟨ retract-equation s a ⟩
    a ∎


-- Lema 3.2.3.
trHomc- : {A : 𝒰 𝒾} (a : A) {x₁ x₂ : A} (p : x₁ ≡ x₂) (q : a ≡ x₁)
          → tr (λ x → a ≡ x) p q ≡ q ∙ p
trHomc- a (refl _) (refl _) = refl (refl a)

-- Proposición 3.2.4.
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

isProp : (A : 𝒰 𝒾) → 𝒰 𝒾
isProp A = (x y : A) → x ≡ y

isProp-𝟙 : (x y : 𝟙) → x ≡ y
isProp-𝟙 ⋆ ⋆ = refl ⋆

isProp-𝟘 : (x y : 𝟘) → x ≡ y
isProp-𝟘 ()

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

isSet : 𝒰 𝒾 → 𝒰 𝒾
isSet X = {x y : X} (p q : x ≡ y) → (p ≡ q)

isSet-𝟘 : isSet 𝟘
isSet-𝟘 {}

isSet-ℕ : isSet ℕ
isSet-ℕ {m} {n} = isProp-ℕ-paths m n

is-n-2-type : (n : ℕ) (A : 𝒰 𝒾) → 𝒰 𝒾
is-n-2-type 0 A        = isContr A
is-n-2-type (succ n) A = (x y : A) → is-n-2-type n (x ≡ y)

n-type-cumul : (n : ℕ) (A : 𝒰 𝒾)
             → is-n-2-type n A
             → is-n-2-type (succ n) A
n-type-cumul 0 A (c , p) x y = ((p x)⁻¹ ∙ (p y)) , contraction
  where
    contraction : (q : x ≡ y) → p x ⁻¹ ∙ p y ≡ q
    contraction (refl x) = ⁻¹-left∙ _
n-type-cumul (succ n) A f x y = n-type-cumul n (x ≡ y) (f x y)

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

≃-preserves-n-type : (n : ℕ) (A : 𝒰 𝒾) (B : 𝒰 𝒿) → (A ≃ B)
                   → is-n-2-type n B
                   → is-n-2-type n A
≃-preserves-n-type n A B eqv f =
  retract-preserves-n-type n A B (≃-← eqv , ≃-→ eqv , ≃-η eqv) f

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

## Sección 3.2. Tipos Inductivos Superiores

En agda, los HITs se tienen que definir de una forma indirecta; esta es una limitación de agda, no de la teoría actual.
En todo caso, las definiciones en agda pueden ser omitidas de la lectura sin ningún inconveniente.
```agda

-- Proposición 3.3.1.
module Interval where
  private
    data I : 𝒰₀ where
      Zero : I
      One  : I

  𝕀 : 𝒰₀
  𝕀 = I

  0ᵢ : 𝕀
  0ᵢ = Zero

  1ᵢ : 𝕀
  1ᵢ = One

  postulate seg : 0ᵢ ≡ 1ᵢ

  𝕀-rec : (B : 𝒰 𝒾)
        → (b₀ b₁ : B)
        → (s : b₀ ≡ b₁)
        → 𝕀 → B
  𝕀-rec B b₀ b₁ s Zero = b₀
  𝕀-rec B b₀ b₁ s One = b₁

  𝕀-ind : (P : 𝕀 → 𝒰 𝒾)
        → (b₀ : P 0ᵢ)
        → (b₁ : P 1ᵢ)
        → (s : tr P seg b₀ ≡ b₁)
        → ((x : 𝕀) → P x)
  𝕀-ind P b₀ b₁ s Zero = b₀
  𝕀-ind P b₀ b₁ s One = b₁

  postulate 𝕀-rec-comp : (B : 𝒰 𝒾)
                       → (b₀ b₁ : B)
                       → (s : b₀ ≡ b₁)
                       → (ap (𝕀-rec B b₀ b₁ s) seg ≡ s)
  postulate 𝕀-ind-comp : (P : 𝕀 → 𝒰 𝒾)
                       → (b₀ : P 0ᵢ)
                       → (b₁ : P 1ᵢ)
                       → (s : tr P seg b₀ ≡ b₁)
                       → (apd (𝕀-ind P b₀ b₁ s) seg ≡ s)

open Interval public

-- Proposición 3.3.2.
𝕀-isContr : isContr 𝕀
𝕀-isContr = (0ᵢ , λ x → contr x)
 where
  contr : (x : 𝕀) → (0ᵢ ≡ x)
  contr = 𝕀-ind (0ᵢ ≡_) (refl 0ᵢ) seg treq
   where
    treq : tr (0ᵢ ≡_) seg (refl 0ᵢ) ≡ seg
    treq = trHomc- 0ᵢ seg (refl 0ᵢ) ∙ refl-left


-- Proposición 3.3.3.
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
```
