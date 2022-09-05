# Apéndice B. Resultados técnicos

<!--
```agda
module ApendiceB where
open import Capitulo3 public
```
-->

```agda

-- Lema 2.1.
fibra≃ : (A : 𝒰 𝒾) (B : A → 𝒰 𝒿) (x : A)
     → (B x) ≃ (Σ z ꞉ (Σ B) , pr₁ z ≡ x)
fibra≃ A B x = f , invs-are-equivs f (g , ε , η)
  where
    f = λ y → (x , y) , refl x
    g : (Σ z ꞉ (Σ B) , pr₁ z ≡ x) → B x
    g ((a , b) , refl _) = b
    ε : (α : (Σ z ꞉ (Σ B) , pr₁ z ≡ x)) → f (g α) ≡ α
    ε ((a , b) , refl _) = refl _
    η = λ y → refl y

fibra= : (A : 𝒰 𝒾) (B : A → 𝒰 𝒾) (x : A)
      → (B x) ≡ (Σ z ꞉ (Σ B) , pr₁ z ≡ x)
fibra= A B x = ua (fibra≃ A B x)

-- Lema 2.2.
paths-over-≃ : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿)
       (x y : A) (p : x ≡ y)
       (u : P x) (v : P y)
     → (Σ q ꞉ ((x , u) ≡ (y , v)) , (ap pr₁ q ≡ p)) ≃ (tr P p u ≡ v)
paths-over-≃ P x y p u v = f p , invs-are-equivs (f p) (g p , ε p , η)
  where
    f : (p : x ≡ y) → (Σ q ꞉ (x , u ≡ y , v) , ap pr₁ q ≡ p) → tr P p u ≡ v
    f p (refl _ , refl _) = refl u
    g : (p : x ≡ y) → tr P p u ≡ v → Σ q ꞉ (x , u ≡ y , v) , ap pr₁ q ≡ p
    g p (refl _) = (lift u p) , lift-lemma u p
    ε : (p : x ≡ y) → (s : tr P p u ≡ v) → f p (g p s) ≡ s
    ε (refl _) (refl _) = refl _
    η : (α : (Σ q ꞉ (x , u ≡ y , v) , ap pr₁ q ≡ p)) → g p (f p α) ≡ α
    η (refl _ , refl _) = refl _

```
