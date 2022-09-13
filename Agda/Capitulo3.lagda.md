# Capítulo 3. La Interpretación Homotópica

<!--
```agda
module Capitulo3 where
open import Capitulo2 public
```
-->

## Sección 3.2. Los tipos son 1-grupoides

```agda

-- Lema 3.2.1.
_∙_ : {X : 𝒰 𝒾} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
(refl x) ∙ (refl x) = (refl x)
infixl 30 _∙_

-- Lema 3.2.2.
refl-left : {X : 𝒰 𝒾} {x y : X} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {X} {x} {x} {refl x} = refl (refl x)

refl-right : {X : 𝒰 𝒾} {x y : X} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {X} {x} {y} {refl x} = refl (refl x)

-- Lema 3.2.3.
∙-assoc : {X : 𝒰 𝒾} {x y z t : X} (p : x ≡ y) {q : y ≡ z} {r : z ≡ t}
        → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙-assoc (refl x) {refl x} {refl x} = refl (refl x)

-- Lema 3.2.4.
_⁻¹ : {X : 𝒰 𝒾} → {x y : X} → x ≡ y → y ≡ x
(refl x)⁻¹ = refl x
infix  40 _⁻¹

⁻¹-left∙ : {X : 𝒰 𝒾} {x y : X} (p : x ≡ y)
         → p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-right∙ : {X : 𝒰 𝒾} {x y : X} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)

-- Lema 3.2.6.
⁻¹-involutive : {X : 𝒰 𝒾} {x y : X} (p : x ≡ y)
              → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive (refl x) = refl (refl x)

⁻¹-∙ : {X : 𝒰 𝒾} {x y z : X} (p : x ≡ y) {q : y ≡ z}
     → (p ∙ q)⁻¹ ≡  (q)⁻¹ ∙ (p)⁻¹
⁻¹-∙ (refl x) {refl x} = refl (refl x)

-- Helpers tomados de
-- https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html#2708
begin_ : {X : 𝒰 𝒾} {x y : X} → x ≡ y → x ≡ y
begin_ x≡y = x≡y
infix  1 begin_

_≡⟨⟩_ : {X : 𝒰 𝒾} (x {y} : X) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

step-≡ : {X : 𝒰 𝒾} (x {y z} : X) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = x≡y ∙ y≡z
syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

step-≡˘ : {X : 𝒰 𝒾} (x {y z} : X) → y ≡ z → y ≡ x → x ≡ z
step-≡˘ _ y≡z y≡x = (y≡x)⁻¹ ∙ y≡z
syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
infixr 2 _≡⟨⟩_ step-≡ step-≡˘

_∎ : {X : 𝒰 𝒾} (x : X) → x ≡ x
_∎ x = refl x
infix  3 _∎
```

## Sección 3.3. Funciones y functores

```agda

-- Lema 3.3.1.
ap : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f {x} {x'} (refl x) = refl (f x)

-- Lema 3.3.3.
ap-∙ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y) {x y z : X}
       (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f (refl x) (refl x) = refl (refl (f x))

-- Lema 3.3.4.
ap⁻¹ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} (f : X → Y) {x y : X} (p : x ≡ y)
     → (ap f p)⁻¹ ≡ ap f (p ⁻¹)
ap⁻¹ f {x} {y} p = (q4)⁻¹ ∙ (h1ap)⁻¹ ∙ q6 ∙ h2q5 ∙ q3
  where
   q1 : p ⁻¹ ∙ p ≡ refl y
   q1 = ⁻¹-left∙ p
   g : (y ≡ y) → (f y ≡ f y)
   g = λ r → ap f r
   gq1 : ap f (p ⁻¹ ∙ p) ≡ refl (f y)
   gq1 = ap g q1
   q2 : ap f (p ⁻¹ ∙ p) ≡ ap f (p ⁻¹) ∙ ap f p
   q2 = ap-∙ f (p ⁻¹) p
   h1 : (f y ≡ f y) → (f y ≡ f x)
   h1 = λ r → r ∙ ((ap f p)⁻¹)
   h1ap : (ap f (p ⁻¹) ∙ ap f p) ∙ ((ap f p)⁻¹) ≡ refl (f y) ∙ ((ap f p)⁻¹)
   h1ap = ap h1 ((q2 ⁻¹) ∙ gq1)
   q3 : (ap f (p ⁻¹)) ∙ refl (f x) ≡ ap f (p ⁻¹)
   q3 = refl-right
   q4 : refl (f y) ∙ (ap f p)⁻¹ ≡ (ap f p)⁻¹
   q4 = refl-left
   q5 : ap f p ∙ ap f p ⁻¹ ≡ refl (f x)
   q5 = ⁻¹-right∙ (ap f p)
   h2 : (f x ≡ f x) → (f y ≡ f x)
   h2 = λ r → ap f (p ⁻¹) ∙ r
   h2q5 : ap f (p ⁻¹) ∙ (ap f p ∙ ap f p ⁻¹) ≡ ap f (p ⁻¹) ∙ (refl (f x))
   h2q5 = ap h2 q5
   q6 : (ap f (p ⁻¹) ∙ ap f p) ∙ ((ap f p)⁻¹) ≡ ap f (p ⁻¹) ∙ (ap f p ∙ (ap f p)⁻¹)
   q6 = ∙-assoc (ap f (p ⁻¹))

-- Lema 3.3.5. (I)
ap-∘ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {Z : 𝒰 𝓀}
       (f : X → Y) (g : Y → Z) {x y : X} (p : x ≡ y)
     → ap (g ∘ f) p ≡ (ap g ∘ ap f) p
ap-∘ f g (refl x) = refl (refl (g (f x)))

-- Lema 3.3.5. (II)
ap-id : {X : 𝒰 𝒾} {x y : X} (p : x ≡ y)
      → ap id p ≡ p
ap-id (refl x) = refl (refl x)

-- Lema 3.3.5. (III)
∙-left-cancel : {X : 𝒰 𝒾} {x y z : X}
                (p : x ≡ y) {q r : y ≡ z}
              → p ∙ q ≡ p ∙ r
              → q ≡ r
∙-left-cancel p {q} {r} path = begin
  q              ≡˘⟨ refl-left ⟩
  refl _ ∙ q     ≡˘⟨ ap (_∙ q) (⁻¹-left∙ p) ⟩
  (p ⁻¹ ∙ p) ∙ q ≡⟨ ∙-assoc (p ⁻¹) ⟩
  p ⁻¹ ∙ (p ∙ q) ≡⟨ ap ((p ⁻¹) ∙_) path ⟩
  p ⁻¹ ∙ (p ∙ r) ≡˘⟨ ∙-assoc (p ⁻¹) ⟩
  (p ⁻¹ ∙ p) ∙ r ≡⟨ ap (_∙ r) (⁻¹-left∙ p) ⟩
  refl _ ∙ r     ≡⟨ refl-left ⟩
  r ∎

-- Lema 3.3.5. (IV)
∙-right-cancel : {X : 𝒰 𝒾} {x y z : X}
                 (p : x ≡ y) {q : x ≡ y} {r : y ≡ z}
               → p ∙ r ≡ q ∙ r
               → p ≡ q
∙-right-cancel p {q} {r} path = begin
  p              ≡˘⟨ refl-right ⟩
  p ∙ refl _     ≡˘⟨ ap (p ∙_) (⁻¹-right∙ r) ⟩
  p ∙ (r ∙ r ⁻¹) ≡˘⟨ ∙-assoc p ⟩
  (p ∙ r) ∙ r ⁻¹ ≡⟨ ap (_∙ (r ⁻¹)) path ⟩
  (q ∙ r) ∙ r ⁻¹ ≡⟨ ∙-assoc q ⟩
  q ∙ (r ∙ r ⁻¹) ≡⟨ ap (q ∙_) (⁻¹-right∙ r) ⟩
  q ∙ refl _     ≡⟨ refl-right ⟩
  q ∎
```

## Sección 3.4. Funciones dependientes y fibraciones

```agda

-- Lema 3.4.1.
tr : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿) {x y : A}
          → x ≡ y → P x → P y
tr P (refl x) = id

-- Lema 3.4.2.
tr-∘ : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿) {x y z : A}
       (p : x ≡ y) (q : y ≡ z)
     → (tr P q) ∘ (tr P p) ≡ tr P (p ∙ q)
tr-∘ P (refl x) (refl x) = refl id

-- Lema 3.4.4.
lift : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿}
       {x y : A} (u : P x) (p : x ≡ y)
     → ((x , u) ≡ (y , tr P p u))
lift u (refl x) = refl (x , u)

lift-lemma : {𝒾 𝒿 : Level} {A : 𝒰 𝒾} {P : A → 𝒰 𝒿}
             {x y : A} (u : P x) (p : x ≡ y)
           → (ap pr₁ (lift {𝒾} {𝒿} {A} {P} {x} {y} u p)) ≡ p
lift-lemma u (refl x) = refl (refl x)

-- Lema 3.4.5.
apd : {A : 𝒰 𝒾} {P : A → 𝒰 𝒿} (f : (x : A) → P x) {x y : A}
      (p : x ≡ y) → tr P p (f x) ≡ f y
apd f (refl x) = refl (f x)

-- Lema 3.4.6.
tr-f : {A : 𝒰 𝒾} (B : A → 𝒰 𝒿) (f : A → A)
       {x y : A} (p : x ≡ y)
     → tr B (ap f p) ≡ tr (B ∘ f) p
tr-f B f (refl _) = refl _

-- Lema 3.4.7.
tr-ap-assoc : {A : 𝒰 𝒾} (B : A → 𝒰 𝒿) {x y : A}
              (p : x ≡ y)
            → tr id (ap B p) ≡ tr B p
tr-ap-assoc B (refl _) = refl _

```

## Sección 3.5. Equivalencias homotópicas

```agda

-- Definición 3.5.1.
_∼_ : {X : 𝒰 𝒾} {P : X → 𝒰 𝒿} → ((x : X) → P x) → ((x : X) → P x) → 𝒰 (𝒾 ⊔ 𝒿)
f ∼ g = ∀ x → f x ≡ g x

∼-refl : {X : 𝒰 𝒾} {P : X → 𝒰 𝒿} (f : (x : X) → P x) → (f ∼ f)
∼-refl f = λ x → (refl (f x))

∼-sym : {X : 𝒰 𝒾} {P : X → 𝒰 𝒿}
      → (f g : (x : X) → P x)
      → (f ∼ g)
      → (g ∼ f)
∼-sym f g H = λ x → (H x)⁻¹

∼-trans : {X : 𝒰 𝒾} {P : X → 𝒰 𝒿}
        → (f g h : (x : X) → P x)
        → (f ∼ g)
        → (g ∼ h)
        → (f ∼ h)
∼-trans f g h H1 H2 = λ x → (H1 x) ∙ (H2 x)

-- Lema 3.5.2.
∼-naturality : {X : 𝒰 𝒾} {A : 𝒰 𝒿}
               (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
             → H x ∙ ap g p ≡ ap f p ∙ H y
∼-naturality f g H {x} {_} {refl a} = refl-right ∙ refl-left ⁻¹

-- Definición 3.5.3.
qinv : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A → B) → 𝒰 (𝒾 ⊔ 𝒿)
qinv f = Σ g ꞉ (codomain f → domain f) , (f ∘ g ∼ id) × (g ∘ f ∼ id)

-- Ejemplo 3.5.4.
qinv-id-id : (A : 𝒰 𝒾) → qinv (𝑖𝑑 A)
qinv-id-id A = (𝑖𝑑 A) , refl , refl

-- Ejemplo 3.5.5.
qinv-tr : {A : 𝒰 𝒾} {x y : A} (P : A → 𝒰 𝒿) (p : x ≡ y)
        → qinv (tr P p)
qinv-tr P (refl x) = id , refl , refl

-- Definición 3.5.6.
isequiv : {A : 𝒰 𝒾} {B : 𝒰 𝒿} → (A → B) → 𝒰 (𝒾 ⊔ 𝒿)
isequiv f = (Σ g ꞉ (codomain f → domain f) , (f ∘ g ∼ id))
           × (Σ h ꞉ (codomain f → domain f) , (h ∘ f ∼ id))

-- Proposición 3.5.7.
invs-are-equivs : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B)
                → (qinv f) → (isequiv f)
invs-are-equivs f ( g , α , β ) = ( (g , α) , (g , β) )

equivs-are-invs : {A : 𝒰 𝒾} {B : 𝒰 𝒿} (f : A → B)
                → (isequiv f) → (qinv f)
equivs-are-invs f ( (g , α) , (h , β) ) = ( g , α , β' )
  where
    γ : (x : codomain f) → (g x ≡ h x)
    γ x = begin
      g x ≡˘⟨ β (g x) ⟩
      h (f (g x)) ≡⟨ ap h (α x) ⟩
      h x ∎
    β' : g ∘ f ∼ 𝑖𝑑 (domain f)
    β' x = γ (f x) ∙ β x

-- Definición 3.5.8.
_≃_ : 𝒰 𝒾 → 𝒰 𝒿 → 𝒰 (𝒾 ⊔ 𝒿)
A ≃ B = Σ f ꞉ (A → B), isequiv f

-- Helpers para conseguir la data de quasi-inversas de una equivalencia
≃-→ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ≃ Y → (X → Y)
≃-→ (f , eqv) = f

≃-← : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ≃ Y → (Y → X)
≃-← (f , eqv) =
 let (g , ε , η) = equivs-are-invs f eqv
  in g

≃-ε : {X : 𝒰 𝒾} {Y : 𝒰 𝒿}
    → (equiv : (X ≃ Y))
    → ((pr₁ equiv) ∘ (≃-← equiv) ∼ id)
≃-ε (f , eqv) =
 let (g , ε , η) = equivs-are-invs f eqv
  in ε

≃-η : {X : 𝒰 𝒾} {Y : 𝒰 𝒿}
    → (equiv : (X ≃ Y))
    → ((≃-← equiv) ∘ (pr₁ equiv) ∼ id)
≃-η (f , eqv) =
 let (g , ε , η) = equivs-are-invs f eqv
  in η

-- Lema 3.5.9.
≃-refl : (X : 𝒰 𝒾) → X ≃ X
≃-refl X = ( 𝑖𝑑 X , invs-are-equivs (𝑖𝑑 X) (qinv-id-id X) )

≃-sym : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} → X ≃ Y → Y ≃ X
≃-sym ( f , e ) =
  let ( f⁻¹ , p , q) = ( equivs-are-invs f e )
  in  ( f⁻¹ , invs-are-equivs f⁻¹ (f , q , p) )

≃-trans-helper : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
                 (eqvf : A ≃ B) (eqvg : B ≃ C)
               → isequiv (pr₁ eqvg ∘ pr₁ eqvf)
≃-trans-helper ( f , ef ) ( g , eg ) =
  let ( f⁻¹ , pf , qf ) = ( equivs-are-invs f ef )
      ( g⁻¹ , pg , qg ) = ( equivs-are-invs g eg )
      h1 : ((g ∘ f) ∘ (f⁻¹ ∘ g⁻¹) ∼ id)
      h1 x = begin
        g (f (f⁻¹ (g⁻¹ x))) ≡⟨ ap g (pf (g⁻¹ x)) ⟩
        g (g⁻¹ x) ≡⟨ pg x ⟩
        x ∎
      h2 : ((f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) ∼ id)
      h2 x = begin
        f⁻¹ (g⁻¹ (g (f x))) ≡⟨ ap f⁻¹ (qg (f x)) ⟩
        f⁻¹ (f x) ≡⟨ qf x ⟩
        x ∎
  in  invs-are-equivs (g ∘ f) ((f⁻¹ ∘ g⁻¹) , h1 , h2)

≃-trans : {A : 𝒰 𝒾} {B : 𝒰 𝒿} {C : 𝒰 𝓀}
        → A ≃ B → B ≃ C → A ≃ C
≃-trans eqvf@( f , ef ) eqvg@( g , eg ) =
  let ( f⁻¹ , pf , qf ) = ( equivs-are-invs f ef )
      ( g⁻¹ , pg , qg ) = ( equivs-are-invs g eg )
      h1 : ((g ∘ f) ∘ (f⁻¹ ∘ g⁻¹) ∼ id)
      h1 x = begin
        g (f (f⁻¹ (g⁻¹ x))) ≡⟨ ap g (pf (g⁻¹ x)) ⟩
        g (g⁻¹ x)           ≡⟨ pg x ⟩
        x ∎
      h2 : ((f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) ∼ id)
      h2 x = begin
        f⁻¹ (g⁻¹ (g (f x))) ≡⟨ ap f⁻¹ (qg (f x)) ⟩
        f⁻¹ (f x)           ≡⟨ qf x ⟩
        x ∎
  in  ((g ∘ f) , ≃-trans-helper eqvf eqvg)

-- Proposición 3.5.10
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

-- Proposición 3.5.11
paths-over-≃ : {A : 𝒰 𝒾} (P : A → 𝒰 𝒿)
       (x y : A) (p : x ≡ y)
       (u : P x) (v : P y)
     → (Σ q ꞉ ((x , u) ≡ (y , v)) , (ap pr₁ q ≡ p)) ≃ (tr P p u ≡ v)
paths-over-≃ P x y p u v = f p , invs-are-equivs (f p) (g p , ε p , η)
  where
    f : (p : x ≡ y) → (Σ q ꞉ (x , u ≡ y , v) , ap pr₁ q ≡ p) → tr P p u ≡ v
    f p (refl (x , u) , refl p) = refl u
    g : (p : x ≡ y) → tr P p u ≡ v → Σ q ꞉ (x , u ≡ y , v) , ap pr₁ q ≡ p
    g p (refl v) = (lift u p) , lift-lemma u p
    ε : (p : x ≡ y) → (s : tr P p u ≡ v) → f p (g p s) ≡ s
    ε (refl u) (refl v) = refl _
    η : (α : (Σ q ꞉ (x , u ≡ y , v) , ap pr₁ q ≡ p)) → g p (f p α) ≡ α
    η (refl _ , refl _) = refl _
```

## Sección 3.6. Caminos entre pares dependientes

```agda

-- Teorema 3.6.1.
pair⁼⁻¹ : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} {w w' : Σ Y}
        → (w ≡ w') → (Σ p ꞉ (pr₁ w ≡ pr₁ w') , tr Y p (pr₂ w) ≡ (pr₂ w'))
pair⁼⁻¹ (refl w) = ( refl (pr₁ w) , refl (pr₂ w) )

pair⁼ : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} {w w' : Σ Y}
        → (Σ p ꞉ (pr₁ w ≡ pr₁ w') , tr Y p (pr₂ w) ≡ (pr₂ w')) → (w ≡ w')
pair⁼ {𝒾} {𝒿} {X} {Y} {w1 , w2} {w'1 , w'2} (refl w1 , refl w2) = refl (w1 , w2)

Σ-≡-≃ : {X : 𝒰 𝒾} {Y : X → 𝒰 𝒿} {w w' : Σ Y}
      → (w ≡ w') ≃ (Σ p ꞉ (pr₁ w ≡ pr₁ w') , tr Y p (pr₂ w) ≡ (pr₂ w'))
Σ-≡-≃ {𝒾} {𝒿} {X} {Y} {w1 , w2} {w'1 , w'2} =
  pair⁼⁻¹ , invs-are-equivs pair⁼⁻¹ (pair⁼ , α , β)
    where
      α : (pq : (Σ p ꞉ w1 ≡ w'1 , tr Y p w2 ≡ w'2))
        → pair⁼⁻¹ (pair⁼ pq) ≡ pq
      α (refl w1 , refl w2) = refl (refl w1 , refl w2)
      β : (p : (w1 , w2 ≡ w'1 , w'2))
        → pair⁼ (pair⁼⁻¹ p) ≡ p
      β (refl (w1 , w2)) = refl (refl (w1 , w2))

-- Corolario 3.6.2.
Σ-uniq : {X : 𝒰 𝒾} {P : X → 𝒰 𝒿} (z : Σ P)
       → z ≡ (pr₁ z , pr₂ z)
Σ-uniq z = pair⁼ (refl _ , refl _)

-- Corolario 3.6.2.
pair×⁼⁻¹ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {w w' : X × Y}
         → (w ≡ w') → ((pr₁ w ≡ pr₁ w') × (pr₂ w ≡ pr₂ w'))
pair×⁼⁻¹ (refl w) = ( refl (pr₁ w) , refl (pr₂ w) )

pair×⁼ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {w w' : X × Y}
       → ((pr₁ w ≡ pr₁ w') × (pr₂ w ≡ pr₂ w')) → (w ≡ w')
pair×⁼ {𝒾} {𝒿} {X} {Y} {w1 , w2} {w'1 , w'2} (refl w1 , refl w2) = refl (w1 , w2)

×-≡-≃ : {X : 𝒰 𝒾} {Y : 𝒰 𝒿} {w w' : X × Y}
      → (w ≡ w') ≃ ((pr₁ w ≡ pr₁ w') × (pr₂ w ≡ pr₂ w'))
×-≡-≃ {𝒾} {𝒿} {X} {Y} {w1 , w2} {w'1 , w'2} =
  pair×⁼⁻¹ , invs-are-equivs pair×⁼⁻¹ (pair×⁼ , α , β)
    where
      α : (pq : (w1 ≡ w'1) × (w2 ≡ w'2))
        → pair×⁼⁻¹ (pair×⁼ pq) ≡ pq
      α (refl w1 , refl w2) = refl (refl w1 , refl w2)
      β : (p : (w1 , w2 ≡ w'1 , w'2))
        → pair×⁼ (pair×⁼⁻¹ p) ≡ p
      β (refl (w1 , w2)) = refl (refl (w1 , w2))
```

# Sección 3.7. Caminos entre funciones dependientes

```agda

happly : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} {f g : (x : A) → B x}
       → f ≡ g → f ∼ g
happly p x = ap (λ - → - x) p

-- Axioma 3.7.1.
has-funext : (𝒾 𝒿 : Level) → 𝒰 ((𝒾 ⊔ 𝒿)⁺)
has-funext 𝒾 𝒿 = {A : 𝒰 𝒾} {B : A → 𝒰 𝒿} (f g : (x : A) → B x)
               → isequiv (happly {𝒾} {𝒿} {A} {B} {f} {g})

postulate fe-ax : {𝒾 𝒿 : Level} → has-funext 𝒾 𝒿

qinv-fe : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿}
          (f g : (x : A) → B x) → qinv happly
qinv-fe f g = equivs-are-invs happly (fe-ax f g)

funext : {A : 𝒰 𝒾} {B : A → 𝒰 𝒿}
       → {f g : (x : A) → B x}
       → f ∼ g → f ≡ g
funext {f} {g} htpy =
  let (funext , η , ε ) = qinv-fe _ _
   in funext htpy

-- Lema 3.7.3.
PathOver-→ : {X : 𝒰 𝒾}
             {A B : X → 𝒰 𝓀}
             {x₁ x₂ : X} {p : x₁ ≡ x₂}
             {f : A x₁ → B x₁}
             {y : A x₂}
           → tr (λ (x : X) → (A x → B x)) p f y
               ≡ tr B p (f (tr A (p ⁻¹) y))
PathOver-→ {A} {B} {p = refl _} = refl _

-- Lema 3.7.4
PathOver-Π : {X : 𝒰 𝒾}
              {A : X → 𝒰 𝓀}
              {B : (x : X) → A x → 𝒰 𝒿}
              {x₁ x₂ : X} {p : x₁ ≡ x₂}
              {f : (y : A x₁) → B x₁ y}
              {g : (y : A x₂) → B x₂ y}
            → ({a₁ : A x₁} {a₂ : A x₂} (q : tr A p a₁ ≡ a₂)
                → tr (λ (w : Σ A) → B (pr₁ w) (pr₂ w)) (pair⁼(p , q)) (f a₁) ≡ (g a₂))
            → (tr (λ (x : X) → ((a : A x) → B x a)) p f) ≡ g
PathOver-Π {A = A} {B} {p = refl _} {f = f} {g = g} lem
  = funext (λ - → lem (refl -))
```

# Sección 3.8. Caminos entre tipos

```agda

-- Lema 3.8.1.
idtoeqv-helper : {X Y : 𝒰 𝒾} (p : X ≡ Y) → isequiv (tr (λ C → C) p)
idtoeqv-helper (refl X) = invs-are-equivs (𝑖𝑑 X) (qinv-id-id X)

idtoeqv : {X Y : 𝒰 𝒾} → X ≡ Y → X ≃ Y
idtoeqv {𝒾} {X} {Y} p = tr (λ C → C) p , (idtoeqv-helper p)

-- Axioma 3.8.2.
is-univalent : (𝒾 : Level) → 𝒰 (𝒾 ⁺)
is-univalent 𝒾 = (X Y : 𝒰 𝒾) → isequiv (idtoeqv {𝒾} {X} {Y})

postulate ua-ax : {𝒾 : Level} → is-univalent 𝒾

qinv-ua : (X Y : 𝒰 𝒾) → qinv idtoeqv
qinv-ua X Y = equivs-are-invs idtoeqv (ua-ax X Y)

ua : {X Y : 𝒰 𝒾} → X ≃ Y → X ≡ Y
ua eqv =
  let (ua , idtoeqv∘ua , ua∘idtoeqv) = qinv-ua _ _
   in ua eqv

-- Helper
id∼idtoeqv∘ua : {X Y : 𝒰 𝒾} (eqv : X ≃ Y)
              → eqv ≡ idtoeqv (ua eqv)
id∼idtoeqv∘ua {X} {Y} eqv =
  let (ua , idtoeqv∘ua , ua∘idtoeqv) = qinv-ua _ _
   in (idtoeqv∘ua eqv)⁻¹
```

# Sección 3.9. Caminos entre naturales

```agda

code-ℕ : ℕ → ℕ → 𝒰₀
code-ℕ 0 0               = 𝟙
code-ℕ (succ m) 0        = 𝟘
code-ℕ 0 (succ m)        = 𝟘
code-ℕ (succ m) (succ n) = code-ℕ m n

-- Teorema 3.9.1.
r-ℕ : (n : ℕ) → code-ℕ n n
r-ℕ 0        = ⋆
r-ℕ (succ n) = r-ℕ n

encode-ℕ : (m n : ℕ) → (m ≡ n) → code-ℕ m n
encode-ℕ m n p = tr (code-ℕ m) p (r-ℕ m)

decode-ℕ : (m n : ℕ) → code-ℕ m n → (m ≡ n)
decode-ℕ 0 0 f = refl 0
decode-ℕ (succ m) 0 f = !𝟘 (succ m ≡ 0) f
decode-ℕ 0 (succ n) f = !𝟘 (0 ≡ succ n) f
decode-ℕ (succ m) (succ n) f = ap succ (decode-ℕ m n f)

decode∘encode-ℕ∼id : (m n : ℕ) → (decode-ℕ m n) ∘ (encode-ℕ m n) ∼ id
decode∘encode-ℕ∼id m n (refl n) = lema n
  where
    lema : (n : ℕ) → decode-ℕ n n (r-ℕ n) ≡ refl n
    lema 0 = refl _
    lema (succ n) = ap (ap succ) (lema n)

encode∘decode-ℕ∼id : (m n : ℕ) → (encode-ℕ m n) ∘ (decode-ℕ m n) ∼ id
encode∘decode-ℕ∼id 0 0 ⋆               = refl ⋆
encode∘decode-ℕ∼id (succ m) 0 c        = !𝟘 _ c
encode∘decode-ℕ∼id 0 (succ n) c        = !𝟘 _ c
encode∘decode-ℕ∼id (succ m) (succ n) c = begin
  encode-ℕ (succ m) (succ n) (decode-ℕ (succ m) (succ n) c)           ≡⟨⟩
  encode-ℕ (succ m) (succ n) (ap succ (decode-ℕ m n c))               ≡⟨⟩
  tr (code-ℕ (succ m)) (ap succ (decode-ℕ m n c)) (r-ℕ (succ m))      ≡⟨ i ⟩
  tr (λ - → code-ℕ (succ m) (succ -)) (decode-ℕ m n c) (r-ℕ (succ m)) ≡⟨⟩
  tr (λ - → code-ℕ (succ m) (succ -)) (decode-ℕ m n c) (r-ℕ m)        ≡⟨⟩
  tr (code-ℕ m) (decode-ℕ m n c) (r-ℕ m)                              ≡⟨⟩
  encode-ℕ m n (decode-ℕ m n c)                                       ≡⟨ ii ⟩
  c ∎
 where
  i = happly (tr-f (code-ℕ (succ m)) succ ((decode-ℕ m n c))) (r-ℕ (succ m))
  ii = encode∘decode-ℕ∼id m n c

ℕ-≡-≃ : (m n : ℕ) → (m ≡ n) ≃ code-ℕ m n
ℕ-≡-≃ m n =
  encode-ℕ m n , invs-are-equivs (encode-ℕ m n)
    (decode-ℕ m n , encode∘decode-ℕ∼id m n , decode∘encode-ℕ∼id m n)

-- Corolario 3.9.2.
sm≡sn→m≡n : {m n : ℕ} → (succ m ≡ succ n) → (m ≡ n)
sm≡sn→m≡n {m} {n} p = decode-ℕ m n (encode-ℕ (succ m) (succ n) p)

-- Corolario 3.9.3.
ℕ-decidable : (m n : ℕ) → (m ≡ n) ⊎ ((m ≡ n) → 𝟘)
ℕ-decidable 0 0               = inl (refl 0)
ℕ-decidable (succ m) 0        = inr (λ - → !𝟘 _ (encode-ℕ (succ m) 0 -))
ℕ-decidable 0 (succ n)        = inr (λ - → !𝟘 _ (encode-ℕ 0 (succ n) -))
ℕ-decidable (succ m) (succ n) =
  ⊎-ind ((λ - → (succ m ≡ succ n) ⊎ (succ m ≡ succ n → 𝟘)))
    (λ p → inl(ap succ p))
    (λ contra → inr(λ p → contra (sm≡sn→m≡n p)))
    (ℕ-decidable m n)
```
