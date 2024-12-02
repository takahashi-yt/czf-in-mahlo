{-# OPTIONS --cubical-compatible --safe #-}

module CZFBasics where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Preliminaries

{-
   This file formalises Aczel's interpretation of constructive set theory CZF in MLTT [1,2,3]:

   [1] Peter Aczel. The type theoretic interpretation of constructive set theory. In Angus Macintyre,
       Leszek Pacholski, and Jeff Paris, editors, Logic Colloquium '77, volume 96 of Studies in Logic and
       the Foundations of Mathematics, pages 55--66. Elsevier, 1978.

   [2] Peter Aczel. The type theoretic interpretation of constructive set theory: Choice principles. In
       A. S. Troelstra and D. van Dalen, editors, The L.E.J. Brouwer Centenary Symposium, pages 1--40.
       North-Holland, 1982.

   [3] Peter Aczel. The type theoretic interpretation of constructive set theory: Inductive definitions.
       In R. B. Marcus, G. J. Dorn, and G. J. W. Dorn, editors, Logic, Methodology, and Philosophy of
       Science VII, pages 17--49. North-Holland, 1986.
-}


-- the type of iterative sets

𝕍 : Set₁
𝕍 = W Set λ A → A

∀𝕧∈ : {ℓ : Level} → 𝕍 → (𝕍 → Set ℓ) → Set ℓ
∀𝕧∈ a B = ∀ (x : index a) → B (pred a x)

∃𝕧∈ : {ℓ : Level} → 𝕍 → (𝕍 → Set ℓ) → Set ℓ
∃𝕧∈ a B = Σ (index a) (λ x → B (pred a x))


-- a transfinite induction principle on 𝕍 which is weaker than ∈-TI below

∈-wTI : {ℓ : Level} {F : 𝕍 → Set ℓ} →
         (∀ (a : 𝕍) → (∀𝕧∈ a F → F a)) → ∀ (a : 𝕍) → F a
∈-wTI e (sup A f) = e (sup A f) λ x → ∈-wTI e (f x)


-- the equality on 𝕍

_≐_ : 𝕍 → 𝕍 → Set
sup A f ≐ sup B g = ((x : A) → Σ B λ y → f x ≐ g y) ×
  ((y : B) → Σ A λ x → f x ≐ g y)

{- another definition of _≐_

_≐_ : 𝕍 → 𝕍 → Set
a ≐ b = Welim (λ v → 𝕍 → Set) (λ A z f → G A z (λ x → f x)) a b 
  where
  G₁ : (A : Set) → 𝕍 → (A → 𝕍 → Set) → Set
  G₁ A a w = (x : A) → ∃𝕧∈ a (w x)
  
  G₂ : (A : Set) → 𝕍 → (A → 𝕍 → Set) → Set
  G₂ A a w = ∀𝕧∈ a (λ y → Σ A (λ x → w x y))

  G : (A : Set) → (A → 𝕍) → (A → 𝕍 → Set) → (𝕍 → Set)
  G u _ w = λ v → (G₁ u v w) × (G₂ u v w)             -}


-- some properties of _≐_ 

ip-compat : {a b : 𝕍} → a ≐ b → (x : index a) → Σ (index b) λ y → pred a x ≐ pred b y
ip-compat {sup A f} {sup B g} p x = fst (fst p x) , snd (fst p x)

≐comp : (a b : 𝕍) → (a ≐ b) ≡
          ∀𝕧∈ a (λ x → ∃𝕧∈ b (λ y → x ≐ y)) × ∀𝕧∈ b (λ y → ∃𝕧∈ a (λ x → x ≐ y))
≐comp (sup A f) (sup B g) = refl

≐logeq : {a b : 𝕍} → (a ≐ b) ↔
          (∀𝕧∈ a (λ x → ∃𝕧∈ b (λ y → x ≐ y)) × ∀𝕧∈ b (λ y → ∃𝕧∈ a (λ x → x ≐ y)))
≐logeq {sup A f} {sup B g} = (λ c → c) , λ c → c


-- _≐_ is an equivalence relation 

≐refl : (a : 𝕍) → a ≐ a
≐refl (sup A f) = (λ x → (x , ≐refl (f x))) , (λ x → (x , ≐refl (f x)))

≐sym : (a b : 𝕍) → a ≐ b → b ≐ a
≐sym (sup A f) (sup B g) (c₁ , c₂) =
  (λ x → fst (c₂ x) , ≐sym (f (fst (c₂ x))) (g x) (snd (c₂ x))) ,
    (λ y → fst (c₁ y) , ≐sym (f y) (g (fst (c₁ y))) (snd (c₁ y)))

≐trans : (a b c : 𝕍) → a ≐ b → b ≐ c → a ≐ c
≐trans (sup A f) (sup B g) (sup C h) (c₁ , c₂) (d₁ , d₂) =
  (λ x → fst (d₁ (fst (c₁ x))) , ≐trans (f x) (g (fst (c₁ x))) (h (fst (d₁ (fst (c₁ x))))) (snd (c₁ x)) (snd (d₁ (fst (c₁ x))))) ,
    (λ z → fst (c₂ (fst (d₂ z))) , ≐trans (f (fst (c₂ (fst (d₂ z))))) (g (fst (d₂ z))) (h z) (snd (c₂ (fst (d₂ z)))) (snd (d₂ z)))

≐cong : {A : Set} {f g : A → 𝕍} → ((a : A) → f a ≐ g a) → sup A f ≐ sup A g
≐cong {A} {f} {g} p = (λ x → x , p x) , (λ y → y , p y)

-- "eta-equality" for _≐_

≐eta : (a : 𝕍) → a ≐ sup (index a) (pred a)
≐eta (sup A f) = (λ x → x , ≐refl (f x)) , (λ x → x , ≐refl (f x))

≐bisim : {v w : 𝕍} → v ≐ w →
            (∀𝕧∈ v λ x → ∃𝕧∈ w λ y → x ≐ y) × (∀𝕧∈ w λ y → ∃𝕧∈ v λ x → x ≐ y)
≐bisim {v = sup A f} {w = sup B g} p =
  (λ x → fst (fst p x) , snd (fst p x)) , λ y → fst (snd p y) , snd (snd p y)

-- a useful lemma relating ≡ and ≐

≡-≐ : {A B : Set} → (g : B → 𝕍) → (p : A ≡ B)
        → sup A (λ x → g (transp (λ X → X) p x)) ≐ sup B g
≡-≐ {A} {.A} g refl = ≐refl (sup A g)

-- a similar lemma not mentioning ≐

≡-≡ : {A B : Set} → (g : B → 𝕍) → (p : A ≡ B)
        → sup A (λ x → g (transp (λ X → X) p x)) ≡ sup B g
≡-≡ {A} {.A} g refl = refl


-- the membership relation on 𝕍

_∈_ : 𝕍 → 𝕍 → Set
a ∈ b = ∃𝕧∈ b (λ v → a ≐ v)

infix 25 _∈_


-- the subset relation on 𝕍

_⊆_ : 𝕍 → 𝕍 → Set
a ⊆ b = ∀𝕧∈ a (λ v → v ∈ b)

infix 25 _⊆_

⊆trans : {a b c : 𝕍} → a ⊆ b → b ⊆ c → a ⊆ c
⊆trans {a} {b} {c} d f x = fst (f (fst (d x))) ,
  ≐trans (pred a x) (pred b (fst (d x))) (pred c (fst (f (fst (d x)))))
    (snd (d x)) (snd (f (fst (d x))))

_⊆'_ : 𝕍 → 𝕍 → Set₁
a ⊆' b = (x : 𝕍) → x ∈ a → x ∈ b

infix 25 _⊆'_


-- transitive sets

isTransitive : 𝕍 → Set₁
isTransitive a = (b c : 𝕍) → b ∈ a → c ∈ b → c ∈ a


-- some properties of _∈_ 

≐transp : {a b x : 𝕍} → a ≐ b → a ∈ x → b ∈ x
≐transp {a}{b}{x} p (y , c) = y , ≐trans b a (pred x y) (≐sym a b p) c

≐ext : {a b : 𝕍} → a ≐ b → (x : 𝕍) → (x ∈ a ↔ x ∈ b)
≐ext {sup A f}{sup B g} p x =
  (λ (y , c₁) → fst (fst p y) , ≐trans x (f y) (g (fst (fst p y))) c₁ (snd (fst p y))) ,
    (λ (z , c₂) → fst (snd p z) ,
      ≐trans x (g z) (f (fst (snd p z))) c₂ (≐sym (f (fst (snd p z))) (g z) (snd (snd p z))))

≐ext' : {a b : 𝕍} → ((x : 𝕍) → (x ∈ a ↔ x ∈ b)) → a ≐ b
≐ext' {sup A f}{sup B g} h = (λ x → fst (h (f x)) (x , ≐refl (f x))) ,
  λ y → fst (snd (h (g y)) (y , ≐refl (g y))) ,
    ≐sym (g y) (f (fst (snd (h (g y)) (y , ≐refl (g y)))))
      (snd (snd (h (g y)) (y , ≐refl (g y))))

∈-isWF : (a b : 𝕍) → ((a ∈ b) × (b ∈ a)) → ⊥
∈-isWF (sup A f) (sup B g) (c , d) = ∈-isWF (f (fst d)) (g (fst c))
  (fst (≐ext (snd c) (f (fst d))) (≐transp (snd d) d) ,
    fst (≐ext (snd d) (g (fst c))) (≐transp (snd c) c))

≐-⊆ : {a b c : 𝕍} → a ≐ b → a ⊆ c → b ⊆ c
≐-⊆ {a}{b}{c} p e x = ≐transp {pred a (fst ≐-⊆-lem)}{pred b x}{c}
  (≐sym (pred b x) (pred a (fst ≐-⊆-lem)) (snd ≐-⊆-lem)) (e (fst ≐-⊆-lem))
  where
  ≐-⊆-lem : pred b x ∈ a
  ≐-⊆-lem = fst (≐ext (≐sym a b p) (pred b x)) (x , ≐refl (pred b x))
  

-- extensional properties

isExt : {ℓ : Level} → (𝕍 → Set ℓ) → Set (lsuc lzero ⊔ ℓ)
isExt F = (a : 𝕍) → F a → (b : 𝕍) → b ≐ a → F b

-- another formulation of extensional properties: invariant properties

isInv : {ℓ : Level} → (𝕍 → Set ℓ) → Set (lsuc lzero ⊔ ℓ)
isInv F = {a b : 𝕍} → a ≐ b → F a → F b


-- some lemmas on extensional properties

∀𝕧∈-Inv : {ℓ : Level} {F : 𝕍 → Set ℓ} → isInv F → isInv λ a → ∀𝕧∈ a (λ v → F v)
∀𝕧∈-Inv {F = F} F-is-inv {sup A f} {sup B g} p c y = F-is-inv (snd (snd p y)) (c (fst (snd p y)))

Trans-is-Ext : isExt λ a → isTransitive a
Trans-is-Ext = λ a a-trans b p v w v-in-b w-in-v →
  snd (≐ext p w) (a-trans v w (fst (≐ext p v) v-in-b) w-in-v) 

ExtAll : {ℓ : Level} {F : 𝕍 → Set} → isExt F → (a : 𝕍) →
           ∀𝕧∈ a F ↔ ((v : 𝕍) → v ∈ a → F v)
ExtAll {F = F} prf (sup A f) = (λ g v (x , y) → prf (f x) (g x) v y) , λ h x → h (f x) ((x , ≐refl (f x)))

ExtEx : {ℓ : Level} {F : 𝕍 → Set} → isExt F → (a : 𝕍) →
           ∃𝕧∈ a F ↔ (Σ 𝕍 (λ v → v ∈ a × F v))
ExtEx {F = F} prf (sup A f) = (λ (x , y) → f x , (x , ≐refl (f x)) , y) ,
                                λ (a , b) → fst (fst b) ,
                                  prf a (snd b) (f (fst (fst b))) (≐sym a (f (fst (fst b))) (snd (fst b)))


-- the transfinite induction principle for transitive sets

∈-TI : {ℓ : Level} {F : 𝕍 → Set ℓ} → isExt F →
         ((a : 𝕍) → isTransitive a → ((b : 𝕍) → isTransitive b → (b ∈ a → F b)) → F a) →
           (a : 𝕍) → isTransitive a → F a
∈-TI {ℓ}{F} F-ext e (sup A f) a-trans  = e (sup A f) a-trans λ b b-trans b-in-a →
  let F' : 𝕍 → Set ℓ
      F' = λ x → x ∈ sup A f → F x
        
      ∈-TI-lem₁ : isExt F'
      ∈-TI-lem₁ v₁ w₁ v₂ p d' = F-ext v₁ (w₁ (≐transp p d')) v₂ p 

      ∈-TI-lem₂ : ((v : 𝕍) → isTransitive v → ((w : 𝕍) → isTransitive w → (w ∈ v → F' w)) → F' v)
      ∈-TI-lem₂ v v-trans e₁ v-in-a = e v v-trans
        λ b b-trans b-in-v → e₁ b b-trans b-in-v (a-trans v b v-in-a b-in-v)

      ∈-TI-lem₃ : isTransitive (f (fst b-in-a))
      ∈-TI-lem₃ y z c z-in-y =
        Trans-is-Ext b b-trans (f (fst b-in-a)) (≐sym b (f (fst b-in-a)) (snd b-in-a)) y z c z-in-y
                    
      ∈-TI-lem₄ : F' (f (fst b-in-a))
      ∈-TI-lem₄ = ∈-TI ∈-TI-lem₁ ∈-TI-lem₂ (f (fst b-in-a)) ∈-TI-lem₃
  in F-ext (f (fst b-in-a)) (∈-TI-lem₄ (fst b-in-a , ≐refl (f (fst b-in-a)))) b (snd b-in-a)
