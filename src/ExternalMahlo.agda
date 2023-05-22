
module ExternalMahlo where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Preliminaries


{-
   Mahlo universe was introduced by Setzer [1], and this file formalises an external variant of Mahlo universe
   which was introduced by Dybjer and Setzer [2]

   the sort Set is considered as the external Mahlo universe in Russell universe-style, so it does not have any decoding function

   the fundamental property of Set as the external Mahlo universe is that for any function f on families of sets,
   there is a subuniverse 𝕌 which is closed under f

   the universe 𝕌 with the decoding function 𝕋 is defined by induction-recursion, and the closedness under f is expressed by
   the constructors code₁ and code₂

   [1] Anton Setzer. Extending Martin-Löf type theory by one Mahlo-universe. Arch. Math. Log., 39(3):155--181, 2000.

   [2] Peter Dybjer and Anton Setzer. Induction-recursion and initial algebras. Ann. Pure Appl. Log., 124(1-3):1--47, 2003.
-}

data 𝕌 (f : Σ Set (λ A → A → Set) → Σ Set (λ A → A → Set)) : Set
𝕋 : (f : Σ Set (λ A → A → Set) → Σ Set (λ A → A → Set)) → 𝕌 f → Set

data 𝕌 f where
  code₁ : Σ (𝕌 f) (λ a → 𝕋 f a → 𝕌 f) → 𝕌 f
  code₂ : (c : Σ (𝕌 f) (λ a → 𝕋 f a → 𝕌 f)) → 𝕋 f (code₁ c) → 𝕌 f
  code⊥ : 𝕌 f
  code⊤ : 𝕌 f
  codeB : 𝕌 f
  codeN : 𝕌 f
  codeS : 𝕌 f → 𝕌 f → 𝕌 f
  codeE : (x : 𝕌 f) → (a b : 𝕋 f x) → 𝕌 f
  codeΠ : (a : 𝕌 f) → (b : 𝕋 f a → 𝕌 f) → 𝕌 f
  codeΣ : (a : 𝕌 f) → (b : 𝕋 f a → 𝕌 f) → 𝕌 f
  codeW : (a : 𝕌 f) → (b : 𝕋 f a → 𝕌 f) → 𝕌 f

𝕋 f (code₁ c) = fst (f (𝕋 f (fst c) , λ x → 𝕋 f (snd c x)))
𝕋 f (code₂ c d) = snd (f (𝕋 f (fst c) , λ x → 𝕋 f (snd c x))) d
𝕋 f code⊥ = ⊥
𝕋 f code⊤ = ⊤
𝕋 f codeB = Bool
𝕋 f codeN = Nat
𝕋 f (codeS a b) = (𝕋 f a) ⊕ (𝕋 f b)
𝕋 f (codeE x a b) = a ≡ b
𝕋 f (codeΠ a b) = (x : 𝕋 f a) → 𝕋 f (b x)
𝕋 f (codeΣ a b) = Σ (𝕋 f a) (λ x → 𝕋 f (b x))
𝕋 f (codeW a b) = W (𝕋 f a) (λ x → 𝕋 f (b x))


-- injection function

ι : {f : Σ Set (λ A → A → Set) → Σ Set (λ A → A → Set)} →
    Σ (𝕌 f) (λ x → 𝕋 f x → 𝕌 f) → Σ Set (λ A → A → Set)
ι {f} (c₁ , c₂) = 𝕋 f c₁ , λ x → 𝕋 f (c₂ x)


{-
   𝕆 n is the type of operators of order n, in particular 𝕆 1 is the type of functions on families of sets
   
   𝔽 n is the type of families of n-order operators

   These notions are defined by Palmgren [3]

   [3] Erik Palmgren. On universes in type theory. In Giovanni Sambin and Jan M. Smith, editors,
       Twenty Five Years of Constructive Type Theory, Oxford Logic Guides, pages 191--204.
       Oxford University Press, 1998.
-}

interleaved mutual

  𝕆 : Nat → Set₁
  𝔽 : Nat → Set₁

  𝕆 0 = Set
  𝔽 n = Σ Set (λ A → A → 𝕆 n)

  𝕆 (suc n) = 𝔽 n → 𝔽 n


{-
   the operator u𝕄 provides a subuniverse closed under all first-order operators
   in a given family of first-order operator (A , f)  (cf. the cases (i) and (ii))
-}

u𝕄 : 𝔽 1 → 𝕆 1
u𝕄 (A , f) (B , g) = Uni¹₀
  where
  famSets : (c : 𝔽 0) → ((⊤ ⊕ B) ⊕ A) ⊕ (Σ A (λ e → fst (f e c))) → Set
  famSets c (injl (injl (injl x₁))) = B
  famSets c (injl (injl (injr x₂))) = g x₂
  famSets c (injl (injr e)) = fst (f e c)    -- (i)
  famSets c (injr (e , y)) = snd (f e c) y   -- (ii)

  uni¹₀ : Set
  uni¹₀ = 𝕌 (λ c → ((⊤ ⊕ B) ⊕ A) ⊕ (Σ A (λ e → fst (f e c))) , famSets c)

  dec¹₀ : uni¹₀ → Set
  dec¹₀ = 𝕋 (λ c → ((⊤ ⊕ B) ⊕ A) ⊕ (Σ A (λ e → fst (f e c))) , famSets c)

  Uni¹₀ : 𝔽 0
  Uni¹₀ = uni¹₀ , dec¹₀
