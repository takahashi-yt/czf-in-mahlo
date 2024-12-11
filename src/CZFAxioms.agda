{-# OPTIONS --cubical-compatible --safe #-}

module CZFAxioms where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Preliminaries
open import CZFBasics

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

   Moreover, we prove Fullness Axiom and Exponentiation Axiom, following the proof in

   Michael Rathjen, Edward R. Griffor, and Erik Palmgren. Inaccessibility in constructive set theory
   and type theory. Ann. Pure Appl. Log., 94(1-3):181--200, 1998.
-}


-- Extensionality Axioms

ExtAx1 : {a b x : 𝕍} → a ≐ b → a ∈ x → b ∈ x
ExtAx1 {a}{b}{x} = ≐transp {a}{b}{x}

ExtAx2 : {a b : 𝕍} → a ≐ b → (x : 𝕍) → (x ∈ a ↔ x ∈ b)
ExtAx2 = ≐ext

ExtAx2' : {a b : 𝕍} → ((x : 𝕍) → (x ∈ a ↔ x ∈ b)) → a ≐ b
ExtAx2' = ≐ext'

_⊧ExtAx : 𝕍 → Set
c ⊧ExtAx = (∀𝕧∈ c λ a → ∀𝕧∈ c λ b → ∀𝕧∈ c λ x → a ≐ b → a ∈ x → b ∈ x) ×
           (∀𝕧∈ c λ a → ∀𝕧∈ c λ b → a ≐ b → ∀𝕧∈ c λ x → (x ∈ a ↔ x ∈ b)) ×
           ∀𝕧∈ c λ a → ∀𝕧∈ c λ b → (∀𝕧∈ c λ x → (x ∈ a ↔ x ∈ b)) → a ≐ b


-- Set Induction Axiom as ∈-wTI

SetInd : {ℓ : Level} {F : 𝕍 → Set ℓ} → ((a : 𝕍) → ∀𝕧∈ a F → F a) → (a : 𝕍) → F a
SetInd = ∈-wTI

-- the relativisation of transfinite induction

_⊧SetInd : 𝕍 → Set₁
c ⊧SetInd = {F : 𝕍 → Set} → isInv F → (∀𝕧∈ c λ a → (∀𝕧∈ a λ v → F v) → F a) → ∀𝕧∈ c λ a → F a

-- _⊧SetInd is invariant

⊧SetIndInv : isInv (λ v → v ⊧SetInd)
⊧SetIndInv {sup A f} {sup B g} p c {F} F-is-inv e y = F-is-inv (snd (snd p y))
  (c F-is-inv (λ x e' → ⊧SetIndInv-lem x e') (fst (snd p y)))
  where
  ⊧SetIndInv-lem : ∀𝕧∈ (sup A f) (λ a → ∀𝕧∈ a F → F a)
  ⊧SetIndInv-lem z u = F-is-inv (≐sym (f z) (g (fst (fst p z))) (snd (fst p z)))
    (e (fst (fst p z)) (∀𝕧∈-Inv F-is-inv (snd (fst p z)) u))


-- Pairing Axiom with some notions and lemmas concerning the axiom

Pairs : (a b : 𝕍) → Σ 𝕍 (λ c → (x : 𝕍) → x ∈ c ↔ ((x ≐ a) ⊕ (x ≐ b)))
Pairs a b = sup Bool pair , λ x → (λ (z , e) → pair-prf₁ x z e) , pair-prf₂ x
  where
  pair : Bool → 𝕍
  pair false = a
  pair true = b

  pair-prf₁ : (x : 𝕍) (y : Bool) → (x ≐ pair y) → ((x ≐ a) ⊕ (x ≐ b))
  pair-prf₁ x false d = injl d
  pair-prf₁ x true  d = injr d

  pair-prf₂ : (x : 𝕍) → (x ≐ a) ⊕ (x ≐ b) → x ∈ sup Bool pair
  pair-prf₂ x (injl w) = false , w
  pair-prf₂ x (injr w) = true , w

-- pair-set a b corresponds to {a , b}

pair-set : 𝕍 → 𝕍 → 𝕍
pair-set a b = fst (AC λ (a , b) → Pairs a b) (a , b)

pair-set-proof : (a b x : 𝕍) → x ∈ pair-set a b ↔ ((x ≐ a) ⊕ (x ≐ b))
pair-set-proof a b = snd (AC λ (a , b) → Pairs a b) (a , b)

pair-set-fst : (a b : 𝕍) → a ∈ pair-set a b
pair-set-fst a b = snd (pair-set-proof a b a) (injl (≐refl a))

pair-set-snd : (a b : 𝕍) → b ∈ pair-set a b
pair-set-snd a b = snd (pair-set-proof a b b) (injr (≐refl b))

pair-compat₁ : {a b : 𝕍} → a ≐ b → (c : 𝕍) → pair-set a c ≐ pair-set b c
pair-compat₁ {a}{b} p c = ≐ext' λ v → (λ d → lem₁-pair-compat₁ v (fst (pair-set-proof a c v) d)) ,
  (λ d → lem₂-pair-compat₁ v (fst (pair-set-proof b c v) d) )
  where
  lem₁-pair-compat₁ : (v : 𝕍) → (v ≐ a) ⊕ (v ≐ c) → v ∈ pair-set b c
  lem₁-pair-compat₁ v (injl q) = snd (pair-set-proof b c v) (injl (≐trans v a b q p))
  lem₁-pair-compat₁ v (injr r) = snd (pair-set-proof b c v) (injr r)

  lem₂-pair-compat₁ : (v : 𝕍) → (v ≐ b) ⊕ (v ≐ c) → v ∈ pair-set a c
  lem₂-pair-compat₁ v (injl q) = snd (pair-set-proof a c v) (injl (≐trans v b a q (≐sym a b p)))
  lem₂-pair-compat₁ v (injr r) = snd (pair-set-proof a c v) (injr r)

pair-compat₂ : {a b : 𝕍} → a ≐ b → (c : 𝕍) → pair-set c a ≐ pair-set c b
pair-compat₂ {a}{b} p c = ≐ext' λ v → (λ d → lem₁-pair-compat₂ v (fst (pair-set-proof c a v) d)) ,
  (λ d → lem₂-pair-compat₂ v (fst (pair-set-proof c b v) d) )
  where
  lem₁-pair-compat₂ : (v : 𝕍) → (v ≐ c) ⊕ (v ≐ a) → v ∈ pair-set c b
  lem₁-pair-compat₂ v (injl q) = snd (pair-set-proof c b v) (injl q)
  lem₁-pair-compat₂ v (injr r) = snd (pair-set-proof c b v) (injr (≐trans v a b r p))

  lem₂-pair-compat₂ : (v : 𝕍) → (v ≐ c) ⊕ (v ≐ b) → v ∈ pair-set c a
  lem₂-pair-compat₂ v (injl q) = snd (pair-set-proof c a v) (injl q)
  lem₂-pair-compat₂ v (injr r) = snd (pair-set-proof c a v) (injr (≐trans v b a r (≐sym a b p)))

_⊧Pairs : 𝕍 → Set
w ⊧Pairs = ∀𝕧∈ w λ a → ∀𝕧∈ w λ b → ∃𝕧∈ w λ c → ∀𝕧∈ w λ x → x ∈ c ↔ ((x ≐ a) ⊕ (x ≐ b))

inv-Pairs : isInv λ v → v ⊧Pairs
inv-Pairs {v}{w} p e x y = fst In-w , λ z → lem₁ z , lem₂ z
  where
  x' : index v
  x' = fst (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  xx' : pred w x ≐ pred v x'
  xx' = snd (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  y' : index v
  y' = fst (snd (≐ext p (pred w y)) (y , ≐refl (pred w y)))

  yy' : pred w y ≐ pred v y'
  yy' = snd (snd (≐ext p (pred w y)) (y , ≐refl (pred w y)))

  pair-in-v : ∃𝕧∈ v λ c → ∀𝕧∈ v λ z → (z ∈ c) ↔ ((z ≐ pred v x') ⊕ (z ≐ pred v y'))
  pair-in-v = e x' y'

  In-w : pred v (fst pair-in-v) ∈ w
  In-w = fst (≐ext p (pred v (fst pair-in-v))) (fst pair-in-v , ≐refl (pred v (fst pair-in-v)))

  inw≐inv : pred w (fst In-w) ≐ pred v (fst pair-in-v)
  inw≐inv = ≐sym (pred v (fst pair-in-v)) (pred w (fst In-w)) (snd In-w)

  lem₁ : ∀𝕧∈ w λ z → z ∈ pred w (fst In-w) → (z ≐ pred w x) ⊕ (z ≐ pred w y)
  lem₁ z d = ⊕elim (λ _ → (pred w z ≐ pred w x) ⊕ (pred w z ≐ pred w y))
                   (λ q₁ → injl (≐trans (pred w z)
                                       (pred v x')
                                       (pred w x)
                                       (≐trans (pred w z)
                                               (pred v (fst (ip-compat (≐sym v w p) z)))
                                               (pred v x')
                                               (snd (ip-compat (≐sym v w p) z))
                                               q₁)
                                       (≐sym (pred w x) (pred v x') xx')))
                   (λ q₂ → injr (≐trans (pred w z)
                                       (pred v y')
                                       (pred w y)
                                       (≐trans (pred w z)
                                               (pred v (fst (ip-compat (≐sym v w p) z)))
                                               (pred v y')
                                               ((snd (ip-compat (≐sym v w p) z)))
                                               q₂)
                                       (≐sym (pred w y) (pred v y') yy')))
                   (fst (snd pair-in-v (fst (ip-compat (≐sym v w p) z)))
                        (fst (fst (≐ext inw≐inv (pred w z)) d) ,
                        ≐trans (pred v (fst (ip-compat (≐sym v w p) z)))
                               (pred w z)
                               (pred (pred v (fst pair-in-v))
                                     (fst (fst (≐ext inw≐inv (pred w z)) d)))
                               (≐sym (pred w z)
                                     (pred v (fst (ip-compat (≐sym v w p) z)))
                                     (snd (ip-compat (≐sym v w p) z)))
                               (snd (fst (≐ext inw≐inv (pred w z)) d))))

  lem₂ : ∀𝕧∈ w λ z → (z ≐ pred w x) ⊕ (z ≐ pred w y) → z ∈ pred w (fst In-w)
  lem₂ z (injl q₁) = let sublem : pred v (fst (ip-compat (≐sym v w p) z)) ∈ pred w (fst In-w)
                         sublem = fst (≐ext (≐sym (pred w (fst In-w)) (pred v (fst pair-in-v)) inw≐inv)
                                            (pred v (fst (ip-compat (≐sym v w p) z))))
                                        (snd (snd pair-in-v (fst (ip-compat (≐sym v w p) z)))
                                               (injl (≐trans (pred v (fst (ip-compat (≐sym v w p) z)))
                                                             (pred w z)
                                                             (pred v x')
                                                             (≐sym (pred w z)
                                                                   (pred v (fst (ip-compat (≐sym v w p) z)))
                                                                   (snd (ip-compat (≐sym v w p) z)))
                                                             (≐trans (pred w z) (pred w x) (pred v x') q₁ xx'))))
                     in fst sublem ,
                        ≐trans (pred w z)
                                (pred v (fst (ip-compat (≐sym v w p) z)))
                                (pred (pred w (fst In-w)) (fst sublem))
                                (snd (ip-compat (≐sym v w p) z))
                                (snd sublem)
  lem₂ z (injr q₂) = let sublem : pred v (fst (ip-compat (≐sym v w p) z)) ∈ pred w (fst In-w)
                         sublem = fst (≐ext (≐sym (pred w (fst In-w)) (pred v (fst pair-in-v)) inw≐inv)
                                            (pred v (fst (ip-compat (≐sym v w p) z))))
                                        (snd (snd pair-in-v (fst (ip-compat (≐sym v w p) z)))
                                               (injr (≐trans (pred v (fst (ip-compat (≐sym v w p) z)))
                                                             (pred w z)
                                                             (pred v y')
                                                             (≐sym (pred w z)
                                                                   (pred v (fst (ip-compat (≐sym v w p) z)))
                                                                   (snd (ip-compat (≐sym v w p) z)))
                                                             (≐trans (pred w z) (pred w y) (pred v y') q₂ yy'))))
                      in fst sublem ,
                         ≐trans (pred w z)
                                (pred v (fst (ip-compat (≐sym v w p) z)))
                                (pred (pred w (fst In-w)) (fst sublem))
                                (snd (ip-compat (≐sym v w p) z))
                                (snd sublem)

-- sglt a corresponds to { a }

sglt : 𝕍 → 𝕍
sglt a = sup ⊤ λ _ → a

-- ordered pairs

⟨_,_⟩ : 𝕍 → 𝕍 → 𝕍
⟨ a , b ⟩ = pair-set (sglt a) (pair-set a b)

-- some lemmas for a proof of the ordered pair axiom

lemOPairAx₁ : {a b : 𝕍} → sglt a ≐ sglt b → a ≐ b
lemOPairAx₁ {a}{b} p = snd (fst (≐ext p a) (tt , ≐refl a))

lemOPairAx₂ : {a b c : 𝕍} → (a ≐ b → ⊥) ⊕ (a ≐ c → ⊥) → sglt a ≐ pair-set b c → ⊥
lemOPairAx₂ {a} {b} {c} (injl f) p =
  f (≐sym b a (snd (snd (≐ext p b) (pair-set-fst b c))))
lemOPairAx₂ {a} {b} {c} (injr g) p =
  g (≐sym c a (snd (snd (≐ext p c) (pair-set-snd b c))))

lemOPairAx₃ : {a b v w : 𝕍} → (⟨ a , v ⟩ ≐ ⟨ b , w ⟩) → a ≐ b
lemOPairAx₃ {a}{b}{v}{w} p =
  sublem₃ ((fst (pair-set-proof (sglt b) (pair-set b w) (sglt a))) sublem₁)
  where
  sublem₁ : sglt a ∈ pair-set (sglt b) (pair-set b w)
  sublem₁ = fst (≐ext p (sglt a))
              (pair-set-fst (sglt a) (pair-set a v))

  sublem₂ : sglt a ≐ pair-set b w → a ≐ b
  sublem₂ q = ≐sym b a (snd (snd (≐ext q b) (pair-set-fst b w)))

  sublem₃ : (sglt a ≐ sglt b) ⊕ (sglt a ≐ pair-set b w) → a ≐ b
  sublem₃ (injl p) = lemOPairAx₁ p
  sublem₃ (injr q) = sublem₂ q

lemOPairAx₄ : {a v w : 𝕍} → pair-set a v ≐ pair-set a w → v ≐ w
lemOPairAx₄ {a}{v}{w} p = sublem₃ (fst (pair-set-proof a w v) sublem₁ ,
                                     fst (pair-set-proof a v w) sublem₂)
  where
  sublem₁ : v ∈ pair-set a w
  sublem₁ = fst (≐ext p v) (pair-set-snd a v)

  sublem₂ : w ∈ pair-set a v
  sublem₂ = snd (≐ext p w) (pair-set-snd a w)

  sublem₃ : ((v ≐ a) ⊕ (v ≐ w)) × ((w ≐ a) ⊕ (w ≐ v)) → v ≐ w
  sublem₃ (injl p₁ , injl q₁) = ≐trans v a w p₁ (≐sym w a q₁)
  sublem₃ (injl p₁ , injr r₁) = ≐sym w v r₁
  sublem₃ (injr p₂ , c) = p₂

lemOPairAx₅ : {a b c : 𝕍} → sglt a ≐ pair-set b c → (a ≐ b) × (a ≐ c)
lemOPairAx₅ {a}{b}{c} p =
  ≐sym b a (snd (snd (≐ext p b) (pair-set-fst b c))) ,
    ≐sym c a (snd (snd (≐ext p c) (pair-set-snd b c)))

lemOPairAx₆ : {a b v w : 𝕍} → (⟨ a , v ⟩ ≐ ⟨ b , w ⟩) → v ≐ w
lemOPairAx₆ {a}{b}{v}{w} p = sublem₃ (sublem₁ , sublem₂)
  where
  sublem₁ : (pair-set a v ≐ sglt b) ⊕ (pair-set a v ≐ pair-set b w)
  sublem₁ = fst (pair-set-proof (sglt b) (pair-set b w) (pair-set a v))
    (fst (≐ext p (pair-set a v)) (pair-set-snd (sglt a) (pair-set a v)))

  sublem₂ : (pair-set b w ≐ sglt a) ⊕ (pair-set b w ≐ pair-set a v)
  sublem₂ = fst (pair-set-proof (sglt a) (pair-set a v) (pair-set b w))
    (snd (≐ext p (pair-set b w)) (pair-set-snd (sglt b) (pair-set b w)))

  sublem₃ : ((pair-set a v ≐ sglt b) ⊕ (pair-set a v ≐ pair-set b w)) ×
              ((pair-set b w ≐ sglt a) ⊕ (pair-set b w ≐ pair-set a v)) → v ≐ w
  sublem₃ (injl q₁ , injl r₁) = ≐trans v b w
    (≐sym b v (snd (lemOPairAx₅ (≐sym (pair-set a v) (sglt b) q₁))))
      (≐trans b a w (≐sym a b (lemOPairAx₃ p)) (snd (lemOPairAx₅ (≐sym (pair-set b w) (sglt a) r₁))))
  sublem₃ (injl q₁ , injr r₂) = lemOPairAx₄ (≐trans (pair-set a v) (pair-set b w) (pair-set a w)
    (≐sym (pair-set b w) (pair-set a v) r₂) (pair-compat₁ (≐sym a b (lemOPairAx₃ p)) w))
  sublem₃ (injr q₂ , s) = lemOPairAx₄ (≐trans (pair-set a v) (pair-set b w) (pair-set a w)
    q₂ (pair-compat₁ (≐sym a b (lemOPairAx₃ p)) w))

lemOPairAx₇ : {a b v w : 𝕍} → ((a ≐ b) × (v ≐ w)) → (⟨ a , v ⟩ ≐ ⟨ b , w ⟩)
lemOPairAx₇ {a}{b}{v}{w} (p , q) = ≐trans ⟨ a , v ⟩ (pair-set (sglt b) (pair-set a v)) ⟨ b , w ⟩
  (pair-compat₁ sublem₂ (pair-set a v)) (pair-compat₂ sublem₁ (sglt b))
  where
  sublem₁ : pair-set a v ≐ pair-set b w
  sublem₁ = ≐trans (pair-set a v) (pair-set b v) (pair-set b w) (pair-compat₁ p v) (pair-compat₂ q b)

  sublem₂ : sglt a ≐ sglt b
  sublem₂ = (λ _ → tt , p) , λ _ → tt , p

-- a proof for the axiom of ordered pairs

OPairAx : {a b v w : 𝕍} → (⟨ a , v ⟩ ≐ ⟨ b , w ⟩) ↔ ((a ≐ b) × (v ≐ w))
OPairAx {a}{b}{v}{w} = (λ p → lemOPairAx₃ p , lemOPairAx₆ p) , lemOPairAx₇

-- the cartesian product of two sets

_×𝕍_ : 𝕍 → 𝕍 → 𝕍
a ×𝕍 b = sup (index a × index b) (λ x → ⟨ pred a (fst x) , pred b (snd x) ⟩)

infixl 20 _×𝕍_

×𝕍₁ : {a b x : 𝕍} → x ∈ (a ×𝕍 b) → ∃𝕧∈ a λ v → ∃𝕧∈ b λ w → x ≐ ⟨ v , w ⟩
×𝕍₁ {a}{b}{x} d = fst (fst d) , snd (fst d) , snd d

proj₁ : {a b x : 𝕍} → x ∈ (a ×𝕍 b) → 𝕍
proj₁ {a} {b} x-is-pair = pred a (fst (×𝕍₁ {a} {b} x-is-pair))

proj₂ : {a b x : 𝕍} → x ∈ (a ×𝕍 b) → 𝕍
proj₂ {a} {b} x-is-pair = pred b (fst (snd ((×𝕍₁ {a} {b} x-is-pair))))


-- Union Axiom with some notions and lemmas concerning the axiom

Union : (a : 𝕍) → Σ 𝕍 (λ c → (x : 𝕍) → x ∈ c ↔ ∃𝕧∈ a (λ v → x ∈ v))
Union (sup A f) = sup (Σ A (λ y → index (f y))) (λ (w₁ , w₂) → pred (f w₁) w₂) ,
  λ x → (λ (z , d) → fst z , snd z , d) , λ (z , d) → (z , fst d) , snd d

-- the union operator

∪ : 𝕍 → 𝕍
∪ = fst (AC Union)

∪-proof : (a b : 𝕍) → b ∈ (∪ a) ↔ ∃𝕧∈ a (λ v → b ∈ v)
∪-proof = snd (AC Union)

∪-index : (a : 𝕍) → index (∪ a) ≡ Σ (index a) λ x → index (pred a x)
∪-index (sup A f) = refl

∪-cong : {a b : 𝕍} → a ≐ b → ∪ a ≐ ∪ b
∪-cong {a} {b} p = ExtAx2' λ x → (λ d → snd (∪-proof b x) (fst (fst (≐bisim p) (fst (fst (∪-proof a x) d))) ,
                                                           fst (ExtAx2 (snd (fst (≐bisim p) (fst (fst (∪-proof a x) d)))) x)
                                                                 (snd (fst (∪-proof a x) d)))) ,
                                 (λ e → snd (∪-proof a x) (fst (snd (≐bisim p) (fst (fst (∪-proof b x) e))) ,
                                                           snd (ExtAx2 (snd (snd (≐bisim p) (fst (fst (∪-proof b x) e)))) x)
                                                                 (snd (fst (∪-proof b x) e))))

_⊧Union : 𝕍 → Set
w ⊧Union = ∀𝕧∈ w λ a → ∃𝕧∈ w λ c → ∀𝕧∈ w λ x → x ∈ c ↔ ∃𝕧∈ a (λ v → x ∈ v)

inv-Union : isInv λ v → v ⊧Union
inv-Union {v}{w} p e x = fst In-w , λ z → lem₁ z , lem₂ z
  where
  x' : index v
  x' = fst (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  xx' : pred w x ≐ pred v x'
  xx' = snd (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  uni-in-v : ∃𝕧∈ v λ c → ∀𝕧∈ v λ z → z ∈ c ↔ ∃𝕧∈ (pred v x') (λ v' → z ∈ v')
  uni-in-v = e x'

  In-w : pred v (fst uni-in-v) ∈ w
  In-w = fst (≐ext p (pred v (fst uni-in-v))) (fst uni-in-v , ≐refl (pred v (fst uni-in-v)))

  inw≐inv : pred w (fst In-w) ≐ pred v (fst uni-in-v)
  inw≐inv = ≐sym (pred v (fst uni-in-v)) (pred w (fst In-w)) (snd In-w)

  lem₁ : ∀𝕧∈ w λ z → z ∈ pred w (fst In-w) → ∃𝕧∈ (pred w x) (λ w' → z ∈ w')
  lem₁ z d = let sublem₁ : ∃𝕧∈ (pred v x') λ a →
                            pred v (fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))) ∈ a
                 sublem₁ = fst (snd uni-in-v (fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))))
                              (≐transp {pred w z}
                                       {pred v (fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z))))}
                                       {pred v (fst uni-in-v)}
                                       (snd (snd (≐ext p (pred w z)) (z , ≐refl (pred w z))))
                                       (fst (≐ext inw≐inv (pred w z)) d))

                 sublem₂ : pred (pred v x') (fst sublem₁) ∈ pred w x
                 sublem₂ = snd (≐ext  xx' (pred (pred v x') (fst sublem₁)))
                               (fst sublem₁ , ≐refl (pred (pred v x') (fst sublem₁)))
             in fst sublem₂ , ≐transp {pred v (fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z))))}
                                      {pred w z}
                                      {pred (pred w x) (fst sublem₂)}
                                      (≐sym (pred w z)
                                            (pred v (fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))))
                                            (snd (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))))
                                      (fst (≐ext (snd sublem₂)
                                                 (pred v (fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z))))))
                                             (snd sublem₁))

  lem₂ : ∀𝕧∈ w λ z → ∃𝕧∈ (pred w x) (λ w' → z ∈ w') → z ∈ pred w (fst In-w)
  lem₂ z (y , d) = let sublem₁ : pred (pred w x) y ∈ pred v x'
                       sublem₁ = fst (≐ext xx' (pred (pred w x) y)) (y , ≐refl (pred (pred w x) y))

                       sublem₂ : pred w z ∈ pred v (fst uni-in-v)
                       sublem₂ = ≐transp {pred v (fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z))))}
                                         {pred w z}
                                         {pred v (fst uni-in-v)}
                                         (≐sym (pred w z)
                                               (pred v (fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))))
                                               (snd (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))))
                                         (snd (snd uni-in-v (fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))))
                                           (fst sublem₁ ,
                                           ≐transp {pred w z}
                                                    {pred v (fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z))))}
                                                    {pred (pred v x') (fst sublem₁)}
                                                    (snd (snd (≐ext p (pred w z)) (z , ≐refl (pred w z))))
                                                    (fst (≐ext (snd sublem₁) (pred w z)) d)))
                   in snd (≐ext inw≐inv (pred w z)) sublem₂

proj∪₁ : {a b R : 𝕍} → ⟨ a , b ⟩ ∈ R → a ∈ ∪ (∪ R)
proj∪₁ {a}{b}{R} x = snd (∪-proof (∪ R) a) (fst lem₃ , fst (≐ext (snd lem₃) a) lem₂)
  where
  lem₁ : sglt a ∈ ⟨ a , b ⟩
  lem₁ = pair-set-fst (sglt a) (pair-set a b)

  lem₂ : a ∈ sglt a
  lem₂ = record {} , ≐refl a

  lem₃ : sglt a ∈ ∪ R
  lem₃ = snd (∪-proof R (sglt a)) (fst x , fst (≐ext (snd x) (sglt a)) lem₁)

proj∪₂ : {a b R : 𝕍} → ⟨ a , b ⟩ ∈ R → b ∈ ∪ (∪ R)
proj∪₂ {a}{b}{R} x = snd (∪-proof (∪ R) b) (fst lem₂ , fst (≐ext (snd lem₂) b) (pair-set-snd a b))
  where
  lem₁ : pair-set a b ∈ ⟨ a , b ⟩
  lem₁ = pair-set-snd (sglt a) (pair-set a b)

  lem₂ : pair-set a b ∈ ∪ R
  lem₂ = snd (∪-proof R (pair-set a b)) (fst x , fst (≐ext (snd x) (pair-set a b)) lem₁)


-- Binary Union Axiom

UnionBi : (a b : 𝕍) → Σ 𝕍 (λ c → (x : 𝕍) → x ∈ c ↔ (x ∈ a ⊕ x ∈ b))
UnionBi (sup A f) (sup B g) = sup (A ⊕ B) h ,
  λ x → (λ (y , d) → union-prf₁ x y d) , λ y → union-prf₂ x y
    where
    h : A ⊕ B → 𝕍
    h (injl x) = f x
    h (injr x) = g x

    union-prf₁ : (x : 𝕍) (y : A ⊕ B) → x ≐ h y → (x ∈ sup A f) ⊕ (x ∈ sup B g)
    union-prf₁ x (injl z) e = injl (z , e)
    union-prf₁ x (injr z) e = injr (z , e)

    union-prf₂ : (x : 𝕍) → (x ∈ sup A f) ⊕ (x ∈ sup B g) → x ∈ sup (A ⊕ B) h
    union-prf₂ x (injl z) = injl (fst z) , snd z
    union-prf₂ x (injr z) = injr (fst z) , snd z

-- the binary union operator

_∪b_ : 𝕍 → 𝕍 → 𝕍
a ∪b b = fst (AC λ (a , b) → UnionBi a b) (a , b)

infix 25 _∪b_

∪b-proof : (a b x : 𝕍) → x ∈ (a ∪b b) ↔ (x ∈ a ⊕ x ∈ b)
∪b-proof a b = snd (AC λ (a , b) → UnionBi a b) (a , b)

∪b-index : (a b : 𝕍) → index (a ∪b b) ≡ index a ⊕ index b
∪b-index (sup A f) (sup B g) = refl

∪b-cong : {a b v w : 𝕍} → a ≐ b → v ≐ w → a ∪b v ≐ b ∪b w
∪b-cong {a} {b} {v} {w} p q = ExtAx2' λ x → (λ d → snd (∪b-proof b w x) (fst (lem x) (fst (∪b-proof a v x) d))) ,
                                            (λ e → snd (∪b-proof a v x) (snd (lem x) (fst (∪b-proof b w x) e)))
  where
  lem : (x : 𝕍) → (x ∈ a ⊕ x ∈ v) ↔ (x ∈ b ⊕ x ∈ w)
  lem x = (λ { (injl d₁) → injl (fst (ExtAx2 p x) d₁) ; (injr d₂) → injr (fst (ExtAx2 q x) d₂) }) ,
          (λ { (injl d₁) → injl (snd (ExtAx2 p x) d₁) ; (injr d₂) → injr (snd (ExtAx2 q x) d₂) })


-- Separation Axiom with the notions and lemmas concerning the axiom

SepAx : (F : 𝕍 → Set) → (a : 𝕍) →
  Σ 𝕍 λ b → (x : 𝕍) → x ∈ b ↔ ∃𝕧∈ a (λ v → (F v) × (x ≐ v))
SepAx F (sup A f) = (sup (Σ A λ x → F (f x)) λ c → f (fst c)) ,
  λ x → (λ (y , d) → fst y , snd y , d) ,
    λ e → ((fst e , fst (snd e))) , snd (snd e)

sep : (𝕍 → Set) → 𝕍 → 𝕍
sep F = fst (AC (SepAx F))

sep-proof : (F : 𝕍 → Set) → (a x : 𝕍) →
  x ∈ (sep F a) ↔ ∃𝕧∈ a (λ v → (F v) × (x ≐ v))
sep-proof F a = snd (AC (SepAx F)) a

-- another formulation of Separation Axiom

SepAx' : (F : 𝕍 → Set) → (isInv F) → (a : 𝕍) →
  Σ 𝕍 λ b → (x : 𝕍) → x ∈ b ↔ (x ∈ a × F x)
SepAx' F F-is-inv (sup A f) = sup (Σ A λ x → F (f x)) (λ c → f (fst c)) ,
  λ x → (λ (y , d) → (fst y , d) , F-is-inv (≐sym x (f (fst y)) d) (snd y)) ,
    λ (d , e) → (fst d , F-is-inv (snd d) e) , snd d

_⊧Sep : 𝕍 → Set₁
w ⊧Sep = (F : 𝕍 → Set) → (isInv F) → ∀𝕧∈ w λ a →
  ∃𝕧∈ w λ b → ∀𝕧∈ w λ x → x ∈ b ↔ (x ∈ a × F x)

inv-Sep : isInv λ v → v ⊧Sep
inv-Sep {v}{w} p e F F-inv x = fst In-w , λ z → lem₁ z , lem₂ z
  where
  x' : index v
  x' = fst (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  xx' : pred w x ≐ pred v x'
  xx' = snd (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  sep-in-v : ∃𝕧∈ v λ b → ∀𝕧∈ v λ z → z ∈ b ↔ (z ∈ (pred v x') × F z)
  sep-in-v = e F F-inv x'

  In-w : pred v (fst sep-in-v) ∈ w
  In-w = fst (≐ext p (pred v (fst sep-in-v))) (fst sep-in-v , ≐refl (pred v (fst sep-in-v)))

  inw≐inv : pred w (fst In-w) ≐ pred v (fst sep-in-v)
  inw≐inv = ≐sym (pred v (fst sep-in-v)) (pred w (fst In-w)) (snd In-w)

  lem₁ : ∀𝕧∈ w λ z → (z ∈ pred w (fst In-w)) → (z ∈ (pred w x) × F z)
  lem₁ z (u , d) = fst (≐ext (≐sym (pred w x) (pred v x') xx') (pred w z)) sublem₂ ,
                   sublem₃
    where
    z' : index v
    z' = fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))

    zz' : pred w z ≐ pred v z'
    zz' = snd (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))

    sublem₁ : pred v z' ∈ pred v (fst sep-in-v)
    sublem₁ = fst (fst (≐bisim inw≐inv) u) ,
              ≐trans (pred v z') (pred w z)
                     (pred (pred v (fst sep-in-v)) (fst (fst (≐bisim inw≐inv) u)))
                     (≐sym (pred w z) (pred v z') zz')
                     (≐trans (pred w z) (pred (pred w (fst In-w)) u)
                             (pred (pred v (fst sep-in-v)) (fst (fst (≐bisim inw≐inv) u)))
                             d
                             (snd (fst (≐bisim inw≐inv) u)))

    sublem₂ : pred w z ∈ pred v x'
    sublem₂ = ≐transp {x = pred v x'} (≐sym (pred w z) (pred v z') zz')
                                      (fst (fst (snd sep-in-v z') sublem₁))

    sublem₃ : F (pred w z)
    sublem₃ = F-inv (≐sym (pred w z) (pred v z') zz')
                    (snd (fst (snd sep-in-v z') sublem₁))

  lem₂ : ∀𝕧∈ w λ z → (z ∈ (pred w x) × F z) → (z ∈ pred w (fst In-w))
  lem₂ z (d₁ , d₂) = snd (≐ext inw≐inv (pred w z)) sublem
    where
    z' : index v
    z' = fst (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))

    zz' : pred w z ≐ pred v z'
    zz' = snd (snd (≐ext p (pred w z)) (z , ≐refl (pred w z)))

    sublem : pred w z ∈ pred v (fst sep-in-v)
    sublem = ≐transp {x = pred v (fst sep-in-v)} (≐sym (pred w z) (pred v z') zz')
                     (snd (snd sep-in-v z') (≐transp {x = pred v x'} zz'
                                                     (fst (≐ext xx' (pred w z)) d₁) ,
                                             F-inv zz' d₂ ))


-- the domain and range of binary relation

domAx : (R : 𝕍) → Σ 𝕍 λ a → (x : 𝕍) → (x ∈ a ↔ Σ 𝕍 λ b → ⟨ x , b ⟩ ∈ R)
domAx R = let invDom : (R : 𝕍) → isInv λ a → ∃𝕧∈ (∪ (∪ R)) (λ b → ⟨ a , b ⟩ ∈ R)
              invDom R p x = fst x , ≐transp {x = R} (lemOPairAx₇ (p , ≐refl (pred (∪ (∪ R)) (fst x)))) (snd x)

              domSet : Σ 𝕍 (λ b → (x : 𝕍) →
                         (x ∈ b) ↔ (x ∈ ∪ (∪ R) × ∃𝕧∈ (∪ (∪ R)) (λ b₁ → ⟨ x , b₁ ⟩ ∈ R)))
              domSet = SepAx' (λ a → ∃𝕧∈ (∪ (∪ R)) (λ b → ⟨ a , b ⟩ ∈ R)) (invDom R) (∪ (∪ R))
          in fst domSet ,
             λ x → (λ c → pred (∪ (∪ R)) (fst (snd (fst (snd domSet x) c))) ,
                          snd (snd (fst (snd domSet x) c))) ,
                    λ d → snd (snd domSet x) (proj∪₁ {R = R} (snd d) ,
                            fst (proj∪₂ {R = R} (snd d)) ,
                            ≐transp {x = R} (lemOPairAx₇ (≐refl x , snd (proj∪₂ {R = R} (snd d)))) (snd d))

dom : 𝕍 → 𝕍
dom = fst (AC domAx)

dom-proof : (R x : 𝕍) → (x ∈ dom R ↔ Σ 𝕍 λ b → ⟨ x , b ⟩ ∈ R)
dom-proof = snd (AC domAx)

ranAx : (R : 𝕍) → Σ 𝕍 λ a → (x : 𝕍) → (x ∈ a ↔ Σ 𝕍 λ b → ⟨ b , x ⟩ ∈ R)
ranAx R = let invRan : (R : 𝕍) → isInv λ a → ∃𝕧∈ (∪ (∪ R)) (λ b → ⟨ b , a ⟩ ∈ R)
              invRan R p x = fst x , ≐transp {x = R} (lemOPairAx₇ (≐refl (pred (∪ (∪ R)) (fst x)) , p)) (snd x)

              ranSet : Σ 𝕍 (λ b → (x : 𝕍) →
                         (x ∈ b) ↔ (x ∈ ∪ (∪ R) × ∃𝕧∈ (∪ (∪ R)) (λ b₁ → ⟨ b₁ , x ⟩ ∈ R)))
              ranSet = SepAx' (λ a → ∃𝕧∈ (∪ (∪ R)) (λ b → ⟨ b , a ⟩ ∈ R)) (invRan R) (∪ (∪ R))
          in fst ranSet ,
             λ x → (λ c → pred (∪ (∪ R)) (fst (snd (fst (snd ranSet x) c))) ,
                          snd (snd (fst (snd ranSet x) c))) ,
                    λ d → snd (snd ranSet x) (proj∪₂ {R = R} (snd d) ,
                            fst (proj∪₁ {R = R} (snd d)) ,
                            ≐transp {x = R} (lemOPairAx₇ (snd (proj∪₁ {R = R} (snd d)) , ≐refl x)) (snd d))

ran : 𝕍 → 𝕍
ran = fst (AC ranAx)

ran-proof : (R x : 𝕍) → (x ∈ ran R ↔ Σ 𝕍 λ b → ⟨ b , x ⟩ ∈ R)
ran-proof = snd (AC ranAx)

-- function application: note that _[_] is defined for an arbitrary set f : 𝕍

funAppAx : (f x : 𝕍) → Σ 𝕍 λ c → (a : 𝕍) → (a ∈ c ↔ Σ 𝕍 (λ b → ⟨ x , b ⟩ ∈ f × a ∈ b))
funAppAx f x = let F : 𝕍 → Set
                   F = λ y → ∃𝕧∈ (ran f) (λ b → ⟨ x , b ⟩ ∈ f × y ∈ b)

                   invApp : isInv F
                   invApp p c = fst c , fst (snd c) , ≐transp {x = pred (ran f) (fst c)} p (snd (snd c))
               in fst (SepAx' F invApp (∪ (ran f))) ,
                  λ a → (λ c → pred (ran f) (fst (snd (fst (snd (SepAx' F invApp (∪ (ran f))) a) c))) ,
                               snd (snd (fst (snd (SepAx' F invApp (∪ (ran f))) a) c))) ,
                        λ d → snd (snd (SepAx' F invApp (∪ (ran f))) a)
                                (snd (∪-proof (ran f) a)
                                  (fst (snd (ran-proof f (fst d)) (x , fst (snd d))) ,
                                   fst (≐ext (snd (snd (ran-proof f (fst d)) (x , fst (snd d)))) a) (snd (snd d))) ,
                                fst (snd (ran-proof f (fst d)) (x , fst (snd d))) ,
                                ≐transp {x = f}
                                  (lemOPairAx₇ (≐refl x , snd (snd (ran-proof f (fst d)) (x , fst (snd d))))) (fst (snd d)) ,
                                  fst (≐ext (snd (snd (ran-proof f (fst d)) (x , fst (snd d)))) a) (snd (snd d)))

_[_] : 𝕍 → 𝕍 → 𝕍
f [ x ] = fst (AC (funAppAx f)) x

funApp-proof : (f x a : 𝕍) → (a ∈ (f [ x ]) ↔ Σ 𝕍 (λ b → ⟨ x , b ⟩ ∈ f × a ∈ b))
funApp-proof f x a = snd (AC (funAppAx f)) x a


-- Collection Axioms

LemForColl : {ℓ : Level} {F : 𝕍 → 𝕍 → Set ℓ} {a b : 𝕍} → (p : index a ≡ index b) →
  ((x : index a) → F (pred a x) (pred b (transp (λ A → A) p x))) →
    ((y : index b) → F (pred a (transp (λ A → A) (≡sym p) y)) (pred b y)) → 
      ∀𝕧∈ a (λ v → ∃𝕧∈ b (λ w → F v w)) × ∀𝕧∈ b (λ w → ∃𝕧∈ a (λ v → F v w))
LemForColl p c₁ c₂ = (λ z → transp (λ A → A) p z , c₁ z) ,
  λ u → transp (λ A → A) (≡sym p) u , c₂ u

-- Strong Collection

StrColl : {ℓ : Level} {F : 𝕍 → 𝕍 → Set ℓ} {a : 𝕍} → ∀𝕧∈ a (λ v → Σ 𝕍 (λ w → F v w)) →
  Σ 𝕍 (λ b → ∀𝕧∈ a (λ v → ∃𝕧∈ b (λ w → F v w)) × ∀𝕧∈ b (λ w → ∃𝕧∈ a (λ v → F v w)))
StrColl {a = a} c = sup (index a) (λ x → fst (c x)) ,
  (λ x → x , snd (c x)) , λ x → x , snd (c x)

_⊧StrColl : 𝕍 → Set₁
c ⊧StrColl = {F : 𝕍 → 𝕍 → Set} → ((w : 𝕍) → isInv (λ v → F v w)) → ((v : 𝕍) → isInv (λ w → F v w)) →
  ∀𝕧∈ c (λ a → (∀𝕧∈ a λ v → ∃𝕧∈ c λ w → F v w) →
    ∃𝕧∈ c λ b → (∀𝕧∈ a λ v → ∃𝕧∈ b λ w → F v w) × (∀𝕧∈ b λ w → ∃𝕧∈ a λ v → F v w))

-- Subset Collection

SubColl : {ℓ : Level} {F : (v w u : 𝕍) → Set ℓ} → (a b : 𝕍) →
  Σ 𝕍 λ c → (u : 𝕍) → ∀𝕧∈ a (λ v → ∃𝕧∈ b (λ w → F v w u)) →
    ∃𝕧∈ c λ d → ∀𝕧∈ a (λ v → ∃𝕧∈ d (λ w → F v w u)) × ∀𝕧∈ d (λ w → ∃𝕧∈ a (λ v → F v w u))
SubColl {F = F} a b = sup (index a → index b) (λ f → sup (index a) λ x → pred b (f x)) ,
  λ u e → (λ x → fst (e x)) , (λ x → x , snd (e x)) , (λ x → x , snd (e x))

_⊧SubColl : 𝕍 → Set₁
z ⊧SubColl = {F : (v w u : 𝕍) → Set} → ((w u : 𝕍) → isInv λ v → F v w u) → ((v u : 𝕍) → isInv λ w → F v w u) →
  ∀𝕧∈ z λ a → ∀𝕧∈ z λ b → ∃𝕧∈ z λ c →
    ∀𝕧∈ z λ u → ∀𝕧∈ a (λ v → ∃𝕧∈ b (λ w → F v w u)) →
      ∃𝕧∈ c λ d → ∀𝕧∈ a (λ v → ∃𝕧∈ d (λ w → F v w u)) × ∀𝕧∈ d (λ w → ∃𝕧∈ a (λ v → F v w u))


-- multi-valued functions

mv : 𝕍 → 𝕍 → 𝕍 → Set
mv a b R = R ⊆ (a ×𝕍 b) × ∀𝕧∈ a λ v → ∃𝕧∈ b λ w → ⟨ v , w ⟩ ∈ R

mv-is-inv : (a b : 𝕍) → isInv λ R → mv a b R
mv-is-inv a b {R} {S} p d =
  (λ x → fst (v₂ x) ,
    ≐trans (pred S x) (pred R ((fst (v₁ x)))) (pred (a ×𝕍 b) (fst (v₂ x))) (snd (v₁ x)) (snd (v₂ x))) ,
  λ x → fst (snd d x) , fst (≐ext p ⟨ pred a x , pred b (fst (snd d x))⟩) (snd (snd d x))
  where
  v₁ : (x : index S) → pred S x ∈ R
  v₁ x = fst (≐ext (≐sym R S p) (pred S x)) (x , ≐refl (pred S x))
    
  v₂ : (x : index S) → pred R ((fst (v₁ x))) ∈ (a ×𝕍 b)
  v₂ x = fst d (fst (v₁ x))

-- Fullness relation

isFull : 𝕍 → 𝕍 → 𝕍 → Set₁
isFull a b C = (∀𝕧∈ C λ S → mv a b S) × ((R : 𝕍) → mv a b R → ∃𝕧∈ C λ S → S ⊆ R)

Fullness-lem : (a b R : 𝕍) → mv a b R → ∀𝕧∈ a λ x → ∃𝕧∈ (a ×𝕍 b) λ y →
  y ∈ R × ∃𝕧∈ b λ z → y ≐ ⟨ x , z ⟩
Fullness-lem a b R e x = (x , fst (snd e x)) , snd (snd e x) ,
  fst (snd e x) , ≐refl ⟨ pred a x , pred b (fst (snd e x)) ⟩

-- Fullness Axiom

Fullness : (a b : 𝕍) → Σ 𝕍 λ C → isFull a b C
Fullness a b = C , (λ x → full₁ (pred C x) (x , ≐refl (pred C x))) , full₂
  where
  F₁ : (x y R : 𝕍) → Set
  F₁ x y R = y ∈ R × ∃𝕧∈ b λ z → y ≐ ⟨ x , z ⟩

  C' : 𝕍
  C' = fst (SubColl {F = F₁} a (a ×𝕍 b))

  C : 𝕍
  C = fst (SepAx' (λ R → mv a b R) (mv-is-inv a b) C')

  C-claim : (R : 𝕍) → R ∈ C ↔ (R ∈ C' × mv a b R)
  C-claim = snd (SepAx' (λ R → mv a b R) (mv-is-inv a b) C')

  full₁ : (R : 𝕍) → R ∈ C → mv a b R
  full₁ R e = snd (fst (C-claim R) e)

  C'-claim₁ : (R : 𝕍) → mv a b R →
    ∃𝕧∈ C' (λ S → ∀𝕧∈ a (λ x → ∃𝕧∈ S (λ y → F₁ x y R)) × ∀𝕧∈ S (λ y → ∃𝕧∈ a (λ x → F₁ x y R)))
  C'-claim₁ R e = (snd (SubColl {F = F₁} a (a ×𝕍 b))) R (Fullness-lem a b R e)

  C'-claim₂ : (R : 𝕍) → mv a b R → ∃𝕧∈ C' λ S → S ⊆ R × (mv a b S)
  C'-claim₂ R e = fst (C'-claim₁ R e) , S⊆R ,
    ⊆trans {S}{R} S⊆R (fst e) ,
      λ x → idb x , ≐transp (snd (snd (snd (fst (snd (C'-claim₁ R e)) x))))
        (fst (fst (snd (C'-claim₁ R e)) x) , ≐refl (pair-in-S x))
    where
    S : 𝕍
    S = pred C' (fst (C'-claim₁ R e))

    S⊆R : S ⊆ R
    S⊆R = λ x → fst (snd (fst (snd (C'-claim₁ R e)) x))

    pair-in-S : index a → 𝕍
    pair-in-S x = pred S (fst (fst (snd (C'-claim₁ R e)) x))

    idb : index a → index b
    idb x = fst (snd (snd (fst (snd (C'-claim₁ R e)) x)))

  full₂ : (R : 𝕍) → mv a b R → ∃𝕧∈ C λ S → S ⊆ R
  full₂ R e = fst full₂-lem₂ , ⊆trans {pred C (fst full₂-lem₂)}{pred C' idC'}{R}
    (λ x → fst (≐ext full₂-lem₅ (full₂-lem₄ x)) (x , ≐refl (full₂-lem₄ x))) full₂-lem₃
    where
    idC' : index C'
    idC' = fst (C'-claim₂ R e)

    full₂-lem₁ : pred C' idC' ∈ C'
    full₂-lem₁ = fst (C'-claim₂ R e) , ≐refl (pred C' (fst (C'-claim₂ R e)))

    full₂-lem₂ : pred C' idC' ∈ C
    full₂-lem₂ = snd (C-claim (pred C' idC')) (full₂-lem₁ , snd (snd (C'-claim₂ R e)))

    full₂-lem₃ : pred C' idC' ⊆ R
    full₂-lem₃ = fst (snd (C'-claim₂ R e))

    full₂-lem₄ : (x : index (pred C (fst full₂-lem₂))) → 𝕍
    full₂-lem₄ x = pred (pred C (fst full₂-lem₂)) x

    full₂-lem₅ : pred C (fst full₂-lem₂) ≐ pred C' idC'
    full₂-lem₅ = ≐sym (pred C' idC') (pred C (fst full₂-lem₂)) (snd full₂-lem₂)


-- exponentiation

exp : 𝕍 → 𝕍 → 𝕍 → Set
exp a b f = f ⊆ (a ×𝕍 b) × ∀𝕧∈ a λ v → ∃𝕧∈ b λ w →
  (⟨ v , w ⟩ ∈ f) × (∀𝕧∈ b λ w' → ⟨ v , w' ⟩ ∈ f → w ≐ w')

exp-mv : {a b f : 𝕍} → exp a b f → mv a b f
exp-mv {a}{b}{f} e = fst e , λ x → fst (snd e x) , fst (snd (snd e x))


Exp-lem : (a b : 𝕍) → isInv (λ f → exp a b f)
Exp-lem a b {g} {h} p e = ≐-⊆ p (fst e) , λ x → fst (snd e x) ,
  fst (≐ext p ⟨ pred a x , pred b (fst (snd e x)) ⟩) (fst (snd (snd e x))) ,
    λ y d → (snd (snd (snd e x))) y (fst (≐ext (≐sym g h p) ⟨ pred a x , pred b y ⟩) d)  

-- Exponentiation Axiom

Exp : (a b : 𝕍) → Σ 𝕍 λ c → (f : 𝕍) → f ∈ c ↔ exp a b f
Exp a b = fst Exp-lem₂ , λ f →
  (λ d → snd (fst (snd Exp-lem₂ f) d)) ,                      -- the proof of f ∈ c → exp a b f
  λ e → snd (snd Exp-lem₂ f) (≐transp (≐ext' (Exp-lem₄ f e))  -- the proof of f ∈ c ← exp a b f 
    (fst (Exp-lem₃ f e) , ≐refl (pred (fst Exp-lem₁) (fst (Exp-lem₃ f e)))) , e)
  where
  Exp-lem₁ : Σ 𝕍 λ C → isFull a b C
  Exp-lem₁ = Fullness a b

  Exp-lem₂ : Σ 𝕍 (λ C' → (f : 𝕍) → (f ∈ C') ↔ (f ∈ fst Exp-lem₁ × exp a b f))
  Exp-lem₂ = SepAx' (λ f → exp a b f) (Exp-lem a b) (fst Exp-lem₁)

  Exp-lem₃ : (f : 𝕍) → exp a b f → ∃𝕧∈ (fst Exp-lem₁) (λ S → S ⊆ f)
  Exp-lem₃ f e = snd (snd Exp-lem₁) f (exp-mv {a}{b}{f} e)

  Exp-lem₄ : (f : 𝕍) → (e : exp a b f) → (x : 𝕍) →
    (x ∈ pred (fst Exp-lem₁) (fst (Exp-lem₃ f e))) ↔ (x ∈ f)
  Exp-lem₄ f e x = (λ d → ≐transp {x = f}
    (≐sym x (pred (pred (fst Exp-lem₁) (fst (Exp-lem₃ f e))) (fst d)) (snd d)) (snd (Exp-lem₃ f e) (fst d))) ,
    λ d → ≐transp {x = pred (fst Exp-lem₁) (fst (Exp-lem₃ f e))} (v₁v₃≐x d) (v₁v₃∈f' d)
    where
    v₁ : x ∈ f → 𝕍
    v₁ d = pred a (fst (×𝕍₁ {a}{b} ((fst e) (fst d))))

    v₂ : x ∈ f → 𝕍
    v₂ d = pred b (fst (snd (×𝕍₁ {a}{b} ((fst e) (fst d)))))

    v₃ : x ∈ f → 𝕍
    v₃ d = pred b (fst (snd e (fst (×𝕍₁ {a}{b} (fst e (fst d))))))

    x≐v₁v₂ : (d : x ∈ f) → x ≐ ⟨ v₁ d , v₂ d ⟩
    x≐v₁v₂ d = ≐trans x (pred f (fst d)) ⟨ v₁ d , v₂ d ⟩ (snd d)
      (snd (snd (×𝕍₁ {a}{b} ((fst e) (fst d)))))

    v₁v₂∈f : (d : x ∈ f) → ⟨ v₁ d , v₂ d ⟩ ∈ f
    v₁v₂∈f d = ≐transp {x = f} (x≐v₁v₂ d) d

    v₁v₃∈f : (d : x ∈ f) → ⟨ v₁ d , v₃ d ⟩ ∈ f
    v₁v₃∈f d = fst (snd ((snd e) (fst (×𝕍₁ {a}{b} ((fst e) (fst d))))))

    v₁v₃∈f' : (d : x ∈ f) → ⟨ v₁ d , v₃ d ⟩ ∈ pred (fst Exp-lem₁) (fst (Exp-lem₃ f e))
    v₁v₃∈f' d = snd (snd (fst (snd Exp-lem₁) (fst (Exp-lem₃ f e))) (fst (×𝕍₁ {a}{b} ((fst e) (fst d)))))

    v₃≐v₂ : (d : x ∈ f) → ⟨ v₁ d , v₃ d ⟩ ≐ ⟨ v₁ d , v₂ d ⟩
    v₃≐v₂ d = snd OPairAx (≐refl (v₁ d) ,
      snd (snd (snd e (fst (×𝕍₁ {a}{b} (fst e (fst d)))))) (fst (snd (×𝕍₁ {a}{b} ((fst e) (fst d))))) (v₁v₂∈f d))

    v₁v₃≐x : (d : x ∈ f) → ⟨ v₁ d , v₃ d ⟩ ≐ x
    v₁v₃≐x d = ≐trans ⟨ v₁ d , v₃ d ⟩ ⟨ v₁ d , v₂ d ⟩ x (v₃≐v₂ d) (≐sym x ⟨ v₁ d , v₂ d ⟩ (x≐v₁v₂ d))


-- Infinity Axiom with some notions and lemmas concerning the axiom

∅ : 𝕍
∅ = sup ⊥ (⊥elim λ _ → 𝕍)

suc𝕍 : 𝕍 → 𝕍
suc𝕍 a = sup (index a ⊕ ⊤) λ x → ⊕elim (λ _ → 𝕍) (λ y → pred a y) (λ z → a) x

∅-is-empty : (a : 𝕍) → a ∈ ∅ ↔ ⊥
∅-is-empty a = (λ c → fst c) , λ x → ⊥elim (λ _ → a ∈ ∅) x

suc𝕍Ax : (a x : 𝕍) → x ∈ suc𝕍 a ↔ ((x ∈ a) ⊕ (x ≐ a))
suc𝕍Ax a x = suc𝕍Axlem₁ , suc𝕍Axlem₂ 
  where
  suc𝕍Axlem₁ : x ∈ suc𝕍 a → ((x ∈ a) ⊕ (x ≐ a))
  suc𝕍Axlem₁ (injl y , c₂) = injl (y , c₂)
  suc𝕍Axlem₁ (injr y , c₂) = injr c₂

  suc𝕍Axlem₂ : ((x ∈ a) ⊕ (x ≐ a)) → x ∈ suc𝕍 a
  suc𝕍Axlem₂ (injl y) = injl (fst y) , snd y
  suc𝕍Axlem₂ (injr y) = injr tt , y

PeanoAx₁ : (a : 𝕍) → suc𝕍 a ≐ ∅ → ⊥
PeanoAx₁ a p = fst (fst (≐ext p a) (injr tt , ≐refl a))

PeanoAx₂ : (a b : 𝕍) → suc𝕍 a ≐ suc𝕍 b → a ≐ b
PeanoAx₂ a b p = ⊕elim (λ _ → a ≐ b) PeanoAx₂lem₃ (λ q → q) (fst (suc𝕍Ax b a) PeanoAx₂lem₁)
  where
  PeanoAx₂lem₁ : a ∈ suc𝕍 b
  PeanoAx₂lem₁ = fst (≐ext p a) (injr tt , ≐refl a)

  PeanoAx₂lem₂ : b ∈ suc𝕍 a
  PeanoAx₂lem₂ = fst (≐ext (≐sym (suc𝕍 a) (suc𝕍 b) p) b) (injr tt , ≐refl b)

  PeanoAx₂lem₃ : a ∈ b → a ≐ b
  PeanoAx₂lem₃ c₁ = ⊕elim (λ _ → a ≐ b) (λ c₂ → ⊥elim (λ _ → a ≐ b) (∈-isWF a b (c₁ , c₂)))
    (λ q → ≐sym b a q ) (fst (suc𝕍Ax a b) PeanoAx₂lem₂)

suc𝕍-compat : (a b : 𝕍) → a ≐ b → suc𝕍 a ≐ suc𝕍 b
suc𝕍-compat (sup A f) (sup B g) p = suc𝕍-compat-lem₁ , suc𝕍-compat-lem₂
  where
  suc𝕍-compat-lem₁ : ∀𝕧∈ (suc𝕍 (sup A f)) (λ v → ∃𝕧∈ (suc𝕍 (sup B g)) (λ w → v ≐ w))
  suc𝕍-compat-lem₁ (injl x) = injl (fst (fst p x)) , snd (fst p x)
  suc𝕍-compat-lem₁ (injr x) = injr tt , p

  suc𝕍-compat-lem₂ : ∀𝕧∈ (suc𝕍 (sup B g)) (λ w → ∃𝕧∈ (suc𝕍 (sup A f)) (λ v → v ≐ w))
  suc𝕍-compat-lem₂ (injl x) = injl (fst (snd p x)) , snd (snd p x)
  suc𝕍-compat-lem₂ (injr x) = injr tt , p

ω : 𝕍
ω = sup Nat λ n → Natelim (λ _ → 𝕍) ∅ (λ m a → suc𝕍 a) n

∅-in-ω : ∅ ∈ ω
∅-in-ω = zero , ≐refl ∅

suc𝕍-ω : (a : 𝕍) → a ∈ ω → suc𝕍 a ∈ ω
suc𝕍-ω a c = suc (fst c) , suc𝕍-compat a (pred ω (fst c)) (snd c)

pred-suc𝕍 : (n : Nat) → pred ω (suc n) ≐ suc𝕍 (pred ω n)
pred-suc𝕍 n = ≐refl (suc𝕍 (pred ω n))

suc𝕍-ω' : ∀𝕧∈ ω (λ v → suc𝕍 v ∈ ω)
suc𝕍-ω' x = ≐transp (pred-suc𝕍 x) (suc x , ≐refl (pred ω (suc x)))

pdc : (a : 𝕍) → {a ∈ ω} → 𝕍
pdc a {zero , c} = ∅
pdc a {suc n , c} = pred ω n

ω-ind : {ℓ : Level} {F : 𝕍 → Set ℓ} → F ∅ → (∀𝕧∈ ω (λ v → F v → F (suc𝕍 v))) →
  ∀𝕧∈ ω (λ v → F v)
ω-ind {F = F} base idstep zero = base
ω-ind {F = F} base idstep (suc x) = idstep x (ω-ind {F = F} base idstep x)

_⊧Infty : 𝕍 → Set
w ⊧Infty = (∃𝕧∈ w λ a → a ≐ ∅) × (∀𝕧∈ w λ a → ∃𝕧∈ w λ b → b ≐ suc𝕍 a)


-- transitive closure

tc : 𝕍 → 𝕍
tc (sup A f) = (sup A f) ∪b (∪ (sup A (λ x → tc (f x))))

TcAx : (a x : 𝕍) → x ∈ tc a ↔ ((x ∈ a) ⊕ (x ∈ ∪ (sup (index a) λ x → tc (pred a x))))
TcAx (sup A f) x = ∪b-proof (sup A f) (∪ (sup A λ x → tc (f x))) x

⊆-tc : (a : 𝕍) → a ⊆ tc a
⊆-tc (sup A f) = λ x → injl x , ≐refl (f x)

⊆'-tc : (a : 𝕍) → a ⊆' tc a
⊆'-tc (sup A f) x (y , c) = injl y , c

tc-is-trans : (a : 𝕍) → isTransitive (tc a)
tc-is-trans (sup A f) (sup B g) c d d' = ⊕elim (λ _ → c ∈ tc (sup A f))
  (λ e → injr (fst e , fst (⊆'-tc (f (fst e)) c (fst (≐ext (snd e) c) d'))) ,
    snd (⊆'-tc (f (fst e)) c (fst (≐ext (snd e) c) d')))
  (λ e → injr (fst (fst e) , fst (tc-is-trans (f (fst (fst e))) (sup B g) c (snd (fst e) , snd e) d')) ,
    snd (tc-is-trans (f (fst (fst e))) (sup B g) c (snd (fst e) , snd e) d'))
  (fst (TcAx (sup A f) (sup B g)) d)

tc-tc : (a : 𝕍) → {b : 𝕍} → b ∈ (tc a) → (tc b) ⊆ (tc a)
tc-tc a {sup B g} c (injl x) = tc-is-trans a (sup B g) (g x) c (x , ≐refl (g x))
tc-tc a {sup B g} c (injr (x , u)) = tc-tc a {g x} (tc-is-trans a (sup B g) (g x) c (x , ≐refl (g x))) u

tc-tc' : (a : 𝕍) → {b : 𝕍} → b ∈ (tc a) → (tc b) ⊆' (tc a)
tc-tc' a {b} d c e = ≐transp {pred (tc b) (fst e)} {c} {tc a}
  (≐sym c (pred (tc b) (fst e)) (snd e)) (tc-tc a {b} d (fst e))

tc-cong : {a b : 𝕍} → a ≐ b → (c : 𝕍) → c ∈ tc a → c ∈ tc b
tc-cong {sup A f} {sup B g} p c (injl x , q) =
  injl (fst (fst p x)) , ≐trans c (f x) (g (fst (fst p x))) q (snd (fst p x))
tc-cong {sup A f} {sup B g} p c (injr x , q) =
  injr (fst (fst p (fst x)) , fst lem) , snd lem
  where
  lem : c ∈ tc (g (fst (fst p (fst x))))
  lem = tc-cong (snd (fst p (fst x))) c (snd x , q)

tc-cong' : {a b : 𝕍} → a ≐ b → tc a ≐ tc b
tc-cong' {sup a f}{sup b g} p = lem₁ , lem₂
  where
  lem₁ : (x : index (tc (sup a f))) → Σ (index (tc (sup b g))) λ y → pred (tc (sup a f)) x ≐ pred (tc (sup b g)) y
  lem₁ (injl z) = injl (fst (fst p z)) , snd (fst p z)
  lem₁ (injr w) = injr (fst (fst p (fst w)) ,
                          fst ((fst (fst ≐logeq (tc-cong' {f (fst w)}{g (fst (fst p (fst w)))} (snd (fst p (fst w)))))) (snd w))) ,
                  snd ((fst (fst ≐logeq (tc-cong' {f (fst w)}{g (fst (fst p (fst w)))} (snd (fst p (fst w)))))) (snd w))

  lem₂ : (y : index (tc (sup b g))) → Σ (index (tc (sup a f))) λ x → pred (tc (sup a f)) x ≐ pred (tc (sup b g)) y
  lem₂ (injl z) = injl (fst (snd p z)) , snd (snd p z)
  lem₂ (injr w) = injr (fst (snd p (fst w)) ,
                          fst ((snd (fst ≐logeq (tc-cong' {f (fst (snd p (fst w)))}{g (fst w)} (snd (snd p (fst w)))))) (snd w))) ,
                  snd ((snd (fst ≐logeq (tc-cong' {f (fst (snd p (fst w)))}{g (fst w)} (snd (snd p (fst w)))))) (snd w))


-- the transfinite induction principles for transitive closures of sets

interleaved mutual

  ∈-tcTI : {ℓ : Level} {F : 𝕍 → Set ℓ} →
            ((a : 𝕍) → (∀𝕧∈ (tc a) λ v → F v) → F a) → (a : 𝕍) → F a

  ∈-tcTI-IH : {ℓ : Level} {F : 𝕍 → Set ℓ} →
                ((a : 𝕍) → (∀𝕧∈ (tc a) λ v → F v) → F a) →
                  (a : 𝕍) → ∀𝕧∈ (tc a) λ v → F v

  ∈-tcTI {ℓ} {F} e (sup A f) = e (sup A f) (∈-tcTI-IH {ℓ} {F} e (sup A f))
  ∈-tcTI-IH {ℓ} {F} e (sup A f) (injl x) = ∈-tcTI e (f x)
  ∈-tcTI-IH {ℓ} {F} e (sup A f) (injr (y , c)) =
    ∈-tcTI {F = λ a → ∀𝕧∈ (tc a) λ v → F v} (λ a d z → e (pred (tc a) z) (d z)) (f y) c


-- the notion of CZF model

_⊧CZF : 𝕍 → Set₁
a ⊧CZF = (a ⊧SetInd) × (a ⊧Pairs) × (a ⊧Union) × (a ⊧Sep) × (a ⊧StrColl) × (a ⊧SubColl) × (a ⊧Infty)
