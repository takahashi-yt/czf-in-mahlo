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

   The proofs for Fullness Axiom and Exponentiation Axiom below are the ones in:

   Michael Rathjen, Edward R. Griffor, and Erik Palmgren. Inaccessibility in constructive set theory
   and type theory. Ann. Pure Appl. Log., 94(1-3):181--200, 1998.
-}


-- Pairing Axiom and some notions and lemmas concerning the axiom

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

_⊧Pairs : 𝕍 → Set₁
w ⊧Pairs = ∀𝕧∈ w λ a → ∀𝕧∈ w λ b → ∃𝕧∈ w λ c → (x : 𝕍) → x ∈ c ↔ ((x ≐ a) ⊕ (x ≐ b))

inv-Pairs : isInv λ v → v ⊧Pairs
inv-Pairs {v}{w} p e x y = fst In-w ,
  λ z → lem₁ z , lem₂ z
  where
  x' : index v
  x' = fst (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  xx' : pred w x ≐ pred v x'
  xx' = snd (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  y' : index v
  y' = fst (snd (≐ext p (pred w y)) (y , ≐refl (pred w y)))

  yy' : pred w y ≐ pred v y'
  yy' = snd (snd (≐ext p (pred w y)) (y , ≐refl (pred w y)))

  pair-in-v : ∃𝕧∈ v (λ c → (z : 𝕍) → (z ∈ c) ↔ ((z ≐ pred v x') ⊕ (z ≐ pred v y')))
  pair-in-v = e x' y'

  In-w : pred v (fst pair-in-v) ∈ w
  In-w = fst (≐ext p (pred v (fst pair-in-v))) (fst pair-in-v , ≐refl (pred v (fst pair-in-v)))

  inw≐inv : pred w (fst In-w) ≐ pred v (fst pair-in-v)
  inw≐inv = ≐sym (pred v (fst pair-in-v)) (pred w (fst In-w)) (snd In-w)

  lem₁ : (z : 𝕍) → z ∈ pred w (fst In-w) → (z ≐ pred w x) ⊕ (z ≐ pred w y)
  lem₁ z d = ⊕elim (λ _ → (z ≐ pred w x) ⊕ (z ≐ pred w y))
    (λ c → injl (≐trans z (pred v x') (pred w x) c (≐sym (pred w x) (pred v x') xx')))
      (λ c → injr (≐trans z (pred v y') (pred w y) c (≐sym (pred w y) (pred v y') yy')))
        (fst (snd pair-in-v z) (fst (≐ext inw≐inv z) d))

  lem₂ : (z : 𝕍) → (z ≐ pred w x) ⊕ (z ≐ pred w y) → z ∈ pred w (fst In-w)
  lem₂ z (injl d₁) = fst (≐ext (snd In-w) z)
    (snd (snd pair-in-v z) (injl (≐trans z (pred w x) (pred v x') d₁ xx')))
  lem₂ z (injr d₂) = fst (≐ext (snd In-w) z)
    (snd (snd pair-in-v z) (injr (≐trans z (pred w y) (pred v y') d₂ yy')))

-- sglt a corresponds to {a}

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

×𝕍₁ : {a b x : 𝕍} → x ∈ (a ×𝕍 b) → ∃𝕧∈ a λ v → ∃𝕧∈ b λ w → x ≐ ⟨ v , w ⟩
×𝕍₁ {a}{b}{x} d = fst (fst d) , snd (fst d) , snd d


-- Union Axiom and some notions and lemmas concerning the axiom

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

_⊧Union : 𝕍 → Set₁
w ⊧Union = ∀𝕧∈ w λ a → ∃𝕧∈ w λ c → (x : 𝕍) → x ∈ c ↔ ∃𝕧∈ a (λ v → x ∈ v)

inv-Union : isInv λ v → v ⊧Union
inv-Union {v}{w} p e x = fst In-w , λ z → lem₁ z , lem₂ z
  where
  x' : index v
  x' = fst (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  xx' : pred w x ≐ pred v x'
  xx' = snd (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  uni-in-v : ∃𝕧∈ v λ c → (z : 𝕍) → z ∈ c ↔ ∃𝕧∈ (pred v x') (λ v' → z ∈ v')
  uni-in-v = e x'

  In-w : pred v (fst uni-in-v) ∈ w
  In-w = fst (≐ext p (pred v (fst uni-in-v))) (fst uni-in-v , ≐refl (pred v (fst uni-in-v)))

  inw≐inv : pred w (fst In-w) ≐ pred v (fst uni-in-v)
  inw≐inv = ≐sym (pred v (fst uni-in-v)) (pred w (fst In-w)) (snd In-w)

  lem₁ : (z : 𝕍) → z ∈ pred w (fst In-w) → ∃𝕧∈ (pred w x) (λ w' → z ∈ w')
  lem₁ z d = fst sublem₁ ,
    fst (≐ext (snd sublem₁) z) (snd (fst (snd uni-in-v z) (fst (≐ext inw≐inv z) d)))
    where
    idx : index (pred v x')
    idx = fst (fst (snd uni-in-v z) (fst (≐ext inw≐inv z) d))

    sublem₁ : pred (pred v x') idx ∈ pred w x
    sublem₁ = fst (≐ext (≐sym (pred w x) (pred v x') xx') (pred (pred v x') idx))
      (idx , ≐refl (pred (pred v x') idx))

  lem₂ : (z : 𝕍) → ∃𝕧∈ (pred w x) (λ w' → z ∈ w') → z ∈ pred w (fst In-w)
  lem₂ z (u , d) = fst (≐ext (≐sym (pred w (fst In-w)) (pred v (fst uni-in-v)) inw≐inv) z) sublem₃
    where
    sublem₂ : pred (pred w x) u ∈ pred v x'
    sublem₂ = fst (≐ext xx' (pred (pred w x) u)) (u , ≐refl (pred (pred w x) u))

    sublem₃ : z ∈ pred v (fst uni-in-v)
    sublem₃ = snd (snd uni-in-v z) (fst sublem₂ , fst (≐ext (snd sublem₂) z) d)


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


-- Separation Axiom and the notions and lemmas concerning the axiom

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
  ∃𝕧∈ w λ b → (x : 𝕍) → x ∈ b ↔ (x ∈ a × F x)

inv-Sep : isInv λ v → v ⊧Sep
inv-Sep {v}{w} p e F F-inv x = fst In-w , λ z → lem₁ z , lem₂ z
  where
  x' : index v
  x' = fst (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  xx' : pred w x ≐ pred v x'
  xx' = snd (snd (≐ext p (pred w x)) (x , ≐refl (pred w x)))

  sep-in-v : ∃𝕧∈ v λ b → (z : 𝕍) → z ∈ b ↔ (z ∈ (pred v x') × F z)
  sep-in-v = e F F-inv x'

  In-w : pred v (fst sep-in-v) ∈ w
  In-w = fst (≐ext p (pred v (fst sep-in-v))) (fst sep-in-v , ≐refl (pred v (fst sep-in-v)))

  inw≐inv : pred w (fst In-w) ≐ pred v (fst sep-in-v)
  inw≐inv = ≐sym (pred v (fst sep-in-v)) (pred w (fst In-w)) (snd In-w)

  lem₁ : (z : 𝕍) → (z ∈ pred w (fst In-w)) → (z ∈ (pred w x) × F z)
  lem₁ z (u , d) = snd (≐ext xx' z) (fst sublem₁) , snd sublem₁
    where
    sublem₁ : z ∈ (pred v x') × F z
    sublem₁ = fst (snd sep-in-v z) (fst (≐ext inw≐inv z) (u , d))

  lem₂ : (z : 𝕍) → (z ∈ (pred w x) × F z) → (z ∈ pred w (fst In-w))
  lem₂ z (d₁ , d₂) = snd (≐ext inw≐inv z) (snd (snd sep-in-v z) (fst (≐ext xx' z) d₁ , d₂))


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
c ⊧StrColl = {F : 𝕍 → 𝕍 → Set} → ∀𝕧∈ c (λ a → (∀𝕧∈ a λ v → ∃𝕧∈ c λ w → F v w) →
  ∃𝕧∈ c λ b → (∀𝕧∈ a λ v → ∃𝕧∈ b λ w → F v w) × (∀𝕧∈ b λ w → ∃𝕧∈ a λ v → F v w))

-- Subset Collection

SubColl : {ℓ : Level} {F : (v w u : 𝕍) → Set ℓ} → (a b : 𝕍) →
  Σ 𝕍 λ c → (u : 𝕍) → ∀𝕧∈ a (λ v → ∃𝕧∈ b (λ w → F v w u)) →
    ∃𝕧∈ c λ d → ∀𝕧∈ a (λ v → ∃𝕧∈ d (λ w → F v w u)) × ∀𝕧∈ d (λ w → ∃𝕧∈ a (λ v → F v w u))
SubColl {F = F} a b = sup (index a → index b) (λ f → sup (index a) λ x → pred b (f x)) ,
  λ u e → (λ x → fst (e x)) , (λ x → x , snd (e x)) , (λ x → x , snd (e x))

_⊧SubColl : 𝕍 → Set₁
z ⊧SubColl = {F : (v w u : 𝕍) → Set} → ∀𝕧∈ z λ a → ∀𝕧∈ z λ b → ∃𝕧∈ z λ c →
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


-- Infinity Axiom and some notions and lemmas concerning the axiom

∅ : 𝕍
∅ = sup ⊥ (⊥elim λ _ → 𝕍)

suc𝕍 : 𝕍 → 𝕍
suc𝕍 a = sup (index a ⊕ ⊤) λ x → ⊕elim' (λ _ → 𝕍) (λ y → pred a y) (λ z → a) x

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

-- the transfinite induction principles for transitive closures of sets

∈-tcTI : {ℓ : Level} {F : 𝕍 → Set ℓ} →
          ((a : 𝕍) → (∀𝕧∈ (tc a) λ v → F v) → F a) → (a : 𝕍) → F a
∈-tcTI {ℓ}{F} e (sup A f) = e (sup A f) ∈-tcTI-lem
  where
  F' : 𝕍 → Set ℓ
  F' a = ∀𝕧∈ (tc a) λ v → F v

  ∈-tcTI-lem : (x : A ⊕ Σ A (λ y → index (tc (f y)))) → F (pred (tc (sup A f)) x)
  ∈-tcTI-lem (injl x) = ∈-tcTI e (f x)
  ∈-tcTI-lem (injr (y , c)) = ∈-tcTI {F = F'}
    (λ a d z → e (pred (tc a) z) (d z)) (f y) c


-- the notion of CZF model

_⊧CZF : 𝕍 → Set₁
a ⊧CZF = a ⊧SetInd × (a ⊧Pairs) × (a ⊧Union) × (a ⊧Sep) ×
  (a ⊧StrColl) × (a ⊧SubColl) × (a ⊧Infty)
