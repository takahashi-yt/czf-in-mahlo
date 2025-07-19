{-# OPTIONS --cubical-compatible --safe #-}

module TypeHierarchy where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Preliminaries
open import CZFBasics
open import CZFAxioms
open import ExternalMahlo


-- definition of the accessibility predicate

data Acc : 𝕍 → Set₁ where
  prog : {a : 𝕍} → ((x : index (tc a)) → Acc (pred (tc a) x)) → Acc a

-- some useful lemmas for Acc

Acc-inversion : {a : 𝕍} → Acc a → (x : index (tc a)) → Acc (pred (tc a) x)
Acc-inversion (prog f) x = f x

AccIsInv : isInv Acc
AccIsInv {a} {b} p (prog f) = prog λ x →
  AccIsInv (snd (snd (fst ≐logeq (tc-cong' p)) x)) (f (fst (snd (fst ≐logeq (tc-cong' p)) x)))

𝕍⊆Acc : (a : 𝕍) → Acc a
𝕍⊆Acc (sup A f) = prog g
  where
  g : (x : index (tc (sup A f))) → Acc (pred (tc (sup A f)) x)
  g (injl z) = 𝕍⊆Acc (f z)
  g (injr w) = Acc-inversion (𝕍⊆Acc (f (fst w))) (snd w)


-- the iterator ϕ of u𝕄 along a given iterative set a and its accessibility proof t : Acc a

ϕ : (a : 𝕍) → Acc a → 𝕆 1
ϕ a (prog f) = u𝕄 (index (tc a) , λ x → ϕ (pred (tc a) x) (f x))


-- the a-th subuniverse Û a t c of the external Mahlo universe with the decoding function T̂ a t c
-- for any a : 𝕍, t : Acc a, and c : 𝔽 0
--
-- Û a t c is a universe constructed by iterating ϕ along a and t

Û : (a : 𝕍) → (t : Acc a) → 𝔽 0 → Set
Û a t c = fst (ϕ a t c)

T̂ : (a : 𝕍) → (t : Acc a) → (c : 𝔽 0) → Û a t c → Set
T̂ a t c x = snd (ϕ a t c) x

codeForFamSets : (a : 𝕍) → (t : Acc a) → (c : 𝔽 0) → (z : fst c) →
                    Σ (Û a t c) (λ x → T̂ a t c x ≡ snd c z)
codeForFamSets a (prog f) c z = code₂ (code⊥ , ⊥elim (λ _ → Û a (prog f) c)) (injl (injl (injr z))) , refl


-- the type V̂ a t c of iterative sets on the a-th subuniverse Û a t c

V̂ : (a : 𝕍) → (t : Acc a) → (c : 𝔽 0) → Set
V̂ a t c = W (Û a t c) (T̂ a t c)

∀𝕧∈' : (a : 𝕍) (t : Acc a) (c : 𝔽 0) →
         V̂ a t c → (V̂ a t c → Û a t c) → Û a t c
∀𝕧∈' a (prog f) c v B = codeΠ (index v) λ x → B (pred v x)

∃𝕧∈' : (a : 𝕍) (t : Acc a) (c : 𝔽 0) →
         V̂ a t c → (V̂ a t c → Û a t c) → Û a t c
∃𝕧∈' a (prog f) c v B = codeΣ (index v) λ x → B (pred v x)

small× : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → Û a t c → Û a t c → Û a t c
small× a (prog f) c A B = codeΣ A λ _ → B

small⊕ : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → Û a t c → Û a t c → Û a t c
small⊕ a (prog f) c A B = codeS A B


-- the equality on V̂ a t c

≐' : (a : 𝕍) (t : Acc a) (c : 𝔽 0) (v w : V̂ a t c) → Û a t c
≐' a (prog f) c (sup b₁ g₁) (sup b₂ g₂) = codeΣ (codeΠ b₁ λ x → codeΣ b₂ λ y → ≐' a (prog f) c (g₁ x) (g₂ y))
                                                 λ _ → codeΠ b₂ λ y → codeΣ b₁ λ x → ≐' a (prog f) c (g₁ x) (g₂ y)

private variable
  a : 𝕍
  t : Acc a
  c : 𝔽 0

≐'refl : (b : V̂ a t c) → T̂ a t c (≐' a t c b b)
≐'refl {a} {prog g} {c} (sup x f) = (λ y → y , ≐'refl {a} {prog g} {c} (f y)) ,
                                    (λ z → z , ≐'refl {a} {prog g} {c} (f z))

≐'sym : (v w : V̂ a t c) → T̂ a t c (≐' a t c v w) → T̂ a t c (≐' a t c w v)
≐'sym {a} {prog h} {c} (sup x f) (sup y g) p =
  (λ y₁ → fst (snd p y₁) , ≐'sym {a} {prog h} {c} (f (fst (snd p y₁))) (g y₁) (snd (snd p y₁))) ,
  (λ x₁ → fst (fst p x₁) , ≐'sym {a} {prog h} {c} (f x₁) (g (fst (fst p x₁))) (snd (fst p x₁)))

≐'trans : (b v w : V̂ a t c) →  T̂ a t c (≐' a t c b v) → T̂ a t c (≐' a t c v w) → T̂ a t c (≐' a t c b w)
≐'trans {a} {prog l} {c} (sup x f) (sup y g) (sup z h) (d₁ , d₂) (e₁ , e₂) =
  (λ x₁ → fst (e₁ (fst (d₁ x₁))) ,
    ≐'trans {a} {prog l} {c} (f x₁) (g (fst (d₁ x₁))) (h (fst (e₁ (fst (d₁ x₁)))))
      (snd (d₁ x₁)) (snd (e₁ (fst (d₁ x₁))))) ,
  λ y₁ → fst (d₂ (fst (e₂ y₁))) ,
    ≐'trans {a} {prog l} {c} (f (fst (d₂ (fst (e₂ y₁))))) (g (fst (e₂ y₁))) (h y₁)
      (snd (d₂ (fst (e₂ y₁)))) (snd (e₂ y₁))

≐'eta : (b : V̂ a t c) → T̂ a t c (≐' a t c b (sup (index b) (pred b)))
≐'eta {a} {prog g} {c} (sup x f) = (λ y → y , ≐'refl {a} {prog g} {c} (f y)) ,
                                   (λ z → z , ≐'refl {a} {prog g} {c} (f z))

≐'bisim : {v w : V̂ a t c} → T̂ a t c (≐' a t c v w) →
            T̂ a t c (∀𝕧∈' a t c v λ x → ∃𝕧∈' a t c w λ y → ≐' a t c x y) ×
            T̂ a t c (∀𝕧∈' a t c w λ y → ∃𝕧∈' a t c v λ x → ≐' a t c x y)
≐'bisim {a} {prog h} {c} {sup x₁ f} {sup y₁ g} p =
  (λ x → fst (fst p x) , snd (fst p x)) , λ y → fst (snd p y) , snd (snd p y)


-- the membership relation on V̂ a t c

∈' : (a : 𝕍) (t : Acc a) (c : 𝔽 0) (v w : V̂ a t c) → Û a t c
∈' a (prog f) c v w = codeΣ (index w) λ x → ≐' a (prog f) c v (pred w x)

ExtAll' : {F : V̂ a t c → Û a t c} →
            ((z₁ : V̂ a t c) → T̂ a t c (F z₁) → (z₂ : V̂ a t c) → T̂ a t c (≐' a t c z₂ z₁) → T̂ a t c (F z₂)) →
              (v : V̂ a t c) → T̂ a t c (∀𝕧∈' a t c v F) ↔ ((w : V̂ a t c) → T̂ a t c (∈' a t c w v) → T̂ a t c (F w))
ExtAll' {a} {prog h} {c} {F} All-ext (sup x f) =
  (λ g w d → All-ext (f (fst d)) (g (fst d)) w (snd d)) ,
  (λ e x₁ → e (f x₁) (x₁ , ≐'refl {a} {prog h} {c} (f x₁)))

ExtEx' : {F : V̂ a t c → Û a t c} →
           ((z₁ : V̂ a t c) → T̂ a t c (F z₁) → (z₂ : V̂ a t c) → T̂ a t c (≐' a t c z₂ z₁) → T̂ a t c (F z₂)) →
             (v : V̂ a t c) → T̂ a t c (∃𝕧∈' a t c v F) ↔
                             (Σ (V̂ a t c) λ w → T̂ a t c (small× a t c (∈' a t c w v) (F w)))
ExtEx' {a} {prog h} {c} {F} Ex-ext (sup x f) =
  (λ d → f (fst d) , (fst d , ≐'refl {a} {prog h} {c} (f (fst d))) , snd d) ,
  (λ e → fst (fst (snd e)) ,
         Ex-ext (fst e) (snd (snd e)) (f (fst (fst (snd e))))
                  (≐'sym {a} {prog h} {c} (fst e) (f (fst (fst (snd e)))) (snd (fst (snd e)))))


-- embedding of iterative sets in V̂ a t c into 𝕍

h : (a : 𝕍) → (t : Acc a) → (c : 𝔽 0) → V̂ a t c → 𝕍
h a t c (sup x f) = sup (T̂ a t c x) λ y → h a t c (f y)

h-iso : {v w : V̂ a t c} → T̂ a t c (≐' a t c v w) ↔ (h a t c v ≐ h a t c w)
h-iso {a} {prog h} {c} {v = sup x f} {w = sup y g}  =
  (λ p → (λ x₁ → fst (fst p x₁) , fst h-iso (snd (fst p x₁))) ,
         (λ y₁ → fst (snd p y₁) , fst h-iso (snd (snd p y₁)))) ,
  (λ p → (λ x₁ → fst (fst p x₁) , snd h-iso (snd (fst p x₁))) ,
         (λ y₁ → fst (snd p y₁) , snd h-iso (snd (snd p y₁))))

h∈-iso : {v w : V̂ a t c} → T̂ a t c (∈' a t c v w) ↔ h a t c v ∈ h a t c w
h∈-iso {a} {prog h} {c} {sup x f} {sup y g} =
  (λ d → fst d , fst h-iso (snd d)) , (λ d → fst d , snd h-iso (snd d))

h-iso⊕ : {x y v w : V̂ a t c} →
            (T̂ a t c (≐' a t c v x) ⊕ T̂ a t c (≐' a t c w y)) ↔ ((h a t c v ≐ h a t c x) ⊕ (h a t c w ≐ h a t c y))
h-iso⊕ {a} {t} {c} {x} {y} {v} {w} = ⊕elim (λ _ → (h a t c v ≐ h a t c x) ⊕ (h a t c w ≐ h a t c y))
                                           (λ d₁ → injl (fst h-iso d₁))
                                           (λ d₂ → injr (fst h-iso d₂)) ,
                                     ⊕elim (λ _ → T̂ a t c (≐' a t c v x) ⊕ T̂ a t c (≐' a t c w y))
                                           (λ d₁ → injl (snd h-iso d₁))
                                           (λ d₂ → injr (snd h-iso d₂))

h-index : (v : V̂ a t c) → index (h a t c v) ≡ T̂ a t c (index v)
h-index {a} {prog g} {c} (sup z f) = refl

h-pred : (v : V̂ a t c) (i : index (h a t c v)) →
           Σ (T̂ a t c (index v)) λ j → pred (h a t c v) i ≐ h a t c (pred v j)
h-pred {a} {prog g} {c} (sup z f) i = i , ≐refl (h a (prog g) c (f i))


-- V̂ a t c validates all axioms of CZF

-- V̂ a t c validates Extensionality Axioms

ExtAx1V̂ : {u v w : V̂ a t c} →
            T̂ a t c (≐' a t c v w) → T̂ a t c (∈' a t c v u) → T̂ a t c (∈' a t c w u)
ExtAx1V̂ {a} {prog f} {c} {u} {v} {w} p d =
  fst d , ≐'trans {a} {prog f} {c} w v (pred u (fst d)) (≐'sym {a} {prog f} {c} v w p) (snd d)

ExtAx2V̂ : {v w : V̂ a t c} → T̂ a t c (≐' a t c v w) → (u : V̂ a t c) →
            T̂ a t c (∈' a t c u v) ↔ T̂ a t c (∈' a t c u w)
ExtAx2V̂ {a} {prog h} {c} {sup x f} {sup y g} p u =
  (λ (x₁ , d₁) → fst (fst p x₁) , ≐'trans {a} {prog h} {c}u (f x₁) (g (fst (fst p x₁))) d₁ (snd (fst p x₁))) ,
   λ (y₂ , d₂) → fst (snd p y₂) , ≐'trans {a} {prog h} {c} u (g y₂) (f (fst (snd p y₂)))
                                    d₂ (≐'sym {a} {prog h} {c} (f (fst (snd p y₂))) (g y₂) (snd (snd p y₂)))

ExtAx2V̂' : {v w : V̂ a t c} →
             ((u : V̂ a t c) → T̂ a t c (∈' a t c u v) ↔ T̂ a t c (∈' a t c u w)) → T̂ a t c (≐' a t c v w)
ExtAx2V̂' {a} {prog l} {c} {sup x f} {sup y g} h =
  (λ x₁ → fst (h (f x₁)) (x₁ , ≐'refl {a} {prog l} {c} (f x₁))) ,
   λ y₁ → fst (snd (h (g y₁)) (y₁ , ≐'refl {a} {prog l} {c} (g y₁))) ,
     ≐'sym {a} {prog l} {c} (g y₁) (f (fst (snd (h (g y₁)) (y₁ , ≐'refl {a} {prog l} {c} (g y₁)))))
       (snd (snd (h (g y₁)) (y₁ , ≐'refl {a} {prog l} {c} (g y₁))))


-- V̂ a t c validates Set Induction Axiom

SetIndV̂ : {F : V̂ a t c → Û a t c} →
            ({z₁ z₂ : V̂ a t c} → T̂ a t c (≐' a t c z₁ z₂) → T̂ a t c (F z₁) → T̂ a t c (F z₂)) →
              ((v : V̂ a t c) → ((w : V̂ a t c) → T̂ a t c (∈' a t c w v) → T̂ a t c (F w)) → T̂ a t c (F v)) →
                (v : V̂ a t c) → T̂ a t c (F v)
SetIndV̂ {a} {prog g} {c} {F} F-inv d (sup x f) =
  d (sup x f) λ w e → F-inv (≐'sym {a} {prog g} {c} w (f (fst e)) (snd e))
                            (SetIndV̂ {a} {prog g} {c} {F} F-inv d (f (fst e)))


-- V̂ a t c validates Pairing Axiom

PairsV̂ : (v w : V̂ a t c) →
           Σ (V̂ a t c) λ b → (x : V̂ a t c) →
                               T̂ a t c (∈' a t c x b) ↔ (T̂ a t c (small⊕ a t c (≐' a t c x v) (≐' a t c x w)))
PairsV̂ {a} {prog f} {c} v w = sup codeB (Boolelim (λ _ → V̂ a (prog f) c) w v) ,
                              λ x → (λ (z , e) → pair-prf₁ x z e) ,
                                    pair-prf₂ x
  where
  pair-prf₁ : (a₁ : V̂ a (prog f) c) (i : Bool) → (T̂ a (prog f) c (≐' a (prog f) c a₁ (Boolelim (λ _ → V̂ a (prog f) c) w v i))) →
                (T̂ a (prog f) c (≐' a (prog f) c a₁ v) ⊕ T̂ a (prog f) c (≐' a (prog f) c a₁ w))
  pair-prf₁ a₁ false d = injl d
  pair-prf₁ a₁ true d  = injr d

  pair-prf₂ : (a₁ : V̂ a (prog f) c) →
                T̂ a (prog f) c (≐' a (prog f) c a₁ v) ⊕ T̂ a (prog f) c (≐' a (prog f) c a₁ w) →
                  T̂ a (prog f) c (∈' a (prog f) c a₁ (sup codeB (Boolelim (λ _ → V̂ a (prog f) c) w v)))
  pair-prf₂ a₁ (injl d) = false , d
  pair-prf₂ a₁ (injr d) = true , d

-- pair-setV̂ a t c v w corresponds to {v , w} in V̂ a t c

pair-setV̂ : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → V̂ a t c → V̂ a t c → V̂ a t c
pair-setV̂ a t c v w = fst (AC λ (v' , w') → PairsV̂ {a} {t} {c} v' w') (v , w)

pair-set-proofV̂ : (v w x : V̂ a t c) →
                    T̂ a t c (∈' a t c x (pair-setV̂ a t c v w)) ↔
                    (T̂ a t c (≐' a t c x v) ⊕ T̂ a t c (≐' a t c x w))
pair-set-proofV̂ {a} {prog f} {c} v w = snd (AC λ (v' , w') → PairsV̂ {a} {prog f} {c} v' w') (v , w)

-- sgltV̂ a t c v corresponds to { v } in V̂ a t c

sgltV̂ : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → V̂ a t c → V̂ a t c
sgltV̂ a (prog f) c v = sup code⊤ λ _ → v

-- ordered-pair a t c v w correponds to ⟨ v , w ⟩ in V̂ a t c

ordered-pair : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → V̂ a t c → V̂ a t c → V̂ a t c
ordered-pair a t c v w = pair-setV̂ a t c (sgltV̂ a t c v) (pair-setV̂ a t c v w)


-- V̂ a t c validates Union Axiom

UnionV̂ : (v : V̂ a t c) →
           Σ (V̂ a t c) λ w → (x : V̂ a t c) →
                               T̂ a t c (∈' a t c x w) ↔
                                 Σ (V̂ a t c) λ y → T̂ a t c (small× a t c (∈' a t c y v) (∈' a t c x y))
UnionV̂ {a} {prog g} {c} (sup z f) = sup (codeΣ z λ i → index (f i)) (λ (i , j) → pred (f i) j) ,
                   λ x → (λ ((i , j) , d) → f i , (i , ≐'refl {a} {prog g} {c} (f i)) , j , d) ,
                         (λ (y , (d , e)) →
                            (fst d , fst (fst (≐'bisim {a} {prog g} {c} {y} (snd d)) (fst e))) ,
                             ≐'trans {a} {prog g} {c}
                                      x (pred y (fst e))
                                        (pred (f (fst d))
                                          (fst (fst (≐'bisim {a} {prog g} {c} {y} (snd d)) (fst e))))
                                     (snd e)
                                     (snd (fst (≐'bisim {a} {prog g} {c} {y} (snd d)) (fst e))))

-- the union operator on V̂ a t c

∪V̂ : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → V̂ a t c → V̂ a t c
∪V̂ a t c = fst (AC (UnionV̂ {a} {t} {c}))

∪V̂-proof : (v x : V̂ a t c) → T̂ a t c (∈' a t c x (∪V̂ a t c v)) ↔
                             Σ (V̂ a t c) λ y → T̂ a t c (small× a t c (∈' a t c y v) (∈' a t c x y))
∪V̂-proof {a} {t} {c} v = snd (AC (UnionV̂ {a} {t} {c})) v


-- V̂ a t c validates Binary Union Axiom

UnionBiV̂ : (v w : V̂ a t c) →
             Σ (V̂ a t c) λ u → (x : V̂ a t c) →
                                 T̂ a t c (∈' a t c x u) ↔ T̂ a t c (small⊕ a t c (∈' a t c x v) (∈' a t c x w))
UnionBiV̂ {a} {prog g} {c} (sup z₁ f₁) (sup z₂ f₂) =
  sup (codeS z₁ z₂) f ,
  λ x → (λ (z , p) → unionBi-prf₁ x z p) ,
        unionBi-prf₂ x
    where
    f : T̂ a (prog g) c (codeS z₁ z₂) → V̂ a (prog g) c
    f (injl x₁) = f₁ x₁
    f (injr x₂) = f₂ x₂

    unionBi-prf₁ : (x : V̂ a (prog g) c) (y : T̂ a (prog g) c (codeS z₁ z₂)) →
                     T̂ a (prog g) c (≐' a (prog g) c x (f y)) →
                       T̂ a (prog g) c (small⊕ a (prog g) c (∈' a (prog g) c x (sup z₁ f₁))
                                                           (∈' a (prog g) c x (sup z₂ f₂)))
    unionBi-prf₁ x (injl x₁) p = injl (x₁ , p)
    unionBi-prf₁ x (injr x₂) p = injr (x₂ , p)
    
    unionBi-prf₂ : (x : V̂ a (prog g) c) →
                     T̂ a (prog g) c (small⊕ a (prog g) c (∈' a (prog g) c x (sup z₁ f₁))
                                                         (∈' a (prog g) c x (sup z₂ f₂))) →
                       T̂ a (prog g) c (∈' a (prog g) c x (sup (codeS z₁ z₂) f))
    unionBi-prf₂ x (injl d₁) = injl (fst d₁) , snd d₁
    unionBi-prf₂ x (injr d₂) = injr (fst d₂) , snd d₂

-- the binary union operator on V̂ a t c

∪bV̂ : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → V̂ a t c → V̂ a t c → V̂ a t c
∪bV̂ a t c v w = fst (AC (λ (v , w) → UnionBiV̂ {a} {t} {c} v w)) (v , w)

∪bV̂-proof : (v w x : V̂ a t c) →
              T̂ a t c (∈' a t c x (∪bV̂ a t c v w)) ↔ T̂ a t c (small⊕ a t c (∈' a t c x v) (∈' a t c x w))
∪bV̂-proof {a} {t} {c} v w = snd (AC (λ (v , w) → UnionBiV̂ {a} {t} {c} v w)) (v , w)


-- V̂ a t c validates Separation Axiom

SepAxV̂ : (F : V̂ a t c → Û a t c) →
           ({z₁ z₂ : V̂ a t c} → T̂ a t c (≐' a t c z₁ z₂) → T̂ a t c (F z₁) → T̂ a t c (F z₂)) →
             (v : V̂ a t c) → Σ (V̂ a t c) λ w → (x : V̂ a t c) →
               T̂ a t c (∈' a t c x w) ↔ (T̂ a t c (∈' a t c x v) × T̂ a t c (F x))
SepAxV̂ {a} {prog g} {c} F F-inv (sup z f) =
  (sup (codeΣ z λ x₁ → F (f x₁)) λ y₁ → f (fst y₁)) ,
   λ x → (λ (y , p) → (fst y , p) , F-inv ((≐'sym {a} {prog g} {c} x (f (fst y)) p)) (snd y)) ,
         λ ((y , p) , d) → (y , F-inv p d) , p


-- V̂ a t c validates Strong Collection

StrCollV̂ : {F : V̂ a t c → V̂ a t c → Û a t c} {v : V̂ a t c} →
  ((x : V̂ a t c) → T̂ a t c (∈' a t c x v) → Σ (V̂ a t c) λ y → T̂ a t c (F x y)) →
    Σ (V̂ a t c) λ w →
      T̂ a t c (∀𝕧∈' a t c v λ x → ∃𝕧∈' a t c w λ y → F x y) ×
      T̂ a t c (∀𝕧∈' a t c w λ y → ∃𝕧∈' a t c v λ x → F x y)
StrCollV̂ {a} {prog f} {c} {v = v} d =
  (sup (index v) λ x₁ → fst (d (pred v x₁) (x₁ , ≐'refl {a} {prog f} {c} (pred v x₁)))) ,
  (λ x → x , snd (d (pred v x) (x , ≐'refl {a} {prog f} {c} (pred v x)))) ,
  (λ y → y , snd (d (pred v y) (y , ≐'refl {a} {prog f} {c} (pred v y))))

StrCollV̂Set : {ℓ : Level} {F : V̂ a t c → V̂ a t c → Set ℓ} {v : V̂ a t c} →
  ({v₁ v₂ : V̂ a t c} → (w₁ : V̂ a t c) → T̂ a t c (≐' a t c v₁ v₂) → F v₁ w₁ → F v₂ w₁) →
    ({w₁ w₂ : V̂ a t c} → (v₁ : V̂ a t c) → T̂ a t c (≐' a t c w₁ w₂) → F v₁ w₁ → F v₁ w₂) →
      ((x : V̂ a t c) → T̂ a t c (∈' a t c x v) → Σ (V̂ a t c) λ y → F x y) →
        Σ (V̂ a t c) λ w →
          ((x : V̂ a t c) → T̂ a t c (∈' a t c x v) → Σ (V̂ a t c) λ y → T̂ a t c (∈' a t c y w) × F x y) ×
          ((y : V̂ a t c) → T̂ a t c (∈' a t c y w) → Σ (V̂ a t c) λ x → T̂ a t c (∈' a t c x v) × F x y)
StrCollV̂Set {a} {prog f} {c} {v = v} F-inv1 F-inv2 d =
  sup (index v) (λ x₁ → fst (d (pred v x₁) (x₁ , ≐'refl {a} {prog f} {c} (pred v x₁)))) ,
    (λ x e₁ → fst (d (pred v (fst e₁)) (fst e₁ , ≐'refl {a} {prog f} {c} (pred v (fst e₁)))) ,
                (fst e₁ , ≐'refl {a} {prog f} {c} (fst (d (pred v (fst e₁)) (fst e₁ , ≐'refl {a} {prog f} {c} (pred v (fst e₁)))))) ,
                F-inv1 (fst (d (pred v (fst e₁)) (fst e₁ , ≐'refl {a} {prog f} {c} (pred v (fst e₁)))))
                       (≐'sym {a} {prog f} {c} x (pred v (fst e₁)) (snd e₁))
                       (snd (d (pred v (fst e₁)) (fst e₁ , ≐'refl {a} {prog f} {c} (pred v (fst e₁)))))) ,
     λ y e₂ → pred v (fst e₂) ,
                (fst e₂ , ≐'refl {a} {prog f} {c} (pred v (fst e₂))) ,
                F-inv2 (pred v (fst e₂))
                       (≐'sym {a} {prog f} {c}
                              y
                              (fst (d (pred v (fst e₂)) (fst e₂ , ≐'refl {a} {prog f} {c} (pred v (fst e₂)))))
                              (snd e₂))
                       (snd (d (pred v (fst e₂)) (fst e₂ , ≐'refl {a} {prog f} {c} (pred v (fst e₂)))))


-- V̂ a t c validates Subset Collection

SubCollV̂ : {F : (x y z : V̂ a t c) → Û a t c} →
             (v w : V̂ a t c) → Σ (V̂ a t c) λ u →
               (z : V̂ a t c) → T̂ a t c (∀𝕧∈' a t c v λ x → ∃𝕧∈' a t c w λ y → F x y z) →
                 Σ (V̂ a t c) λ b →
                   T̂ a t c (small× a t c (∈' a t c b u)
                                         (small× a t c (∀𝕧∈' a t c v λ x → ∃𝕧∈' a t c b λ y → F x y z)
                                                       (∀𝕧∈' a t c b λ y → ∃𝕧∈' a t c v λ x → F x y z)))
SubCollV̂ {a} {prog g} {c} {F} v w =
  let u : V̂ a (prog g) c
      u = sup (codeΠ (index v) λ _ → index w) (λ f → sup (index v) λ x₁ → pred w (f x₁))
  in u , λ z d → pred u (λ z₁ → fst (d z₁)) , ((λ z₁ → fst (d z₁)) ,
                                               ≐'refl {a} {prog g} {c} (pred u (λ z₁ → fst (d z₁)))) ,
       (λ x₁ → x₁ , snd (d x₁)) ,
       (λ y₁ → y₁ , snd (d y₁))


-- V̂ a t c validates Infinity Axiom

∅V̂ : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → V̂ a t c
∅V̂ a (prog f) c = sup code⊥ (⊥elim λ _ → V̂ a (prog f) c)

sucV̂ : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → V̂ a t c → V̂ a t c
sucV̂ a (prog f) c v =
  sup (codeS (index v) code⊤) (⊕elim (λ _ → V̂ a (prog f) c) (λ y → pred v y) (λ z → v))

∅V̂-is-empty : (v : V̂ a t c) → T̂ a t c (∈' a t c v (∅V̂ a t c)) ↔ ⊥
∅V̂-is-empty {a} {prog f} {c} v =
  (λ c → fst c) , λ x → ⊥elim (λ _ → T̂ a (prog f) c (∈' a (prog f) c v (∅V̂ a (prog f) c))) x

sucV̂Ax : (v x : V̂ a t c) → T̂ a t c (∈' a t c x (sucV̂ a t c v)) ↔ T̂ a t c (small⊕ a t c (∈' a t c x v) (≐' a t c x v))
sucV̂Ax {a} {prog f} {c} v x = sucV̂Axlem₁ , sucV̂Axlem₂ 
  where
  sucV̂Axlem₁ : T̂ a (prog f) c (∈' a (prog f) c x (sucV̂ a (prog f) c v)) →
                 T̂ a (prog f) c (small⊕ a (prog f) c (∈' a (prog f) c x v) (≐' a (prog f) c x v))
  sucV̂Axlem₁ (injl y , c₂) = injl (y , c₂)
  sucV̂Axlem₁ (injr y , c₂) = injr c₂

  sucV̂Axlem₂ : T̂ a (prog f) c (small⊕ a (prog f) c (∈' a (prog f) c x v) (≐' a (prog f) c x v)) →
                 T̂ a (prog f) c (∈' a (prog f) c x (sucV̂ a (prog f) c v))
  sucV̂Axlem₂ (injl y) = injl (fst y) , snd y
  sucV̂Axlem₂ (injr y) = injr tt , y

sucV̂-compat : (v w : V̂ a t c) → T̂ a t c (≐' a t c v w) → T̂ a t c (≐' a t c (sucV̂ a t c v) (sucV̂ a t c w))
sucV̂-compat {a} {prog h} {c} (sup x f) (sup y g) p =
  sucV̂-compat-lem₁ , sucV̂-compat-lem₂
  where
  sucV̂-compat-lem₁ : T̂ a (prog h) c (∀𝕧∈' a (prog h) c (sucV̂ a (prog h) c (sup x f))
    (λ v₁ → ∃𝕧∈' a (prog h) c (sucV̂ a (prog h) c (sup y g)) (λ w₁ → ≐' a (prog h) c v₁ w₁)))
  sucV̂-compat-lem₁ (injl x) = injl (fst (fst p x)) , snd (fst p x)
  sucV̂-compat-lem₁ (injr x) = injr tt , p

  sucV̂-compat-lem₂ : T̂ a (prog h) c (∀𝕧∈' a (prog h) c (sucV̂ a (prog h) c (sup y g))
    (λ w₁ → ∃𝕧∈' a (prog h) c (sucV̂ a (prog h) c (sup x f)) (λ v₁ → ≐' a (prog h) c v₁ w₁)))
  sucV̂-compat-lem₂ (injl x) = injl (fst (snd p x)) , snd (snd p x)
  sucV̂-compat-lem₂ (injr x) = injr tt , p

ωV̂ : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → V̂ a t c
ωV̂ a (prog f) c = sup codeN (Natelim (λ _ → V̂ a (prog f) c) (∅V̂ a (prog f) c) (λ m v → sucV̂ a (prog f) c v))

∅V̂-in-ωV̂ : T̂ a t c (∈' a t c (∅V̂ a t c) (ωV̂ a t c))
∅V̂-in-ωV̂ {a} {prog f} {c} = zero , ≐'refl {a} {prog f} {c} (∅V̂ a (prog f) c)

sucV̂-ωV̂ : (v : V̂ a t c) → T̂ a t c (∈' a t c v (ωV̂ a t c)) → T̂ a t c (∈' a t c (sucV̂ a t c v) (ωV̂ a t c))
sucV̂-ωV̂ {a} {prog f} {c} v d =
  suc (fst d) , sucV̂-compat v (pred (ωV̂ a (prog f) c) (fst d)) (snd d)
