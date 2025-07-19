{-# OPTIONS --cubical-compatible #-}

module RegularExtensionAxiom where

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
open import TypeHierarchy
open import IterativeSetHierarchy


-- TODO: validate REA

isRegular : 𝕍 → Set₁
isRegular a = (Σ 𝕍 (λ v → v ∈ a)) × (isTransitive a) ×
                ∀𝕧∈ a λ v → (R : 𝕍) →
                  (R ⊆ (v ×𝕍 a) × ∀𝕧∈ v λ x → ∃𝕧∈ a λ y → ⟨ x , y ⟩ ∈ R) →
                    ∃𝕧∈ a λ w →
                      (∀𝕧∈ v λ x → ∃𝕧∈ w λ y → ⟨ x , y ⟩ ∈ R) ×
                      (∀𝕧∈ w λ y → ∃𝕧∈ v λ x → ⟨ x , y ⟩ ∈ R)


-- Regular Extension Axiom

_⊧REA : (v : 𝕍) → Set₁
v ⊧REA = ∀𝕧∈ v λ x → ∃𝕧∈ v λ y → x ⊆ y × isRegular y


private variable
  a : 𝕍
  t : Acc a
  c : 𝔽 0


V-inhabited : Σ 𝕍 λ v → v ∈ V a t c
V-inhabited {a} {prog f} {c} = ∅ , ∅V̂ a (prog f) c , ⊥elim C₁ , ⊥elim C₂
  where
  C₁ : ⊥ → Set
  C₁ = λ x → Σ ⊥
         (λ y →
           ⊥elim (λ _ → 𝕍) x ≐
           h a (prog f) c (⊥elim (λ _ → V̂ a (prog f) c) y))
  C₂ : ⊥ → Set
  C₂ = λ y → Σ ⊥
         (λ x →
           ⊥elim (λ _ → 𝕍) x ≐
           h a (prog f) c (⊥elim (λ _ → V̂ a (prog f) c) y))


relationInv : {v₁ v₂ w₁ w₂ : 𝕍} → (R : 𝕍) → v₁ ≐ v₂ → w₁ ≐ w₂ → ⟨ v₁ , w₁ ⟩ ∈ R → ⟨ v₂ , w₂ ⟩ ∈ R
relationInv {v₁ = v₁} {v₂ = v₂} {w₁ = w₁} {w₂ = w₂} R p q d =
  ExtAx1 {x = R} (snd OPairAx (p , q)) d

-- V a t c is regular

V-regular : isRegular (V a t c)
V-regular {a} {prog f} {c} = (V-inhabited , V-trans) ,
  λ v R d → let
            F : V̂ a (prog f) c → V̂ a (prog f) c → Set
            F x y = ⟨ h a (prog f) c x , h a (prog f) c y ⟩ ∈ R

            lem₁ : (x : V̂ a (prog f) c) → T̂ a (prog f) c (∈' a (prog f) c x v) → Σ (V̂ a (prog f) c) λ y → F x y
            lem₁ = λ x e → fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {x} {v}) e))) ,
                           ExtAx1 {⟨ pred (h a (prog f) c v) (fst (fst (h∈-iso {a} {prog f} {c} {x} {v}) e)) ,
                                     h a (prog f) c (fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {x} {v}) e)))) ⟩}
                                  {⟨ h a (prog f) c x ,
                                     h a (prog f) c (fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {x} {v}) e)))) ⟩}
                                  {R}
                                  (snd OPairAx (≐sym (h a (prog f) c x)
                                                     (pred (h a (prog f) c v) (fst (fst (h∈-iso {a} {prog f} {c} {x} {v}) e)))
                                                     (snd (fst (h∈-iso {a} {prog f} {c} {x} {v}) e)) ,
                                                ≐refl (h a (prog f) c (fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {x} {v}) e)))))))
                                  (snd (snd d (fst (fst (h∈-iso {a} {prog f} {c} {x} {v}) e))))
            lem₂ : Σ (V̂ a (prog f) c) (λ w →
                                        ((x : V̂ a (prog f) c) → T̂ a (prog f) c (∈' a (prog f) c x v) →
                                          Σ (V̂ a (prog f) c) λ y → T̂ a (prog f) c (∈' a (prog f) c y w) × F x y)
                                          ×
                                        ((y : V̂ a (prog f) c) → T̂ a (prog f) c (∈' a (prog f) c y w) →
                                          Σ (V̂ a (prog f) c) λ x → T̂ a (prog f) c (∈' a (prog f) c x v) × F x y))
            lem₂ = StrCollV̂Set {a} {prog f} {c} {F = F} {v = v}
                                (λ w₁ p → relationInv R (fst (h-iso {a} {prog f} {c}) p) (≐refl (h a (prog f) c w₁)))
                                (λ v₁ q → relationInv R (≐refl (h a (prog f) c v₁)) (fst (h-iso {a} {prog f} {c}) q))
                                lem₁
            lem₃ : (x : index (h a (prog f) c v)) → Σ (index (h a (prog f) c v) → T̂ a (prog f) c (index v))
                                                       λ g → T̂ a (prog f) c (∈' a (prog f) c (pred v (g x)) v)
            lem₃ x = (λ x₁ → fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                   (≐'eta {a} {prog f} {c} v)) x₁)) ,
                               fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                     (≐'eta {a} {prog f} {c} v)) x) ,
                               ≐'refl {a} {prog f} {c} (pred v (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                                                      (≐'eta {a} {prog f} {c} v)) x)))
            in fst lem₂ ,
                 (λ x → fst (fst (snd (fst (snd lem₂)
                                             (pred v (fst (snd (lem₃ x))))
                                                   (fst (ip-compat (fst (h-iso  {a} {prog f} {c} {v} {sup (index v) (pred v)}) (≐'eta {a} {prog f} {c} v)) x) ,
                                                ≐'refl {a} {prog f} {c}
                                                       (pred v (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                                                      (≐'eta {a} {prog f} {c} v)) x))))))) ,
                        ExtAx1 {x = R}
                               (snd OPairAx (≐sym (pred (h a (prog f) c v) x)
                                                  (h a (prog f) c (pred v (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                    (≐'eta {a} {prog f} {c} v)) x))))
                                                  (snd (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)}) (≐'eta {a} {prog f} {c} v)) x)) ,
                                             ≐refl (h a (prog f) c (fst (snd d (fst
                                               (fst (h∈-iso {a} {prog f} {c} {pred v (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                 (≐'eta {a} {prog f} {c} v)) x))} {v})
                                                   (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)}) (≐'eta {a} {prog f} {c} v)) x) ,
                                                    ≐'refl {a} {prog f} {c} (pred v (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                      (≐'eta {a} {prog f} {c} v)) x)))))))))))
                               (snd (snd (fst (snd lem₂)
                                 (pred v (fst (snd (lem₃ x))))
                                   (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)}) (≐'eta {a} {prog f} {c} v)) x) ,
                                    ≐'refl {a} {prog f} {c} (pred v (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                      (≐'eta {a} {prog f} {c} v)) x)))))))) ,
                  λ y → fst (fst (h∈-iso {a} {prog f} {c} {pred v y} {v})
                          (fst (snd (snd (snd lem₂) (fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {pred v y} {v})
                            (y , ≐'refl {a} {prog f} {c} (pred v y))))))
                              (y , ≐'refl {a} {prog f} {c} (fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {pred v y} {v})
                                (y , ≐'refl {a} {prog f} {c} (pred v y))))))))))) ,
                        ExtAx1 {x = R}
                                (snd OPairAx (snd (fst (h∈-iso {a} {prog f} {c} {pred v y} {v})
                                               (fst (snd (snd (snd lem₂) (fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {pred v y} {v})
                                                 (y , ≐'refl {a} {prog f} {c} (pred v y))))))
                                                   (y , ≐'refl {a} {prog f} {c} (fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {pred v y} {v})
                                                     (y , ≐'refl {a} {prog f} {c} (pred v y))))))))))) ,
                                              ≐refl (h a (prog f) c (fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {pred v y} {v})
                                                (y , ≐'refl {a} {prog f} {c} (pred v y)))))))))
                                (snd (snd (snd (snd lem₂) (fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {pred v y} {v})
                                  (y , ≐'refl {a} {prog f} {c} (pred v y))))))
                                    (y , ≐'refl {a} {prog f} {c} (fst (snd d (fst (fst (h∈-iso {a} {prog f} {c} {pred v y} {v})
                                      (y , ≐'refl {a} {prog f} {c} (pred v y))))))))))


-- the transitive closure on V̂ a t c

tcV̂ : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → V̂ a t c → V̂ a t c
tcV̂ a t c (sup z f) = ∪bV̂ a t c (sup z f) (∪V̂ a t c (sup z (λ x → tcV̂ a t c (f x))))

TcAxV̂ : (v x : V̂ a t c) → T̂ a t c (∈' a t c x (tcV̂ a t c v)) ↔
                          T̂ a t c (small⊕ a t c (∈' a t c x v)
                                                (∈' a t c x (∪V̂ a t c (sup (index v) λ y → tcV̂ a t c (pred v y)))))
TcAxV̂ {a} {t} {c} (sup z f) x = ∪bV̂-proof {a} {t} {c} (sup z f) (∪V̂ a t c (sup z λ y → tcV̂ a t c (f y))) x


-- V a t c validates Regular Extension Axiom

-- we first show that V a t c is closed under the transitive closure

-- h a t c is compatible with the singleton operator

h-compatible-sglt : (v : V̂ a t c) → h a t c (sgltV̂ a t c v) ≐ sglt (h a t c v)
h-compatible-sglt {a} {prog f} {c} v =
  (λ _ → tt , ≐refl (h a (prog f) c v)) , λ _ → tt , ≐refl (h a (prog f) c v)

-- h a t c is compatible with the binary union operator

h-compatible-∪b : (v w : V̂ a t c) → h a t c (∪bV̂ a t c v w) ≐ (h a t c v) ∪b (h a t c w)
h-compatible-∪b {a} {prog g} {c} (sup x₁ f₁) (sup x₂ f₂) =
  ExtAx2' λ x → →proof x  ,
                ←proof x
  where
  →proof : (x : 𝕍) → x ∈ h a (prog g) c (∪bV̂ a (prog g) c (sup x₁ f₁) (sup x₂ f₂)) →
                       x ∈ ((h a (prog g) c (sup x₁ f₁)) ∪b (h a (prog g) c (sup x₂ f₂)))
  →proof x (injl y₁ , p) = snd (∪b-proof (h a (prog g) c (sup x₁ f₁)) (h a (prog g) c (sup x₂ f₂)) x)
                             (injl (y₁ , p))
  →proof x (injr y₂ , p) = snd (∪b-proof (h a (prog g) c (sup x₁ f₁)) (h a (prog g) c (sup x₂ f₂)) x)
                             (injr (y₂ , p))

  ←proof : (x : 𝕍) → x ∈ ((h a (prog g) c (sup x₁ f₁)) ∪b (h a (prog g) c (sup x₂ f₂))) →
                       x ∈ h a (prog g) c (∪bV̂ a (prog g) c (sup x₁ f₁) (sup x₂ f₂))
  ←proof x (injl y₁ , p) = injl y₁ , p
  ←proof x (injr y₂ , p) = injr y₂ , p

-- h a t c is compatible with the union operator

h-compatible-∪ : (v : V̂ a t c) → h a t c (∪V̂ a t c v) ≐ ∪ (h a t c v)
h-compatible-∪ {a} {prog g} {c} (sup z f) =
  ExtAx2' λ x → (λ d → let p : h a (prog g) c (pred (f (fst (fst d))) (snd (fst d))) ≐ x
                           p = ≐sym x (h a (prog g) c (pred (f (fst (fst d))) (snd (fst d)))) (snd d)

                           lem : h a (prog g) c (pred (f (fst (fst d))) (snd (fst d))) ∈
                                   h a (prog g) c (f (fst (fst d)))
                           lem = fst (h∈-iso {a} {prog g} {c}
                                             {pred (f (fst (fst d))) (snd (fst d))} {f (fst (fst d))})
                                       (snd (fst d) ,
                                        ≐'refl {a} {prog g} {c} (pred (f (fst (fst d))) (snd (fst d))))
                       in snd (∪-proof (h a (prog g) c (sup z f)) x)
                                (fst (fst d) ,
                                 ExtAx1 {h a (prog g) c (pred (f (fst (fst d))) (snd (fst d)))}
                                        {x}
                                        {h a (prog g) c (f (fst (fst d)))}
                                        p
                                        lem)) ,
                (λ e → let lem : Σ (T̂ a (prog g) c (index (f (fst (fst e))))) λ j →
                                   pred (h a (prog g) c (f (fst (fst e)))) (snd (fst e)) ≐
                                   h a (prog g) c (pred (f (fst (fst e))) j)
                           lem = h-pred (f (fst (fst e))) (snd (fst e))
                       in (fst (fst e) , fst lem) ,
                           ≐trans x
                                  (pred (h a (prog g) c (f (fst (fst e)))) (snd (fst e)))
                                  (h a (prog g) c (pred (f (fst (fst e))) (fst lem)))
                                  (snd e)
                                  (snd lem))

-- h a t c is compatible with the transitive closure

h-compatible-tc : (v : V̂ a t c) → h a t c (tcV̂ a t c v) ≐ tc (h a t c v)
h-compatible-tc {a} {prog g} {c} (sup z f) =
  ≐trans (h a t' c (tcV̂ a t' c v))
          ((h a t' c v) ∪b (h a t' c (∪V̂ a t' c (sup z λ y → tcV̂ a t' c (f y)))))
          (tc (h a t' c v))
          eq₁
          (≐trans ((h a t' c v) ∪b (h a t' c (∪V̂ a t' c (sup z λ y → tcV̂ a t' c (f y)))))
                  ((h a t' c v) ∪b (∪ (h a t' c (sup z λ y → tcV̂ a t' c (f y)))))
                  (tc (h a t' c v))
                  eq₂
                  eq₃)
  where
  t' : Acc a
  t' = prog g

  v : V̂ a t' c
  v = sup z f
  
  eq₁ : h a t' c (tcV̂ a t' c v) ≐
        (h a t' c v) ∪b (h a t' c (∪V̂ a t' c (sup z λ y → tcV̂ a t' c (f y))))
  eq₁ = h-compatible-∪b v (∪V̂ a t' c (sup z λ y → tcV̂ a t' c (f y)))

  eq₂ : (h a t' c v) ∪b (h a t' c (∪V̂ a t' c (sup z λ y → tcV̂ a t' c (f y)))) ≐
        (h a t' c v) ∪b (∪ (h a t' c (sup z λ y → tcV̂ a t' c (f y))))
  eq₂ = ∪b-cong (≐refl (h a t' c v)) (h-compatible-∪ (sup z λ y → tcV̂ a t' c (f y)))

  eq₃ : (h a t' c v) ∪b (∪ (sup (T̂ a t' c z) λ y → h a t' c (tcV̂ a t' c (f y)))) ≐
        (h a t' c v) ∪b (∪ (sup (T̂ a t' c z) λ y → tc (h a t' c (f y))))  -- equals to tc (h a t' c v) definitionally
  eq₃ = ∪b-cong (≐refl (h a t' c v))
                 (∪-cong (≐cong {T̂ a t' c z}
                                {λ y → h a t' c (tcV̂ a t' c (f y))}
                                {λ y → tc (h a t' c (f y))}
                                λ y → h-compatible-tc (f y)))

-- V a t c is closed under the transitive closure

V-tc : ∀𝕧∈ (V a t c) λ v → tc v ∈ V a t c
V-tc {a} {prog f} {c} i = ExtAx1 {h a (prog f) c (tcV̂ a (prog f) c i)}
                                  {tc (h a (prog f) c i)}
                                  {V a (prog f) c}
                                  (h-compatible-tc i)
                                  (tcV̂ a (prog f) c i , ≐refl (h a (prog f) c (tcV̂ a (prog f) c i)))

-- V a t c validates Regular Extension Axiom

postulate
  V-REA : V a t c ⊧REA
