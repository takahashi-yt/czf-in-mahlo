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


postulate
  V-REA : V a t c ⊧REA
