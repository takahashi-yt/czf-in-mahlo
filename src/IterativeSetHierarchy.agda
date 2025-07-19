{-# OPTIONS --cubical-compatible --safe #-}

module IterativeSetHierarchy where

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


private variable
  a : 𝕍
  t : Acc a
  c : 𝔽 0


-- the type V̂ a t c as an iterative set in 𝕍

V : (a : 𝕍) (t : Acc a) (c : 𝔽 0) → 𝕍 
V a t c = sup (V̂ a t c) (h a t c)

V-trans : isTransitive (V a t c)
V-trans {a} {t} {c} v w d e  =
  let Vtrans-lem : v ≐ h a t c (sup (index (fst d)) (pred (fst d)))
      Vtrans-lem = ≐trans v
                          (h a t c (fst d))
                          (h a t c (sup (index (fst d)) (pred (fst d))))
                          (snd d)
                          (fst h-iso (≐'eta {a} {t} {c} (fst d)))
  in pred (fst d) (fst (fst (≐ext Vtrans-lem w) e)) ,
     snd (fst (≐ext Vtrans-lem w) e)


-- V a t c is closed under singleton operation

V-sglt : (x : 𝕍) → x ∈ V a t c → sglt x ∈ V a t c
V-sglt {a} {prog f} {c} x x-in-V =
  let x' : V̂ a (prog f) c
      x' = fst x-in-V
  in (sup code⊤ λ _ → x') , (λ _ → tt , snd x-in-V) , (λ _ → tt , snd x-in-V)

V-sglt' : ∀𝕧∈ (V a t c) λ x → sglt x ∈ V a t c
V-sglt' {a} {prog f} {c} i =
  (sup code⊤ λ _ → i) , (λ _ → tt , ≐refl (h a (prog f) c i)) , λ _ → tt , ≐refl (h a (prog f) c i)
  

-- we show that V a t c validates all axioms of CZF

-- V a t c validates Extensionality Axioms

V-ext : V a t c ⊧ExtAx
V-ext {a} {t} {c} = ((λ v w x p d → fst (h∈-iso {v = w} {w = x})
                                        (ExtAx1V̂ {a} {t} {c} {u = x} {v = v} {w = w} (snd (h-iso) p)
                                                                         (snd (h∈-iso {v = v} {w = x}) d))) ,
                    (λ v w p x → (λ d → fst (h∈-iso {v = x} {w = w})
                                            (fst (ExtAx2V̂ {a} {t} {c} {v = v} {w = w} (snd (h-iso {v = v} {w = w}) p) x)
                                                 (snd (h∈-iso {v = x} {w = v}) d))) ,
                                 λ d → fst (h∈-iso {v = x} {w = v})
                                           (snd (ExtAx2V̂ {a} {t} {c} {v = v} {w = w} (snd (h-iso {v = v} {w = w}) p) x)
                                                (snd (h∈-iso {v = x} {w = w}) d)))) ,
                    λ v w d → fst (h-iso {v = v} {w = w})
                                  (ExtAx2V̂' {a} {t} {c} {v = v} {w = w} λ x →
                                                                          (λ e → snd (h∈-iso {v = x} {w = w})
                                                                                       (fst (d x) (fst (h∈-iso {v = x} {w = v}) e))) ,
                                                                          (λ e → snd (h∈-iso {v = x} {w = v})
                                                                                       (snd (d x) (fst (h∈-iso {v = x} {w = w}) e))))


-- V a t c validates Set Induction Axiom

V-set-ind : V a t c ⊧SetInd
V-set-ind {a} {t} {c} F-inv IH (sup x f) = IH (sup x f) λ z → V-set-ind {a} {t} {c} F-inv IH (f z)

-- a parameterised formulation of models of Set Induction Axiom

[_,_,_]⊧SetInd : (U : Set) (T : U → Set) → 𝕍 → Set₁
[ U , T , w ]⊧SetInd =
  (F : 𝕍 → U) → isInv (λ x → T (F x)) → (∀𝕧∈ w λ a → (∀𝕧∈ a λ v → T (F v)) → T (F a)) → ∀𝕧∈ w λ a → T (F a)

V-set-ind' : [ Û a t c , T̂ a t c , V a t c ]⊧SetInd
V-set-ind' {a} {prog f} {c} F F-inv d =
  let F' : V̂ a (prog f) c → Û a (prog f) c
      F' v = F (h a (prog f) c v)
  in SetIndV̂ {a} {prog f} {c} {F'}
             (λ p d → F-inv (fst (h-iso {a} {prog f} {c}) p) d)
              λ v e → d v λ x → F-inv (≐sym (pred (h a (prog f) c v) x)
                                            (pred (sup (T̂ a (prog f) c (index v)) (λ y → h a (prog f) c (pred v y)))
                                                  (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                                         (≐'eta {a} {prog f} {c} v)) x)))
                                            (snd (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                                   (≐'eta {a} {prog f} {c} v)) x)))
                                      (e (pred v (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                                        (≐'eta {a} {prog f} {c} v)) x)))
                                         (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                                (≐'eta {a} {prog f} {c} v)) x) ,
                                          ≐'refl {a} {prog f} {c} (pred v (fst (ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)})
                                                                                                 (≐'eta {a} {prog f} {c} v)) x)))))


-- V a t c validates Pairing Axiom

V-pairing : V a t c ⊧Pairs
V-pairing {a} {prog f} {c} x y = fst (PairsV̂ {a} {prog f} {c} x y) ,
                                 λ v → (λ d₁ → fst (h-iso⊕ {a} {prog f} {c})
                                                   (fst (snd (PairsV̂ {a} {prog f} {c} x y) v)
                                                        (snd (h∈-iso {a} {prog f} {c} {v}
                                                                     {sup codeB (Boolelim (λ _ → V̂ a (prog f) c) y x)}) d₁))) ,
                                       (λ d₂ → fst (h∈-iso {a} {prog f} {c} {v}
                                                               {sup codeB (Boolelim (λ _ → V̂ a (prog f) c) y x)})
                                                     (snd (snd (PairsV̂ {a} {prog f} {c} x y) v)
                                                       (snd (h-iso⊕ {a} {prog f} {c}) d₂)))


-- V a t c validates Union Axiom

V-union : V a t c ⊧Union
V-union {a} {prog f} {c} x = let lem₁ : (y : V̂ a (prog f) c)
                                          (d : pred (V a (prog f) c) y ∈ pred (V a (prog f) c) (fst (UnionV̂ {a} {prog f} {c} x))) →
                                            h a (prog f) c y ∈
                                              h a (prog f) c (pred x (fst (fst (snd (fst (snd (UnionV̂ {a} {prog f} {c} x) y)
                                                               (snd (h∈-iso {a} {prog f} {c} {y} {fst (UnionV̂ {a} {prog f} {c} x)}) d))))))
                                 lem₁ y d = fst (h∈-iso {a} {prog f} {c} {y}
                                                        {pred x (fst (fst (snd (fst (snd (UnionV̂ {a} {prog f} {c} x) y)
                                                                    (snd (h∈-iso {a} {prog f} {c} {y}
                                                                      {fst (UnionV̂ {a} {prog f} {c} x)}) d)))))})
                                                  (fst (ExtAx2V̂ {a} {prog f} {c}
                                                                {fst (fst (snd (UnionV̂ {a} {prog f} {c} x) y)
                                                                            (snd (h∈-iso {a} {prog f} {c} {y}
                                                                                         {fst (UnionV̂ {a} {prog f} {c} x)}) d))}
                                                                {pred x (fst (fst (snd (fst (snd (UnionV̂ {a} {prog f} {c} x) y)
                                                                                              (snd (h∈-iso {a} {prog f} {c} {y}
                                                                                                           {fst (UnionV̂ {a} {prog f} {c} x)}) d)))))}
                                                                (snd (fst (snd (fst (snd (UnionV̂ {a} {prog f} {c} x) y)
                                                                                      (snd (h∈-iso {a} {prog f} {c} {y}
                                                                                                       {fst (UnionV̂ {a} {prog f} {c} x)}) d))))) y)
                                                         (snd (snd (fst (snd (UnionV̂ {a} {prog f} {c} x) y)
                                                                          (snd (h∈-iso {a} {prog f} {c} {y}
                                                                                       {fst (UnionV̂ {a} {prog f} {c} x)}) d)))))
                                 lem₂ : (y : V̂ a (prog f) c)
                                          (d : pred (V a (prog f) c) y ∈ pred (V a (prog f) c) (fst (UnionV̂ {a} {prog f} {c} x))) →
                                            Σ (index (h a (prog f) c x))
                                              (λ z → h a (prog f) c (pred x (fst (fst (snd (fst (snd (UnionV̂ {a} {prog f} {c} x) y)
                                                                                (snd (h∈-iso {a} {prog f} {c} {y}
                                                                                  {fst (UnionV̂ {a} {prog f} {c} x)}) d))))))
                                                     ≐ pred (h a (prog f) c x) z)
                                 lem₂ y d = ip-compat (fst (h-iso {a} {prog f} {c} {sup (index x) (pred x)} {x})
                                                             (≐'sym {a} {prog f} {c} x (sup (index x) (pred x)) (≐'eta {a} {prog f} {c} x)))
                                                      (fst (fst (snd (fst (snd (UnionV̂ {a} {prog f} {c} x) y)
                                                                            (snd (h∈-iso {a} {prog f} {c} {y}
                                                                                         {fst (UnionV̂ {a} {prog f} {c} x)}) d)))))
                                 lem₃ : (y : V̂ a (prog f) c) (z : index (pred (V a (prog f) c) x))
                                          (e : h a (prog f) c y ∈ pred (h a (prog f) c x) z) →
                                            Σ (T̂ a (prog f) c (index x))
                                              λ u → pred (h a (prog f) c x) z ≐ h a (prog f) c (pred x u)
                                 lem₃ y z e = ip-compat (fst (h-iso {a} {prog f} {c} {x} {sup (index x) (pred x)})
                                                               (≐'eta {a} {prog f} {c} x)) z
                             in fst (UnionV̂ {a} {prog f} {c} x) ,
                                λ y → (λ d → fst (lem₂ y d) ,
                                             fst (≐ext (snd (lem₂ y d)) (h a (prog f) c y)) (lem₁ y d)) ,
                                       λ (z , e) → fst (h∈-iso {a} {prog f} {c} {y} {fst (UnionV̂ {a} {prog f} {c} x)})
                                                         (snd (snd (UnionV̂ {a} {prog f} {c} x) y)
                                                           (pred x (fst (lem₃ y z e)) ,
                                                             (fst (ip-compat (fst (h-iso {a} {prog f} {c} {x} {sup (index x) (pred x)})
                                                                                    (≐'eta {a} {prog f} {c} x)) z) ,
                                                              ≐'refl {a} {prog f} {c} (pred x (fst (ip-compat (fst (h-iso {a} {prog f} {c} {x}
                                                                                                                          {sup (index x) (pred x)})
                                                                                                                     (≐'eta {a} {prog f} {c} x)) z)))) ,
                                                             snd (h∈-iso {a} {prog f} {c} {y} {pred x (fst (lem₃ y z e))})
                                                                   (fst (≐ext (snd (lem₃ y z e)) (h a (prog f) c y)) e)))


-- V a t c satisfies Restricted Separation Axiom

-- we need the parameters U and V in the definition of [_,_,_]⊧Sep in order to express the condition that F is restricted to w 

[_,_,_]⊧Sep : (U : Set) (T : U → Set) → 𝕍 → Set₁
[ U , T , w ]⊧Sep =
  (F : 𝕍 → U) → isInv (λ x → T (F x)) → ∀𝕧∈ w λ a → ∃𝕧∈ w λ b → ∀𝕧∈ w λ x → x ∈ b ↔ (x ∈ a × T (F x))

V-sep : [ Û a t c , T̂ a t c , V a t c ]⊧Sep
V-sep {a} {prog f} {c} F F-inv x =
  let lem₁ : Σ (V̂ a (prog f) c)
               λ w → (v : V̂ a (prog f) c) →
                       T̂ a (prog f) c (∈' a (prog f) c v w) ↔ (T̂ a (prog f) c (∈' a (prog f) c v x) × T̂ a (prog f) c (F (h a (prog f) c v)))
      lem₁ = SepAxV̂ {a} {prog f} {c} (λ y → F (h a (prog f) c y)) (λ p → F-inv (fst (h-iso {a} {prog f} {c}) p)) x
      lem₂ : Σ (V̂ a (prog f) c)
               λ w → (v : V̂ a (prog f) c) →
                       T̂ a (prog f) c (∈' a (prog f) c v w) ↔
                       T̂ a (prog f) c (∃𝕧∈' a (prog f) c x (λ z → small× a (prog f) c (≐' a (prog f) c v z) (F (h a (prog f) c z))))
      lem₂ = fst lem₁ ,
             λ v → (λ d → fst (fst (fst (snd lem₁ v) d)) ,
                            snd (fst (fst (snd lem₁ v) d)) ,
                            F-inv (fst (h-iso {a} {prog f} {c}) (snd (fst (fst (snd lem₁ v) d)))) (snd (fst (snd lem₁ v) d)) ) ,
                    λ e → snd (snd lem₁ v) ((fst e , fst (snd e)) ,
                                            F-inv (≐sym (h a (prog f) c v)
                                                        (h a (prog f) c (pred x (fst e)))
                                                        (fst (h-iso {a} {prog f} {c}) (fst (snd e))))
                                                  (snd (snd e)))
  in fst lem₂ , λ y → (λ d → fst (h∈-iso {a} {prog f} {c} {y} {x})
                                   (fst (fst (snd lem₂ y) (snd (h∈-iso {a} {prog f} {c} {y} {fst lem₂}) d)) ,
                                    fst (snd (fst (snd lem₂ y) (snd (h∈-iso {a} {prog f} {c} {y} {fst lem₂}) d)))) ,
                             F-inv (fst (h-iso {a} {prog f} {c} {pred x (fst (fst (snd lem₂ y)
                                          (snd (h∈-iso {a} {prog f} {c} {y} {fst lem₂}) d)))} {y})
                                        (≐'sym {a} {prog f} {c}
                                               y
                                               (pred x (fst (fst (snd lem₂ y) (snd (h∈-iso {a} {prog f} {c} {y} {fst lem₂}) d))))
                                               (fst (snd (fst (snd lem₂ y) (snd (h∈-iso {a} {prog f} {c} {y} {fst lem₂}) d))))))
                                   (snd (snd (fst (snd lem₂ y) (snd (h∈-iso {a} {prog f} {c} {y} {fst lem₂}) d))))) ,
                      (λ e → fst (h∈-iso {a} {prog f} {c} {y} {fst lem₂})
                                   (snd (snd lem₂ y)
                                          (fst (snd (h∈-iso {a} {prog f} {c} {y} {x}) (fst e)) ,
                                            snd (snd (h∈-iso {a} {prog f} {c} {y} {x}) (fst e)) ,
                                            F-inv (fst (h-iso {a} {prog f} {c} {y}
                                                                {pred x (fst (snd (h∈-iso {a} {prog f} {c} {y} {x}) (fst e)))})
                                                         (snd (snd (h∈-iso {a} {prog f} {c} {y} {x}) (fst e))))
                                                  (snd e))))


-- V a t c validates Strong Collection Axiom

V-strcoll : V a t c ⊧StrColl
V-strcoll {a} {prog f} {c} F-inv1 F-inv2 v d =
  (sup (index v) λ x → fst (d (fst (lem₁ x)))) ,
    (λ x → fst (lem₂ x) , F-inv1 (h a (prog f) c (fst (d (fst (lem₁ (fst (lem₂ x)))))))
                                 (≐trans (pred (h a (prog f) c v) (fst (lem₁ (fst (lem₂ x)))))
                                         (h a (prog f) c (pred v (fst (lem₂ x))))
                                         (pred (h a (prog f) c v) x)
                                         (≐sym (h a (prog f) c (pred v (fst (lem₂ x))))
                                               (pred (h a (prog f) c v) (fst (lem₁ (fst (lem₂ x)))))
                                               (snd (lem₁ (fst (lem₂ x)))))
                                         (≐sym (pred (h a (prog f) c v) x)
                                                (h a (prog f) c (pred v (fst (lem₂ x))))
                                                (snd (lem₂ x))))
                                 (snd (d (fst (lem₁ (fst (lem₂ x))))))) ,
    (λ y → fst (lem₁ y) , snd (d (fst (lem₁ y))))
  where
  lem₁ : (x : T̂ a (prog f) c (index v)) → h a (prog f) c (pred v x) ∈ h a (prog f) c v 
  lem₁ x = fst (h∈-iso {a} {prog f} {c} {pred v x} {v}) (x , ≐'refl {a} {prog f} {c} (pred v x))

  lem₂ : (x : index (h a (prog f) c v)) → Σ (T̂ a (prog f) c (index v)) λ y →
           pred (h a (prog f) c v) x ≐ h a (prog f) c (pred v y)
  lem₂ x = ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)}) (≐'eta {a} {prog f} {c} v)) x

-- a parameterised formulation of Strong Collection Axiom

[_,_,_]⊧StrColl : (U : Set) → (T : U → Set) → 𝕍 → Set₁
[ U , T , v ]⊧StrColl = {F : 𝕍 → 𝕍 → U} →
                          ((w₂ : 𝕍) → isInv (λ w₁ → T (F w₁ w₂))) → ((w₁ : 𝕍) → isInv (λ w₂ → T (F w₁ w₂))) →
                            ∀𝕧∈ v (λ a → (∀𝕧∈ a λ v₁ → ∃𝕧∈ v λ v₂ → T (F v₁ v₂)) →
                              ∃𝕧∈ v λ b → (∀𝕧∈ a λ v₁ → ∃𝕧∈ b λ v₂ → T (F v₁ v₂)) × (∀𝕧∈ b λ v₂ → ∃𝕧∈ a λ v₁ → T (F v₁ v₂)))

V-strcoll' : [ Û a t c , T̂ a t c , V a t c ]⊧StrColl
V-strcoll' {a} {prog f} {c} {F} F-inv1 F-inv2 v d =
  let lem₁ : Σ (V̂ a (prog f) c)
                λ w →
                  T̂ a (prog f) c (∀𝕧∈' a (prog f) c v (λ x → ∃𝕧∈' a (prog f) c w (λ y → F (h a (prog f) c x) (h a (prog f) c y))))
                  ×
                  T̂ a (prog f) c (∀𝕧∈' a (prog f) c w (λ y → ∃𝕧∈' a (prog f) c v (λ x → F (h a (prog f) c x) (h a (prog f) c y))))
      lem₁ = StrCollV̂ {a} {prog f} {c} {λ x y → F (h a (prog f) c x) (h a (prog f) c y)} {v}
                       λ x e → fst (d (fst (fst (h∈-iso {a} {prog f} {c} {x} {v}) e))) ,
                               F-inv1 (h a (prog f) c (fst (d (fst (fst (h∈-iso {a} {prog f} {c} {x} {v}) e)))))
                                      (≐sym (h a (prog f) c x)
                                            (pred (h a (prog f) c v) (fst (fst (h∈-iso {a} {prog f} {c} {x} {v}) e)))
                                            (snd (fst (h∈-iso {a} {prog f} {c} {x} {v}) e)))
                                      (snd (d (fst (fst (h∈-iso {a} {prog f} {c} {x} {v} ) e))))
      lem₂ : (w : V̂ a (prog f) c) (x : index (h a (prog f) c w)) →
               Σ (index (sup (T̂ a (prog f) c (index w)) (λ y → h a (prog f) c (pred w y))))
                   λ y →
                    pred (h a (prog f) c w) x ≐
                    pred (sup (T̂ a (prog f) c (index w)) (λ y₁ → h a (prog f) c (pred w y₁))) y
      lem₂ w x = ip-compat (fst (h-iso {a} {prog f} {c} {w} {sup (index w) (pred w)})
                                (≐'eta {a} {prog f} {c} w))
                            x
      lem₃ : (w : V̂ a (prog f) c) (x : index (h a (prog f) c w)) →
               T̂ a (prog f) c (∈' a (prog f) c (pred w (fst (ip-compat
                                   (fst (h-iso {a} {prog f} {c} {w} {sup (index w) (pred w)})
                                     (≐'eta {a} {prog f} {c} w)) x)))
                                  w)
      lem₃ w x = snd (h∈-iso {a} {prog f} {c}
                       {pred w (fst (ip-compat
                         (fst (h-iso {a} {prog f} {c} {w} {sup (index w) (pred w)})
                           (≐'eta {a} {prog f} {c} w)) x))} {w})
                     (x , ≐sym (pred (h a (prog f) c w) x)
                               (h a (prog f) c (pred w (fst (ip-compat
                                          (fst (h-iso {a} {prog f} {c} {w} {sup (index w) (pred w)})
                                            (≐'eta {a} {prog f} {c} w)) x))))
                               (snd (lem₂ w x)))
      lem₄ : (x : index (h a (prog f) c v)) →
               h a (prog f) c (pred (fst lem₁) (fst (fst (snd lem₁) (fst (lem₃ v x))))) ∈
                 h a (prog f) c (fst lem₁)
      lem₄ x = fst (h∈-iso {a} {prog f} {c}
                     {pred (fst lem₁) (fst (fst (snd lem₁) (fst (lem₃ v x))))} {fst lem₁})
                   (fst (fst (snd lem₁) (fst (lem₃ v x))) ,
                    ≐'refl {a} {prog f} {c} (pred (fst lem₁) (fst (fst (snd lem₁) (fst (lem₃ v x))))))
      lem₅ : (y : index (h a (prog f) c (fst lem₁))) →
               h a (prog f) c (pred v (fst (snd (snd lem₁) (fst (lem₃ (fst lem₁) y))))) ∈
                 h a (prog f) c v
      lem₅ y = fst (h∈-iso {a} {prog f} {c}
                     {pred v (fst (snd (snd lem₁) (fst (lem₃ (fst lem₁) y))))} {v})
                   (fst (snd (snd lem₁) (fst (lem₃ (fst lem₁) y))) ,
                    ≐'refl {a} {prog f} {c} (pred v (fst (snd (snd lem₁) (fst (lem₃ (fst lem₁) y))))))
  in fst lem₁ ,
       (λ x → fst (lem₄ x) ,
              F-inv1 (pred (h a (prog f) c (fst lem₁)) (fst (lem₄ x)))
                     (≐trans (h a (prog f) c (pred v (fst (lem₃ v x))))
                             (h a (prog f) c (pred v (fst (lem₂ v x))))
                             (pred (h a (prog f) c v) x)
                             (≐sym (h a (prog f) c (pred v (fst (lem₂ v x))))
                                   (h a (prog f) c (pred v (fst (lem₃ v x))))
                                   (fst (h-iso {a} {(prog f)} {c} {pred v (fst (lem₂ v x))} {pred v (fst (lem₃ v x))})
                                        (snd (lem₃ v x))))
                             (≐sym (pred (h a (prog f) c v) x)
                                   (h a (prog f) c (pred v (fst (lem₂ v x))))
                                   (snd (lem₂ v x))))
                     (F-inv2 (h a (prog f) c (pred v (fst (lem₃ v x))))
                             (snd (lem₄ x))
                             (snd (fst (snd lem₁) (fst (lem₃ v x)))))) ,
       (λ y → fst (lem₅ y) ,
              F-inv2 (pred (h a (prog f) c v) (fst (lem₅ y)))
                     (≐trans (h a (prog f) c (pred (fst lem₁) (fst (lem₃ (fst lem₁) y))))
                             (h a (prog f) c (pred (fst lem₁) (fst (lem₂ (fst lem₁) y))))
                             (pred (h a (prog f) c (fst lem₁)) y)
                             (≐sym (h a (prog f) c (pred (fst lem₁) (fst (lem₂ (fst lem₁) y))))
                                   (h a (prog f) c (pred (fst lem₁) (fst (lem₃ (fst lem₁) y))))
                                   (fst (h-iso {a} {prog f} {c} {pred (fst lem₁) (fst (lem₂ (fst lem₁) y))}
                                                           {pred (fst lem₁) (fst (lem₃ (fst lem₁) y))})
                                        (snd (lem₃ (fst lem₁) y))))
                             (≐sym (pred (h a (prog f) c (fst lem₁)) y)
                                   (h a (prog f) c (pred (fst lem₁) (fst (lem₂ (fst lem₁) y))))
                                   (snd (lem₂ (fst lem₁) y))))
                     (F-inv1 (h a (prog f) c (pred (fst lem₁) (fst (lem₃ (fst lem₁) y))))
                             (snd (lem₅ y))
                             (snd (fst (snd lem₁) (fst (lem₃ (fst lem₁) y))))))


-- V a t c validates Subset Collection Axiom

V-subcoll : V a t c ⊧SubColl
V-subcoll {a} {prog g} {c} {F} F-inv1 F-inv2 v w =
  let hv : (x : T̂ a (prog g) c (index v)) → h a (prog g) c (pred v x) ∈ h a (prog g) c v
      hv x = fst (h∈-iso {a} {prog g} {c} {pred v x} {v}) (x , ≐'refl {a} {prog g} {c} (pred v x))

      u : V̂ a (prog g) c
      u = sup (codeΠ (index v) (λ _ → index w)) (λ f → sup (index v) λ x₁ → pred w (f x₁))

      lem₀ : (x : index (h a (prog g) c v)) → Σ (T̂ a (prog g) c (index v)) λ y →
               pred (h a (prog g) c v) x ≐ h a (prog g) c (pred v y)
      lem₀ x = ip-compat (fst (h-iso {a} {prog g} {c} {v} {sup (index v) (pred v)}) (≐'eta {a} {prog g} {c} v)) x

      lem₁ : (y : index (h a (prog g) c w)) →
               pred (h a (prog g) c w) y ∈ sup (T̂ a (prog g) c (index w)) (λ z → h a (prog g) c (pred w z))
      lem₁ y = fst (ExtAx2 (fst (h-iso {a} {prog g} {c} {w} {sup (index w) (pred w)})
                                  (≐'eta {a} {prog g} {c} w))
                           (pred (h a (prog g) c w) y))
                     (y , ≐refl (pred (h a (prog g) c w) y))

      f' : (z : V̂ a (prog g) c) →
             (f : ∀𝕧∈ (pred (V a (prog g) c) v) λ x →
               ∃𝕧∈ (pred (V a (prog g) c) w) λ y →
                 F x y (pred (V a (prog g) c) z)) →
             (i : T̂ a (prog g) c (index v)) →
               Σ (T̂ a (prog g) c (index w)) λ j →
                 F (h a (prog g) c (pred v i)) (h a (prog g) c (pred w j)) (h a (prog g) c z)
      f' z f i = fst (lem₁ (fst (f (fst (hv i))))) ,
                 F-inv2 (h a (prog g) c (pred v i))
                        (h a (prog g) c z)
                        (snd (lem₁ (fst (f (fst (hv i))))))
                        (F-inv1 (pred (h a (prog g) c w)
                                (fst (f (fst (fst (h∈-iso {a} {prog g} {c} {pred v i} {v})
                                  (i , ≐'refl {a} {prog g} {c} (pred v i)))))))
                                (h a (prog g) c z)
                                (≐sym (h a (prog g) c (pred v i))
                                      (pred (h a (prog g) c v) (fst (fst (h∈-iso {a} {prog g} {c} {pred v i} {v})
                                        (i , ≐'refl {a} {prog g} {c} (pred v i)))))
                                      (snd (hv i)))
                                (snd (f (fst (hv i)))))

      lem₂ : (z : V̂ a (prog g) c) →
              (f : ∀𝕧∈ (pred (V a (prog g) c) v) λ x →
                     ∃𝕧∈ (pred (V a (prog g) c) w) λ y →
                       F x y (pred (V a (prog g) c) z)) →
                h a (prog g) c (pred u λ i → fst (f' z f i)) ∈ h a (prog g) c u
      lem₂ z f = fst (h∈-iso {a} {prog g} {c} {pred u λ i → fst (f' z f i)} {u})
                       ((λ i → fst (f' z f i)) ,
                        ≐'refl {a} {prog g} {c} (pred u λ i → fst (f' z f i)))
  in u , λ z f → fst (lem₂ z f) ,
                   (λ x → fst (lem₀ x) ,
                          F-inv1 (h a (prog g) c (pred w (fst (f' z f (fst (lem₀ x))))))
                                  (h a (prog g) c z)
                                  (≐sym (pred (h a (prog g) c v) x)
                                  (h a (prog g) c (pred v (fst (ip-compat
                                                  (fst (h-iso {a} {prog g} {c} {v} {sup (index v) (pred v)})
                                                    (≐'eta {a} {prog g} {c} v)) x))))
                                  (snd (lem₀ x)))
                                  (snd (f' z f (fst (lem₀ x))))) ,
                   λ x → fst (hv x) ,
                         F-inv1 (h a (prog g) c (pred w (fst (lem₁ (fst (f (fst (fst (h∈-iso {a} {prog g} {c} {pred v x} {v})
                                  (x , ≐'refl {a} {prog g} {c} (pred v x))))))))))
                                (h a (prog g) c z)
                                (snd (hv x))
                                (snd (f' z f x))

-- a parameterised formulation of Subset Collection Axiom

[_,_,_]⊧SubColl : (U : Set) (T : U → Set) → 𝕍 → Set₁
[ U , T , b ]⊧SubColl = {F : (x y z : 𝕍) → U} →
                          ∀𝕧∈ b λ v → ∀𝕧∈ b λ w → ∃𝕧∈ b λ u → ∀𝕧∈ b λ z →
                            (∀𝕧∈ v λ x → ∃𝕧∈ w λ y → T (F x y z)) → ∃𝕧∈ b λ b' →
                              b' ∈ u ×
                              (∀𝕧∈ v λ x → ∃𝕧∈ b' λ y → T (F x y z)) ×
                              (∀𝕧∈ b' λ y → ∃𝕧∈ v λ x → T (F x y z))


-- V a t c validates Infinity Axiom

V-infty : V a t c ⊧Infty
V-infty {a} {prog f} {c} = (∅V̂ a (prog f) c , lem₁) ,
                           λ v → sucV̂ a (prog f) c v ,
                             lem₂ v ,
                             lem₃ v
  where
  lem₁ : ((x : ⊥) → Σ ⊥ λ y →
           h a (prog f) c (⊥elim (λ _ → V̂ a (prog f) c) x) ≐ ⊥elim (λ _ → 𝕍) y) ×
         ((y : ⊥) → Σ ⊥ λ x →
           h a (prog f) c (⊥elim (λ _ → V̂ a (prog f) c) x) ≐ ⊥elim (λ _ → 𝕍) y)
  lem₁ = ⊥elim (λ x → Σ ⊥ λ y → h a (prog f) c (⊥elim (λ _ → V̂ a (prog f) c) x) ≐ ⊥elim (λ _ → 𝕍) y) ,
         ⊥elim (λ y → Σ ⊥ λ x → h a (prog f) c (⊥elim (λ _ → V̂ a (prog f) c) x) ≐ ⊥elim (λ _ → 𝕍) y)

  lem₂ : (v : V̂ a (prog f) c) (x : T̂ a (prog f) c (codeS (index v) code⊤)) →
           Σ (index (h a (prog f) c v) ⊕ ⊤) λ y →
             h a (prog f) c (⊕elim (λ _ → V̂ a (prog f) c) (pred v) (λ z → v) x) ≐
             ⊕elim (λ _ → 𝕍) (pred (h a (prog f) c v)) (λ z → h a (prog f) c v) y
  lem₂ v (injl x) =
    let sublem : h a (prog f) c (pred v x) ∈ h a (prog f) c v
        sublem = fst (h∈-iso {a} {prog f} {c} {pred v x} {v}) (x , ≐'refl {a} {prog f} {c} (pred v x))
    in injl (fst sublem) , snd sublem
  lem₂ v (injr one) = injr one , ≐refl (h a (prog f) c v)

  lem₃ : (v : V̂ a (prog f) c) (y : index (h a (prog f) c v) ⊕ ⊤) →
           Σ (T̂ a (prog f) c (codeS (index v) code⊤)) λ x →
             h a (prog f) c (⊕elim (λ _ → V̂ a (prog f) c) (pred v) (λ z → v) x) ≐
             ⊕elim (λ _ → 𝕍) (pred (h a (prog f) c v)) (λ z → h a (prog f) c v) y
  lem₃ v (injl y) =
    let sublem₁ : Σ (T̂ a (prog f) c (index v)) λ z →
                    pred (h a (prog f) c v) y ≐ h a (prog f) c (pred v z)
        sublem₁ = ip-compat (fst (h-iso {a} {prog f} {c} {v} {sup (index v) (pred v)}) (≐'eta {a} {prog f} {c} v)) y

        sublem₂ : Σ (V̂ a (prog f) c) λ w → T̂ a (prog f) c (∈' a (prog f) c w v)
        sublem₂ = pred v (fst sublem₁) , fst sublem₁ , ≐'refl {a} {prog f} {c} (pred v (fst sublem₁))
    in injl (fst (snd sublem₂)) , ≐sym (pred (h a (prog f) c v) y) (h a (prog f) c (pred v (fst sublem₁))) (snd sublem₁)
  lem₃ v (injr one) = injr one , ≐refl (h a (prog f) c v)
  

-- V a t c is a model of CZF

[_,_,_]⊧CZF : (U : Set) (T : U → Set) → 𝕍 → Set₁
[ U , T , v ]⊧CZF = (v ⊧ExtAx) × (v ⊧SetInd) × (v ⊧Pairs) × (v ⊧Union) × [ U , T , v ]⊧Sep × (v ⊧StrColl) × (v ⊧SubColl) × (v ⊧Infty)

V-czf : [ Û a t c , T̂ a t c , V a t c ]⊧CZF
V-czf = ((((((V-ext , V-set-ind) , V-pairing) , V-union) , V-sep) , V-strcoll) , V-subcoll) , V-infty
