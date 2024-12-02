{-# OPTIONS --cubical-compatible #-}

module Inaccessibles.Basics where

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
open import RegularExtensionAxiom

{-
   This file formalises the type-theoretic counterparts of inaccessible sets in
   Aczel's constructive set theory CZF, following

     Michael Rathjen, Edward R. Griffor, and Erik Palmgren. Inaccessibility in
     constructive set theory and type theory. Ann. Pure Appl. Log., 94(1-3):181--200, 1998.
-}


private variable
  a : 𝕍
  t : Acc a
  c : 𝔽 0


-- the definition of set-inaccessibles (or inaccessible sets)

[_,_,_]-isInacc : (U : Set) (T : U → Set) → 𝕍 → Set₁
[ U , T , a ]-isInacc = (isRegular a) × [ U , T , a ]⊧CZF × (∀𝕧∈ a λ b → ∃𝕧∈ a λ c → b ⊆ c × isRegular c)

V-Inacc : [ Û a t c , T̂ a t c , V a t c ]-isInacc
V-Inacc = (V-regular , V-czf) , V-REA

tc-trans : {a b v : 𝕍} → b ∈ (tc a) → v ∈ (tc b) → v ∈ (tc a)
tc-trans {sup A f} {b} {v} d e = lem d
  where
  lem : b ∈ (sup A f ∪b ∪ (sup A (λ x → tc (f x)))) → v ∈ (tc (sup A f))
  lem (injl x , d') = injr (x , fst (tc-cong d' v e)) , snd (tc-cong d' v e)
  lem (injr (x , i) , d') = injr (x , fst (tc-trans {f x} (i , d') e)) , snd (tc-trans {f x} (i , d') e) 

index-trans : (b : 𝕍) (i : index (tc b)) → index (tc (pred (tc b) i)) → index (tc b)
index-trans b i j = fst (tc-trans {b} (i , ≐refl (pred (tc b) i)) (j , ≐refl (pred (tc (pred (tc b) i)) j)))

index-trans≐ : (b : 𝕍) (i : index (tc b)) (j : index (tc (pred (tc b) i))) →
                 pred (tc (pred (tc b) i)) j ≐ pred (tc b) (index-trans b i j)
index-trans≐ b i j = snd (tc-trans {b} (i , ≐refl (pred (tc b) i)) (j , ≐refl (pred (tc (pred (tc b) i)) j)))

_isUnboundedIn_ : 𝕍 → 𝕍 → Set
v isUnboundedIn w = ∀𝕧∈ w λ x → ∃𝕧∈ v λ y → x ∈ y × y ∈ w

unbounded-inv : (w : 𝕍) → isInv (λ v → v isUnboundedIn w)
unbounded-inv w {a} {b} p a-ub-w i =
  let w-b : pred a (fst (a-ub-w i)) ∈ b
      w-b = fst (ExtAx2 p (pred a (fst (a-ub-w i))))
                  (fst (a-ub-w i) , ≐refl (pred a (fst (a-ub-w i))))
  in fst w-b ,
       fst (ExtAx2 (snd w-b) (pred w i)) (fst (snd (a-ub-w i))) ,
       ExtAx1 {pred a (fst (a-ub-w i))} {pred b (fst w-b)} {w} (snd w-b) (snd (snd (a-ub-w i)))

unbounded-inv' : (v : 𝕍) → isInv (λ w → v isUnboundedIn w)
unbounded-inv' v {a} {b} p v-ub-a j =
  let sublem : ∃𝕧∈ v λ y → pred a (fst (snd (≐bisim p) j)) ∈ y × y ∈ a
      sublem = v-ub-a (fst (snd (≐bisim p) j))
  in fst sublem ,
     ExtAx1 {x = pred v (fst sublem)} (snd (snd (≐bisim p) j)) (fst (snd sublem)) ,
     fst (ExtAx2 p (pred v (fst sublem))) (snd (snd sublem))
     

-- the definition of a-set-inaccessibles for an arbitrary set a

[_,_,_]-is_Inacc : (U : Set) (T : U → Set) → 𝕍 → 𝕍 → Set₁
[ U , T , a ]-is b Inacc =
  [ U , T , a ]-isInacc ×
  Σ ((i : index (tc b)) → 𝕍) λ famSets →
    ((i j : index (tc b)) → pred (tc b) i ≐ pred (tc b) j → famSets i ≐ famSets j) ×
    ((i : index (tc b)) →
      (famSets i isUnboundedIn a) ×
      (∀𝕧∈ (famSets i) λ v → Σ Set λ U' → Σ (U' → Set) λ T' → [ U' , T' , v ]-isInacc) ×
      (∀𝕧∈ (famSets i) λ v → (j : index (tc (pred (tc b) i))) → famSets (index-trans b i j) isUnboundedIn v))

famSetsLemma : {a : 𝕍} → (famSets : index (tc a) → 𝕍) →
                 ((i j : index (tc a)) → pred (tc a) i ≐ pred (tc a) j → famSets i ≐ famSets j) →
                   (i₁ : index (tc a)) (i₂ : index (tc (pred (tc a) i₁))) (i₃ : (index (tc (pred (tc (pred (tc a) i₁)) i₂)))) →
                     Σ (index (tc (pred (tc a) (index-trans a i₁ i₂)))) λ i₄ →
                     famSets (index-trans a (index-trans a i₁ i₂) i₄) ≐
                     famSets (index-trans a i₁ (index-trans (pred (tc a) i₁) i₂ i₃))
famSetsLemma {a} famSets famSets-cong i₁ i₂ i₃ =
  fst sublem₁ ,
  famSets-cong (index-trans a (index-trans a i₁ i₂) (fst sublem₁))
               (index-trans a i₁ (index-trans (pred (tc a) i₁) i₂ i₃))
               (≐trans (pred (tc a) (index-trans a (index-trans a i₁ i₂) (fst sublem₁)))
                       (pred (tc (pred (tc a) (index-trans a i₁ i₂))) (fst sublem₁))
                       (pred (tc a) (index-trans a i₁ (index-trans (pred (tc a) i₁) i₂ i₃)))
                       sublem₂
                       (≐trans (pred (tc (pred (tc a) (index-trans a i₁ i₂))) (fst sublem₁))
                               (pred (tc (pred (tc (pred (tc a) i₁)) i₂)) i₃)
                               (pred (tc a) (index-trans a i₁ (index-trans (pred (tc a) i₁) i₂ i₃)))
                               (≐sym (pred (tc (pred (tc (pred (tc a) i₁)) i₂)) i₃)
                                     (pred (tc (pred (tc a) (index-trans a i₁ i₂))) (fst sublem₁))
                                     (snd sublem₁))
                               (≐trans (pred (tc (pred (tc (pred (tc a) i₁)) i₂)) i₃)
                                       (pred (tc (pred (tc a) i₁)) (index-trans (pred (tc a) i₁) i₂ i₃))
                                       (pred (tc a) (index-trans a i₁ (index-trans (pred (tc a) i₁) i₂ i₃)))
                                       sublem₄
                                       sublem₃)))
  where
  sublem₁ : Σ (index (tc (pred (tc a) (index-trans a i₁ i₂)))) λ i₄ →
             pred (tc (pred (tc (pred (tc a) i₁)) i₂)) i₃ ≐
             pred (tc (pred (tc a) (index-trans a i₁ i₂))) i₄
  sublem₁ = fst (≐bisim (tc-cong' (index-trans≐ a i₁ i₂))) i₃

  sublem₂ : pred (tc a) (index-trans a (index-trans a i₁ i₂) (fst sublem₁)) ≐
            pred (tc (pred (tc a) (index-trans a i₁ i₂))) (fst sublem₁)
  sublem₂ = ≐sym (pred (tc (pred (tc a) (index-trans a i₁ i₂))) (fst sublem₁))
                 (pred (tc a) (index-trans a (index-trans a i₁ i₂) (fst sublem₁)))
                 (index-trans≐ a (index-trans a i₁ i₂) (fst sublem₁))

  sublem₃ : pred (tc (pred (tc a) i₁)) (index-trans (pred (tc a) i₁) i₂ i₃) ≐
            pred (tc a) (index-trans a i₁ (index-trans (pred (tc a) i₁) i₂ i₃))
  sublem₃ = index-trans≐ a i₁ (index-trans (pred (tc a) i₁) i₂ i₃)

  sublem₄ : pred (tc (pred (tc (pred (tc a) i₁)) i₂)) i₃ ≐
            pred (tc (pred (tc a) i₁)) (index-trans (pred (tc a) i₁) i₂ i₃)
  sublem₄ = index-trans≐ (pred (tc a) i₁) i₂ i₃


inaccHierarchyLemma : {U : Set} {T : U → Set} {v a : 𝕍} →
                        [ U , T , v ]-is a Inacc → ∀𝕧∈ (tc a) λ b → [ U , T , v ]-is b Inacc
inaccHierarchyLemma {U} {T} {v} {sup A f} v-a-inacc (injl x) =
  fst v-a-inacc , fx-famSets ,
    (λ i j p → fst (snd (snd v-a-inacc)) (injr (x , i)) (injr (x , j)) p) ,
    λ i → snd (snd (snd v-a-inacc)) (injr (x , i))
  where
  a-famSets : index (tc (sup A f)) → 𝕍 
  a-famSets = fst (snd v-a-inacc)

  fx-famSets : index (tc (pred (tc (sup A f)) (injl x))) → 𝕍
  fx-famSets i = a-famSets (injr (x , i))
inaccHierarchyLemma {U} {T} {v} {sup A f} v-a-inacc (injr (x , i)) =
  inaccHierarchyLemma {U} {T} {v} {f x} (fst v-a-inacc ,
                                         fx-famSets ,
                                         (λ j₁ j₂ p → fst (snd (snd v-a-inacc)) (injr (x , j₁)) (injr (x , j₂)) p) ,
                                         λ i → snd (snd (snd v-a-inacc)) (injr (x , i))) i
  where
  a-famSets : index (tc (sup A f)) → 𝕍 
  a-famSets = fst (snd v-a-inacc)

  fx-famSets : index (tc (pred (tc (sup A f)) (injl x))) → 𝕍
  fx-famSets i = a-famSets (injr (x , i))

inaccLemma : {U : Set} {T : U → Set} {v a : 𝕍} →
                        (d : [ U , T , v ]-is a Inacc) → (i : index (tc a)) → ∀𝕧∈ (fst (snd d) i) λ w →
                          Σ Set λ U' → Σ (U' → Set) λ T' → [ U' , T' , w ]-is pred (tc a) i Inacc
inaccLemma {U} {T} {v} {a} v-a-inacc i j =
  fst (snd (fst (snd (snd (snd v-a-inacc)) i)) j) ,
  fst (snd (snd (fst (snd (snd (snd v-a-inacc)) i)) j)) ,
  snd (snd (snd (fst (snd (snd (snd v-a-inacc)) i)) j)) ,
  (λ k → fst (snd v-a-inacc) (index-trans a i k)) ,
  sublem₂ ,
  λ i' → (snd (snd (snd (snd v-a-inacc)) i) j i' ,
          snd (fst (snd (snd (snd v-a-inacc)) (index-trans a i i')))) ,
          λ k l → unbounded-inv (pred (fst (snd v-a-inacc) (index-trans a i i')) k)
                                {fst (snd v-a-inacc) (index-trans a (index-trans a i i')
                                                       (fst (famSetsLemma {a} (fst (snd v-a-inacc)) (fst (snd (snd v-a-inacc))) i i' l)))}
                                {fst (snd v-a-inacc) (index-trans a i (index-trans (pred (tc a) i) i' l))}
                                ((snd (famSetsLemma {a} (fst (snd v-a-inacc)) (fst (snd (snd v-a-inacc))) i i' l)))
                                (snd (snd (snd (snd v-a-inacc)) (index-trans a i i')) k
                                (fst (famSetsLemma {a} (fst (snd v-a-inacc)) (fst (snd (snd v-a-inacc))) i i' l)))
  where
  sublem₁ : (i₁ : index (tc (pred (tc a) i))) → pred (tc a) (index-trans a i i₁) ≐ pred (tc (pred (tc a) i)) i₁
  sublem₁ i₁ = ≐sym (pred (tc (pred (tc a) i)) i₁)
                    (pred (tc a) (index-trans a i i₁))
                    (index-trans≐ a i i₁)

  sublem₂ : (i₁ j₁ : index (tc (pred (tc a) i))) →
              pred (tc (pred (tc a) i)) i₁ ≐ pred (tc (pred (tc a) i)) j₁ →
                fst (snd v-a-inacc) (index-trans a i i₁) ≐
                fst (snd v-a-inacc) (index-trans a i j₁)
  sublem₂ i₁ i₂ p = fst (snd (snd v-a-inacc)) (index-trans a i i₁) (index-trans a i i₂)
                                          (≐trans (pred (tc a) (index-trans a i i₁))
                                                  (pred (tc (pred (tc a) i)) i₁)
                                                  (pred (tc a) (index-trans a i i₂))
                                                  (sublem₁ i₁)
                                                  (≐trans (pred (tc (pred (tc a) i)) i₁)
                                                          (pred (tc (pred (tc a) i)) i₂)
                                                          (pred (tc a) (index-trans a i i₂))
                                                          p
                                                          (index-trans≐ a i i₂)))


inaccHierarchy→ : (U : Set) (T : U → Set) (a b : 𝕍) → [ U , T , a ]-isInacc →
                    [ U , T , a ]-is b Inacc →
                    (∀𝕧∈ b λ v → ∀𝕧∈ a λ w → Σ Set λ U' → Σ (U' → Set) λ T' → Σ 𝕍 λ w' →
                      [ U' , T' , w' ]-is v Inacc × w ∈ w' × w' ∈ a)
inaccHierarchy→ U T a (sup B g) a-inacc a-b-inacc j i =
  fst (inaccLemma {U} {T} {a} {sup B g} a-b-inacc (injl j) (fst (ub-lem j i))) ,
  fst (snd (inaccLemma {U} {T} {a} {sup B g} a-b-inacc (injl j) (fst (ub-lem j i)))) ,
  pred (b-famSets (injl j)) (fst (ub-lem j i)) ,
  (snd (snd (inaccLemma {U} {T} {a} {sup B g} a-b-inacc (injl j) (fst (ub-lem j i)))) ,
  fst (snd (ub-lem j i))) ,
  snd (snd (ub-lem j i))
  where
  b-famSets : index (tc (sup B g)) → 𝕍
  b-famSets = fst (snd a-b-inacc)

  ub-lem : (j : index (sup B g)) → b-famSets (injl j) isUnboundedIn a
  ub-lem j = fst (fst (snd (snd (snd (a-b-inacc))) (injl j)))


postulate
  Inacc-inv : (U : Set) (T : U → Set) → isInv λ a → [ U , T , a ]-isInacc
  αInacc-inv : (U : Set) (T : U → Set) (b : 𝕍) → isInv λ a → [ U , T , a ]-is b Inacc
  αInacc-inv' : (U : Set) (T : U → Set) (a : 𝕍) → isInv λ b → [ U , T , a ]-is b Inacc
