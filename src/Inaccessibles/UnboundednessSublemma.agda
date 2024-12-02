{-# OPTIONS --cubical-compatible #-}

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
open import Inaccessibles.Basics
open import Inaccessibles.FamSetsSublemma


module Inaccessibles.UnboundednessSublemma
  (U : Set)
  (T : U → Set)
  (a : 𝕍)
  (B : Set)
  (g : B → 𝕍)
  (a-inacc : [ U , T , a ]-isInacc)
  (hyp : ∀𝕧∈ (sup B g) λ v → ∀𝕧∈ a λ w → Σ Set λ U' → Σ (U' → Set) λ T' → Σ 𝕍 λ w' → [ U' , T' , w' ]-is v Inacc × w ∈ w' × w' ∈ a)
  (j : index (tc (sup B g)))
  (k : index (famSets U T a B g a-inacc hyp j))
  where


  rightSublemma : pred (famSets U T a B g a-inacc hyp j) k ∈ famSets₂ U T a B g a-inacc hyp j → (j' : index (tc (pred (tc (sup B g)) j))) →
                    famSets U T a B g a-inacc hyp (index-trans (sup B g) j j') isUnboundedIn pred (famSets U T a B g a-inacc hyp j) k
  rightSublemma rightProof j' x =
    fst (famSetsSublemma U T a B g a-inacc hyp j k rightProof j' x) ,
    fst (ExtAx2 {pred (t₃ U T a B g a-inacc hyp j k rightProof j') (fst (subsublem₇ U T a B g a-inacc hyp j k rightProof j' x))}
                {pred (famSets U T a B g a-inacc hyp (index-trans (sup B g) j j')) (fst (famSetsSublemma U T a B g a-inacc hyp j k rightProof j' x))}
                (snd (famSetsSublemma U T a B g a-inacc hyp j k rightProof j' x))
                (pred (pred (famSets U T a B g a-inacc hyp j) k) x))
          (fst (snd (subsublem₇ U T a B g a-inacc hyp j k rightProof j' x))) ,
    ExtAx1 {pred (t₃ U T a B g a-inacc hyp j k rightProof j') (fst (subsublem₇ U T a B g a-inacc hyp j k rightProof j' x))}
           {pred (famSets U T a B g a-inacc hyp (index-trans (sup B g) j j')) (fst (famSetsSublemma U T a B g a-inacc hyp j k rightProof j' x))}
           {pred (famSets U T a B g a-inacc hyp j) k}
           (snd (famSetsSublemma U T a B g a-inacc hyp j k rightProof j' x))
           (snd (snd (subsublem₇ U T a B g a-inacc hyp j k rightProof j' x)))

  tc-unboundedness : (j' : index (tc (pred (tc (sup B g)) j))) →
                       famSets U T a B g a-inacc hyp (index-trans (sup B g) j j') isUnboundedIn pred (famSets U T a B g a-inacc hyp j) k
  tc-unboundedness =
    let sublem₁ : pred (famSets U T a B g a-inacc hyp j) k ∈ famSets₁ U T a B g a-inacc hyp j ⊕
                  pred (famSets U T a B g a-inacc hyp j) k ∈ famSets₂ U T a B g a-inacc hyp j
        sublem₁ = fst (∪b-proof (famSets₁ U T a B g a-inacc hyp j)
                                (famSets₂ U T a B g a-inacc hyp j)
                                (pred (famSets U T a B g a-inacc hyp j) k))
                        (k , ≐refl (pred (famSets U T a B g a-inacc hyp j) k))
    in ⊕elim (λ _ → (j' : index (tc (pred (tc (sup B g)) j))) →
                          famSets U T a B g a-inacc hyp (index-trans (sup B g) j j') isUnboundedIn pred (famSets U T a B g a-inacc hyp j) k)
                (leftSublemma U T a B g a-inacc hyp j k)
                rightSublemma
                sublem₁
