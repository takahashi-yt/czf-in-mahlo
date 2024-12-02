{-# OPTIONS --cubical-compatible #-}

module Inaccessibles.HierarchyLemma where

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
open import Inaccessibles.UnboundednessSublemma


private variable
  a : 𝕍
  t : Acc a
  c : 𝔽 0


inaccHierarchy← : (U : Set) (T : U → Set) (a b : 𝕍) → [ U , T , a ]-isInacc →
                    (∀𝕧∈ b λ v → ∀𝕧∈ a λ w → Σ Set λ U' → Σ (U' → Set) λ T' → Σ 𝕍 λ w' →
                      [ U' , T' , w' ]-is v Inacc × w ∈ w' × w' ∈ a) →
                        [ U , T , a ]-is b Inacc
inaccHierarchy← U T a (sup B g) a-inacc hyp =
  a-inacc ,
  famSets U T a B g a-inacc hyp ,
  famSetsExtensionality U T a B g a-inacc hyp ,
  λ j → (unboundedness U T a B g a-inacc hyp j ,
         (λ k → inaccessibility U T a B g a-inacc hyp j k)) ,
        λ k → tc-unboundedness U T a B g a-inacc hyp j k

inaccHierarchy : (U : Set) (T : U → Set) (a b : 𝕍) → [ U , T , a ]-isInacc →
                   [ U , T , a ]-is b Inacc ↔
                   (∀𝕧∈ b λ v → ∀𝕧∈ a λ w → Σ Set λ U' → Σ (U' → Set) λ T' → Σ 𝕍 λ w' →
                     [ U' , T' , w' ]-is v Inacc × w ∈ w' × w' ∈ a)
inaccHierarchy U T a (sup B g) a-inacc =
  inaccHierarchy→ U T a (sup B g) a-inacc ,
  inaccHierarchy← U T a (sup B g) a-inacc
