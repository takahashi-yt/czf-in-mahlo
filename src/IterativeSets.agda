
module IterativeSets where

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


-- the iterator ϕ of u𝕄 along a given iterative set α

ϕ : 𝕍 → 𝕆 1
ϕ α = ∈-tcTI (λ b e → u𝕄 (index (tc b) , e)) α


-- the α-th subuniverse M α c with the decoding function T α c for any α : 𝕍 and c : 𝔽 0

M : 𝕍 → 𝔽 0 → Set
M α c = fst (ϕ α c)

T : (α : 𝕍) → (c : 𝔽 0) → M α c → Set
T α c x = snd (ϕ α c) x


-- the type V α c of the α-th iterative sets on M α c

V : 𝕍 → 𝔽 0 → Set
V α c = W (M α c) (T α c)
