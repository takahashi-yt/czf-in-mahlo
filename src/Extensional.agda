{-# OPTIONS --cubical-compatible #-}

module Extensional where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Preliminaries
open import CZFBasics
open import CZFAxioms


-- This file postulates Function Extensionality

postulate
  fun-ext : {a b : Level} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
    ((x : A) → f x ≡ g x) → f ≡ g


-- Below we prove the propositional computation rule of the transfinite induction principles for transitive closures of sets
-- First we prove the lemma for this propositional computation rule using Function Extensionality

tcTIcomp-lem : (a : 𝕍) → {ℓ : Level} → (F : 𝕍 → Set ℓ) (e : (a : 𝕍) → (∀𝕧∈ (tc a) λ v → F v) → F a) →
                 (∈-tcTI e a ≡ e a (λ x → ∈-tcTI e (pred (tc a) x))) ×
                 (∈-tcTI (λ v d z → e (pred (tc v) z) (d z)) a ≡ λ x → ∈-tcTI e (pred (tc a) x)) ×
                 (∈-tcTI-IH e a ≡ λ x → ∈-tcTI e (pred (tc a) x))
tcTIcomp-lem a {ℓ} = ∈-tcTI
                       {F = λ a → (F : 𝕍 → Set ℓ) (e : (w : 𝕍) → (∀𝕧∈ (tc w) λ v → F v) → F w) →
                                    (∈-tcTI e a ≡ e a (λ x → ∈-tcTI e (pred (tc a) x))) ×
                                    (∈-tcTI (λ v d z → e (pred (tc v) z) (d z)) a ≡
                                      λ x → ∈-tcTI e (pred (tc a) x)) ×
                                    (∈-tcTI-IH e a ≡ λ x → ∈-tcTI e (pred (tc a) x))}
                       (Welim (λ a → (∀𝕧∈ (tc a) λ b →
                                       (F : 𝕍 → Set ℓ) (e : (w : 𝕍) → (∀𝕧∈ (tc w) λ v → F v) → F w) →
                                         ((∈-tcTI e b ≡ e b (λ x → ∈-tcTI e (pred (tc b) x))) ×
                                         (∈-tcTI (λ v d z → e (pred (tc v) z) (d z)) b ≡
                                           λ x → ∈-tcTI e (pred (tc b) x)) ×
                                         (∈-tcTI-IH e b ≡ λ x → ∈-tcTI e (pred (tc b) x)))) →
                                     (F : 𝕍 → Set ℓ) (e : (w : 𝕍) → (∀𝕧∈ (tc w) λ v → F v) → F w) →
                                       ((∈-tcTI e a ≡ e a (λ x → ∈-tcTI e (pred (tc a) x))) ×
                                       (∈-tcTI (λ v d z → e (pred (tc v) z) (d z)) a ≡
                                         (λ x → ∈-tcTI e (pred (tc a) x))) ×
                                       (∈-tcTI-IH e a ≡ (λ x → ∈-tcTI e (pred (tc a) x)))))
                              λ A f prec IH F e →
                              let sublem-one : (x : index (tc (sup A f))) →
                                                 e (pred (tc (sup A f)) x)
                                                   (∈-tcTI-IH (λ v d z₁ → e (pred (tc v) z₁) (d z₁))
                                                     (sup A f) x) ≡
                                                 ∈-tcTI e (pred (tc (sup A f)) x)
                                  sublem-one = ⊕elim
                                                 (λ x → e (pred (tc (sup A f)) x)
                                                          (∈-tcTI-IH (λ v d z → e (pred (tc v) z) (d z))
                                                                     (sup A f) x) ≡
                                                        ∈-tcTI e (pred (tc (sup A f)) x))
                                                 (λ y → ≡trans
                                                          (transp (λ d → e (f y)
                                                                           (∈-tcTI
                                                                             (λ v d z → e (pred (tc v) z) (d z))
                                                                             (f y)) ≡
                                                                         e (f y) d)
                                                                  (snd (fst (IH (injl y) F e)))
                                                                  refl)
                                                          (≡sym (fst (fst (IH (injl y) F e)))))
                                                 λ (y , c) → ≡trans
                                                               (transp (λ h → e (pred (tc (f y)) c)
                                                                         (∈-tcTI 
                                                                           (λ a d z z₁ →
                                                                             e (pred (tc (pred (tc a) z)) z₁) (d z z₁))
                                                                           (f y) c) ≡
                                                                           e (pred (tc (f y)) c) h)
                                                                       (snd (fst (IH (injr (y , c)) F e)))
                                                                       (transp (λ h → e (pred (tc (f y)) c)
                                                                                        (∈-tcTI {F = λ a → ∀𝕧∈ (tc a)
                                                                                                       λ v → (x : index (tc v)) →
                                                                                                         F (pred (tc v) x)}
                                                                                          (λ v₁ d₁ z₁ →
                                                                                            (λ z →
                                                                                              e (pred (tc (pred (tc v₁) z₁)) z)
                                                                                                (d₁ z₁ z)))
                                                                                          (f y) c) ≡
                                                                                      e (pred (tc (f y)) c) h)
                                                                               (inv-fun-ext
                                                                                 (snd (fst (IH (injl y)
                                                                                   (λ a → ∀𝕧∈ (tc a) λ v → F v)
                                                                                     (λ v d z → e (pred (tc v) z) (d z))))) c)
                                                                               refl))
                                                               (≡sym (fst (fst (IH (injr (y , c)) F e))))
                                  sublem-two : (x : index (tc (sup A f))) →
                                                 ∈-tcTI-IH e (sup A f) x ≡ ∈-tcTI e (pred (tc (sup A f)) x)
                                  sublem-two = ⊕elim
                                                 (λ x → ∈-tcTI-IH e (sup A f) x ≡ ∈-tcTI e (pred (tc (sup A f)) x))
                                                 (λ y → refl)
                                                 λ (y , c) → inv-fun-ext (snd (fst (IH (injl y) F e))) c
                              in (ap (λ d → e (sup A f) d) (fun-ext sublem-two) ,
                                  fun-ext sublem-one) ,
                                  fun-ext sublem-two)
                       a

-- the propositional computation rule of the transfinite induction principles for transitive closures of sets

tcTIcomp : {ℓ : Level} {F : 𝕍 → Set ℓ} → (e : (a : 𝕍) → (∀𝕧∈ (tc a) λ v → F v) → F a) (a : 𝕍) →
                 (∈-tcTI e a ≡ e a (λ x → ∈-tcTI e (pred (tc a) x)))
tcTIcomp {F = F} e a = fst (fst (tcTIcomp-lem a F e))


-- the propositional rule above enables to prove the introduction rule for the accessibility predicate Acc

Acc : 𝕍 → Set
Acc = ∈-tcTI λ a IH → (x : index (tc a)) → IH x

Acc-intro : (a : 𝕍) → (∀𝕧∈ (tc a) λ v → Acc v) → Acc a
Acc-intro (sup A f) = transp (λ A → A)
                             (≡sym (tcTIcomp (λ a IH → (x : index (tc a)) → IH x) (sup A f)))
