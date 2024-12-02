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


module Inaccessibles.FamSetsSublemma
  (U : Set)
  (T : U → Set)
  (a : 𝕍)
  (B : Set)
  (g : B → 𝕍)
  (a-inacc : [ U , T , a ]-isInacc)
  (hyp : ∀𝕧∈ (sup B g) λ v → ∀𝕧∈ a λ w → Σ Set λ U' → Σ (U' → Set) λ T' → Σ 𝕍 λ w' → [ U' , T' , w' ]-is v Inacc × w ∈ w' × w' ∈ a)
  where


  z-inacc-ub-in-a : ∀𝕧∈ a λ x → ∀𝕧∈ (tc (sup B g)) λ z → Σ Set λ U' → Σ (U' → Set) λ T' → Σ 𝕍 λ u →
                      u ∈ a × x ∈ u × [ U' , T' , u ]-is z Inacc
  z-inacc-ub-in-a i (injl y) = fst (hyp y i) , fst (snd (hyp y i)) , fst (snd (snd (hyp y i))) ,
                               (snd (snd (snd (snd (hyp y i)))) , snd (fst (snd (snd (snd (hyp y i)))))) ,
                               fst (fst (snd (snd (snd (hyp y i)))))
  z-inacc-ub-in-a i (injr (y , d)) = fst (hyp y i) , fst (snd (hyp y i)) , fst (snd (snd (hyp y i))) ,
                                     (snd (snd (snd (snd (hyp y i)))) , snd (fst (snd (snd (snd (hyp y i)))))) ,
                                     inaccHierarchyLemma {fst (hyp y i)}
                                                         {fst (snd (hyp y i))}
                                                         {fst (snd (snd (hyp y i)))}
                                                         {a = g y}
                                                         (fst (fst (snd (snd (snd (hyp y i)))))) d

  F : 𝕍 → 𝕍 → Set₁
  F pair triple = Σ Set λ U' → Σ (U' → Set) λ T' → Σ 𝕍 λ u → ∃𝕧∈ a λ v → ∃𝕧∈ (tc (sup B g)) λ w →
                    (pair ≐ ⟨ v , w ⟩) × (triple ≐ ⟨ ⟨ v , w ⟩ , u ⟩) × u ∈ a × v ∈ u × [ U' , T' , u ]-is w Inacc
               
  lem₁ : Σ 𝕍 λ S → (∀𝕧∈ (a ×𝕍 (tc (sup B g))) λ pair → ∃𝕧∈ S λ triple → F pair triple) ×
                   (∀𝕧∈ S λ triple → ∃𝕧∈ (a ×𝕍 (tc (sup B g))) λ pair → F pair triple)
  lem₁ = StrColl {F = F}
           λ (i , j) → ⟨ ⟨ pred a i , pred (tc (sup B g)) j ⟩ , fst (snd (snd (z-inacc-ub-in-a i j))) ⟩ ,
                       fst (z-inacc-ub-in-a i j) ,
                       fst (snd (z-inacc-ub-in-a i j)) ,
                       fst (snd (snd (z-inacc-ub-in-a i j))) ,
                       i ,
                       j ,
                       (((≐refl ⟨ pred a i , pred (tc (sup B g)) j ⟩ ,
                          ≐refl ⟨ ⟨ pred a i , pred (tc (sup B g)) j ⟩ , fst (snd (snd (z-inacc-ub-in-a i j))) ⟩) ,
                         fst (fst (snd (snd (snd (z-inacc-ub-in-a i j)))))) ,
                        snd (fst (snd (snd (snd (z-inacc-ub-in-a i j)))))) ,
                       snd (snd (snd (snd (z-inacc-ub-in-a i j))))

  fam₁Property : (j : index (tc (sup B g))) → Σ 𝕍 λ S' →
                    (x : 𝕍) → x ∈ S' ↔ ∃𝕧∈ a λ u → (∃𝕧∈ a λ v →
                                         ⟨ ⟨ v , pred (tc (sup B g)) j ⟩ , u ⟩ ∈ (fst lem₁)) × (x ≐ u)
  fam₁Property j = SepAx (λ u → ∃𝕧∈ a λ v → ⟨ ⟨ v , pred (tc (sup B g)) j ⟩ , u ⟩ ∈ (fst lem₁)) a

  famSets₁ : (j : index (tc (sup B g))) → 𝕍
  famSets₁ j = fst (fam₁Property j)

  famSets₁Lemma : (j₁ j₂ : index (tc (sup B g))) → pred (tc (sup B g)) j₁ ≐ pred (tc (sup B g)) j₂ → famSets₁ j₁ ≐ famSets₁ j₂
  famSets₁Lemma j₁ j₂ p = ExtAx2' (λ x → (λ d → snd (snd (fam₁Property j₂) x)
                                                (fst (fst (snd (fam₁Property j₁) x) d) ,
                                                (fst (fst (snd (fst (snd (fam₁Property j₁) x) d))) ,
                                                 ExtAx1 {x = fst lem₁} (snd OPairAx (snd OPairAx (≐refl (pred a (fst (fst (snd (fst (snd (fam₁Property j₁) x) d))))) , p) ,
                                                                                     ≐refl (pred a (fst (fst (snd (fam₁Property j₁) x) d)))))
                                                                       (snd (fst (snd (fst (snd (fam₁Property j₁) x) d))))) ,
                                                snd (snd (fst (snd (fam₁Property j₁) x) d)))) ,
                                         (λ e → snd (snd (fam₁Property j₁) x)
                                                (fst (fst (snd (fam₁Property j₂) x) e) ,
                                                (fst (fst (snd (fst (snd (fam₁Property j₂) x) e))) ,
                                                 ExtAx1 {x = fst lem₁} (snd OPairAx (snd OPairAx (≐refl (pred a (fst (fst (snd (fst (snd (fam₁Property j₂) x) e))))) ,
                                                                                                  ≐sym (pred (tc (sup B g)) j₁)
                                                                                                       (pred (tc (sup B g)) j₂)
                                                                                                       p) ,
                                                                                     ≐refl (pred a (fst (fst (snd (fam₁Property j₂) x) e)))))
                                                                       (snd (fst (snd (fst (snd (fam₁Property j₂) x) e))))) ,
                                                snd (snd (fst (snd (fam₁Property j₂) x) e)))))

  lem₂ : (j : index (tc (sup B g))) → ∀𝕧∈ (famSets₁ j) λ u → Σ Set λ U' → Σ (U' → Set) λ T' →
           [ U' , T' , u ]-is pred (tc (sup B g)) j Inacc
  lem₂ j k =
    let sublem₁ : ∃𝕧∈ a (λ u → ∃𝕧∈ a (λ v → ⟨ ⟨ v , pred (tc (sup B g)) j ⟩ , u ⟩ ∈ fst lem₁) × (pred (famSets₁ j) k ≐ u))
        sublem₁ = fst (snd (fam₁Property j) (pred (famSets₁ j) k)) (k , ≐refl (pred (famSets₁ j) k))
        
        sublem₂ : F (pred (a ×𝕍 (tc (sup B g))) (fst (snd (snd lem₁) (fst (snd (fst (snd sublem₁)))))))
                    (pred (fst lem₁) (fst (snd (fst (snd sublem₁)))))
        sublem₂ = snd (snd (snd lem₁) (fst (snd (fst (snd sublem₁)))))
    in fst sublem₂ ,
       fst (snd sublem₂) ,
       αInacc-inv (fst sublem₂) (fst (snd sublem₂)) (pred (tc (sup B g)) j)
                  {fst (snd (snd (snd (snd (snd lem₁) (fst (snd (fst (snd sublem₁))))))))}
                  {pred (famSets₁ j) k}
                  (≐trans (fst (snd (snd (snd (snd (snd lem₁) (fst (snd (fst (snd sublem₁)))))))))
                          (pred a (fst sublem₁))
                          (pred (famSets₁ j) k)
                          (≐trans (fst (snd (snd (snd (snd (snd lem₁) (fst (snd (fst (snd sublem₁)))))))))
                                  (fst (snd (snd (z-inacc-ub-in-a (fst (fst (snd (fst (snd sublem₁))))) (snd (fst (snd (fst (snd sublem₁)))))))))
                                  (pred a (fst sublem₁))
                                  (snd (fst OPairAx (snd (fst (fst (fst (snd (snd (snd (snd (snd sublem₂)))))))))))
                                  (≐sym (pred a (fst sublem₁))
                                        (fst (snd (snd (z-inacc-ub-in-a (fst (fst (snd (fst (snd sublem₁))))) (snd (fst (snd (fst (snd sublem₁)))))))))
                                        (snd (fst OPairAx (snd (snd (fst (snd sublem₁))))))))
                          (≐sym (pred (famSets₁ j) k)
                                (pred a (fst sublem₁))
                                (snd (snd sublem₁))))
                  (αInacc-inv' (fst sublem₂) (fst (snd sublem₂)) (fst (snd (snd (snd (snd (snd lem₁) (fst (snd (fst (snd sublem₁)))))))))
                               {pred (tc (sup B g)) (fst (snd (snd (snd (snd (snd (snd (snd lem₁) (fst (snd (fst (snd sublem₁)))))))))))}
                               {pred (tc (sup B g)) j}
                               (≐trans (pred (tc (sup B g)) (fst (snd (snd (snd (snd (snd (snd (snd lem₁) (fst (snd (fst (snd sublem₁))))))))))))
                                       (pred (tc (sup B g)) (snd (fst (snd (snd lem₁) (fst (snd (fst (snd sublem₁))))))))
                                       (pred (tc (sup B g)) j)
                                       (≐sym (pred (tc (sup B g)) (snd (fst (snd (snd lem₁) (fst (snd (fst (snd sublem₁))))))))
                                             (pred (tc (sup B g)) (fst (snd (snd (snd (snd (snd (snd (snd lem₁) (fst (snd (fst (snd sublem₁))))))))))))
                                             (snd (fst OPairAx (fst (fst (fst (fst (snd (snd (snd (snd (snd sublem₂))))))))))))
                                       (≐sym (pred (tc (sup B g)) j)
                                             (pred (tc (sup B g)) (snd (fst (snd (snd lem₁) (fst (snd (fst (snd sublem₁))))))))
                                             (snd (fst OPairAx (fst (fst OPairAx (snd (snd (fst (snd sublem₁))))))))))
                               (snd (snd (snd (snd (snd (snd sublem₂)))))))

  F' : (j : index (tc (sup B g))) → 𝕍 → 𝕍 → Set
  F' j pair b' = Σ (index (famSets₁ j)) λ k → Σ (index (tc (pred (tc (sup B g)) j))) λ j' →
                   (pair ≐ ⟨ pred (famSets₁ j) k , pred (tc (pred (tc (sup B g)) j)) j' ⟩) ×
                   (b' ≐ ⟨ ⟨ pred (tc (sup B g)) j  , ⟨ pred (famSets₁ j) k , pred (tc (pred (tc (sup B g)) j)) j' ⟩ ⟩ ,
                           fst (snd (snd (snd (lem₂ j k)))) j' ⟩)

  lem₃ : (j : index (tc (sup B g))) → ∀𝕧∈ (famSets₁ j ×𝕍 tc (pred (tc (sup B g)) j)) λ pair → Σ 𝕍 λ b' → F' j pair b'
  lem₃ j (k , j') = ⟨ ⟨ pred (tc (sup B g)) j  , ⟨ pred (famSets₁ j) k , pred (tc (pred (tc (sup B g)) j)) j' ⟩ ⟩ ,
                      fst (snd (snd (snd (lem₂ j k)))) j' ⟩ ,
                    k , j' ,
                    ≐refl ⟨ pred (famSets₁ j) k , pred (tc (pred (tc (sup B g)) j)) j' ⟩ ,
                    ≐refl ⟨ ⟨ pred (tc (sup B g)) j  , ⟨ pred (famSets₁ j) k , pred (tc (pred (tc (sup B g)) j)) j' ⟩ ⟩ ,
                            fst (snd (snd (snd (lem₂ j k)))) j' ⟩
  
  lem₄ : Σ 𝕍 λ G → ((j : index (tc (sup B g))) → ∃𝕧∈ G λ rel →
                     (∀𝕧∈ (famSets₁ j ×𝕍 tc (pred (tc (sup B g)) j)) λ pair → ∃𝕧∈ rel λ b' → F' j pair b') ×
                     (∀𝕧∈ rel λ b' → ∃𝕧∈ (famSets₁ j ×𝕍 tc (pred (tc (sup B g)) j)) λ pair → F' j pair b'))
                   ×
                   (∀𝕧∈ G λ rel → Σ (index (tc (sup B g))) λ j →
                     (∀𝕧∈ (famSets₁ j ×𝕍 tc (pred (tc (sup B g)) j)) λ pair → ∃𝕧∈ rel λ b' → F' j pair b') ×
                     (∀𝕧∈ rel λ b' → ∃𝕧∈ (famSets₁ j ×𝕍 tc (pred (tc (sup B g)) j)) λ pair → F' j pair b'))
  lem₄ =
    let sublem : (j : index (tc (sup B g))) → Σ 𝕍 λ rel →
                   (∀𝕧∈ (famSets₁ j ×𝕍 tc (pred (tc (sup B g)) j)) λ pair → ∃𝕧∈ rel λ b' → F' j pair b') ×
                   (∀𝕧∈ rel λ b' → ∃𝕧∈ (famSets₁ j ×𝕍 tc (pred (tc (sup B g)) j)) λ pair → F' j pair b')
        sublem j = StrColl {F = F' j} {a = famSets₁ j ×𝕍 tc (pred (tc (sup B g)) j)}
                           λ (k , j') → lem₃ j (k , j')
    in sup (index (tc (sup B g))) (λ j → fst (sublem j)) ,
         (λ j → j , snd (sublem j)) ,
         (λ j → j , snd (sublem j))

  fam₂Property : (j : index (tc (sup B g))) → Σ 𝕍 λ G' →
                   (x : 𝕍) → x ∈ G' ↔ ∃𝕧∈ (∪ (∪ (∪ (fst lem₄)))) λ y →
                                        (∃𝕧∈ (fst lem₄) λ rel →
                                          ∃𝕧∈ (dom (dom rel)) λ v₁ → ∃𝕧∈ (dom (ran (dom rel))) λ v₂ →
                                            ⟨ ⟨ v₁ , ⟨ v₂ , pred (tc (sup B g)) j ⟩ ⟩ , y ⟩ ∈ rel) ×
                                        (x ≐ y) 
  fam₂Property j = SepAx (λ y → (∃𝕧∈ (fst lem₄) λ rel →
                                  ∃𝕧∈ (dom (dom rel)) λ v₁ → ∃𝕧∈ (dom (ran (dom rel))) λ v₂ →
                                    ⟨ ⟨ v₁ , ⟨ v₂ , pred (tc (sup B g)) j ⟩ ⟩  , y ⟩ ∈ rel))
                         (∪ (∪ (∪ (fst lem₄))))

  famSets₂ : index (tc (sup B g)) → 𝕍
  famSets₂ j = ∪ (fst (fam₂Property j))

  famSets₂Lemma : (j₁ j₂ : index (tc (sup B g))) → pred (tc (sup B g)) j₁ ≐ pred (tc (sup B g)) j₂ → famSets₂ j₁ ≐ famSets₂ j₂
  famSets₂Lemma j₁ j₂ p =
    let q : pred (tc (sup B g)) j₂ ≐ pred (tc (sup B g)) j₁
        q = ≐sym (pred (tc (sup B g)) j₁) (pred (tc (sup B g)) j₂) p
        
        sublem : fst (fam₂Property j₁) ≐ fst (fam₂Property j₂)
        sublem = ExtAx2' {fst (fam₂Property j₁)}
                         {fst (fam₂Property j₂)}
                         λ x → (λ d → snd (snd (fam₂Property j₂) x)
                                      (fst (fst (snd (fam₂Property j₁) x) d) ,
                                       (fst (fst (snd (fst (snd (fam₂Property j₁) x) d))) ,
                                        fst (snd (fst (snd (fst (snd (fam₂Property j₁) x) d)))) ,
                                        fst (snd (snd (fst (snd (fst (snd (fam₂Property j₁) x) d))))) ,
                                        ExtAx1 {x = pred (fst lem₄) (fst (fst (snd (fst (snd (fam₂Property j₁) x) d))))}
                                               (snd OPairAx (snd OPairAx (≐refl (pred (dom (dom (pred (fst lem₄)
                                                                                        (fst (fst (snd (fst (snd (fam₂Property j₁) x) d)))))))
                                                                                      (fst (snd (fst (snd (fst (snd (fam₂Property j₁) x) d)))))) ,
                                                                          snd OPairAx (≐refl (pred (dom (ran (dom (pred (fst lem₄)
                                                                                                     (fst (fst (snd (fst (snd (fam₂Property j₁) x) d))))))))
                                                                                                   (fst (snd (snd (fst (snd (fst (snd (fam₂Property j₁) x) d))))))) ,
                                                                                       p)) ,
                                                             ≐refl (pred (∪ (∪ (∪ (fst lem₄)))) (fst (fst (snd (fam₂Property j₁) x) d)))))
                                               (snd (snd (snd (fst (snd (fst (snd (fam₂Property j₁) x) d))))))) ,
                                       snd (snd (fst (snd (fam₂Property j₁) x) d)))) ,
                               (λ d → snd (snd (fam₂Property j₁) x)
                                      (fst (fst (snd (fam₂Property j₂) x) d) ,
                                       (fst (fst (snd (fst (snd (fam₂Property j₂) x) d))) ,
                                        fst (snd (fst (snd (fst (snd (fam₂Property j₂) x) d)))) ,
                                        fst (snd (snd (fst (snd (fst (snd (fam₂Property j₂) x) d))))) ,
                                        ExtAx1 {x = pred (fst lem₄) (fst (fst (snd (fst (snd (fam₂Property j₂) x) d))))}
                                               (snd OPairAx (snd OPairAx (≐refl (pred (dom (dom (pred (fst lem₄)
                                                                                        (fst (fst (snd (fst (snd (fam₂Property j₂) x) d)))))))
                                                                                      (fst (snd (fst (snd (fst (snd (fam₂Property j₂) x) d)))))) ,
                                                                          snd OPairAx (≐refl (pred (dom (ran (dom (pred (fst lem₄)
                                                                                                     (fst (fst (snd (fst (snd (fam₂Property j₂) x) d))))))))
                                                                                                   (fst (snd (snd (fst (snd (fst (snd (fam₂Property j₂) x) d))))))) ,
                                                                                       q)) ,
                                                            ≐refl (pred (∪ (∪ (∪ (fst lem₄)))) (fst (fst (snd (fam₂Property j₂) x) d)))))
                                              (snd (snd (snd (fst (snd (fst (snd (fam₂Property j₂) x) d))))))) ,
                                      snd (snd (fst (snd (fam₂Property j₂) x) d))))
    in ∪-cong sublem

  famSets : index (tc (sup B g)) → 𝕍
  famSets j = famSets₁ j ∪b famSets₂ j

  famSetsExtensionality : (j₁ j₂ : index (tc (sup B g))) → pred (tc (sup B g)) j₁ ≐ pred (tc (sup B g)) j₂ → famSets j₁ ≐ famSets j₂
  famSetsExtensionality j₁ j₂ p = ∪b-cong (famSets₁Lemma j₁ j₂ p) (famSets₂Lemma j₁ j₂ p)

  unboundedness : (j : index (tc (sup B g))) → famSets j isUnboundedIn a
  unboundedness j i =
    let u : 𝕍
        u = fst (snd (snd (snd (fst (snd lem₁) (i , j)))))

        i' : index a
        i' = fst (snd (snd (snd (snd (fst (snd lem₁) (i , j))))))

        j' : index (tc (sup B g))
        j' = fst (snd (snd (snd (snd (snd (fst (snd lem₁) (i , j)))))))

        sublem₁ : u ∈ a × pred a i' ∈ u
        sublem₁ = snd (fst (fst (snd (snd (snd (snd (snd (snd (fst (snd lem₁) (i , j)))))))))) ,
                  snd (fst (snd (snd (snd (snd (snd (snd (fst (snd lem₁) (i , j)))))))))

        sublem₂ : ⟨ ⟨ pred a i' , pred (tc (sup B g)) j' ⟩ ,
                      fst (snd (snd (z-inacc-ub-in-a (fst (fst (fst (snd lem₁) (i , j)))) (snd (fst (fst (snd lem₁) (i , j))))))) ⟩ ≐
                  ⟨ ⟨ pred a i' , pred (tc (sup B g)) j ⟩ , pred a (fst (snd (fst (fst (snd (snd (snd (snd (snd (snd (fst (snd lem₁) (i , j)))))))))))) ⟩
        sublem₂ = snd OPairAx (snd OPairAx (≐refl (pred a i') ,
                                            ≐sym (pred (tc (sup B g)) j)
                                                 (pred (tc (sup B g)) j')
                                                 (snd (fst OPairAx (fst (fst (fst (fst (snd (snd (snd (snd (snd (snd (fst (snd lem₁) (i , j))))))))))))))) ,
                               ≐trans (fst (snd (snd (z-inacc-ub-in-a (fst (fst (fst (snd lem₁) (i , j)))) (snd (fst (fst (snd lem₁) (i , j))))))))
                                      u
                                      (pred a (fst (snd (fst (fst (snd (snd (snd (snd (snd (snd (fst (snd lem₁) (i , j)))))))))))))
                                      (snd (fst OPairAx (snd (fst (fst (fst (snd (snd (snd (snd (snd (snd (fst (snd lem₁) (i , j))))))))))))))
                                      (snd (fst sublem₁)))
        
        sublem₃ : u ∈ famSets j
        sublem₃ = snd (∪b-proof (famSets₁ j) (famSets₂ j) u)
                        (injl (snd (snd (fam₁Property j) u) (fst (fst sublem₁) ,
                                                            (i' ,
                                                             ExtAx1 {x = fst lem₁}
                                                                    sublem₂
                                                                    (fst (fst (snd lem₁) (i , j)) , ≐refl (pred (fst lem₁) (fst (fst (snd lem₁) (i , j)))))) ,
                                                            snd (fst sublem₁))))
    in fst sublem₃ ,
       fst (ExtAx2 (snd sublem₃) (pred a i))
             (ExtAx1 {x = u}
                     (≐sym (pred a i)
                           (pred a i')
                           (fst (fst OPairAx (fst (fst (fst (fst (snd (snd (snd (snd (snd (snd (fst (snd lem₁) (i , j)))))))))))))))
                     (snd sublem₁)) ,
       ExtAx1 {x = a}
              (snd sublem₃)
              (fst sublem₁)

  inaccessibility : (j : index (tc (sup B g))) → ∀𝕧∈ (famSets j) λ u → Σ Set (λ U' → Σ (U' → Set) (λ T' → [ U' , T' , u ]-isInacc))
  inaccessibility j k =
    let sublem₁ : pred (famSets j) k ∈ famSets₁ j ⊕ pred (famSets j) k ∈ famSets₂ j
        sublem₁ = fst (∪b-proof (famSets₁ j) (famSets₂ j) (pred (famSets j) k)) (k , ≐refl (pred (famSets j) k))

        sublem₂ : pred (famSets j) k ∈ famSets₁ j → Σ Set (λ U' → Σ (U' → Set) (λ T' → [ U' , T' , pred (famSets j) k ]-isInacc))
        sublem₂ leftProof =
          let subsublem₁ : ⟨ ⟨ pred a (fst (fst (snd (fst (snd (fam₁Property j) (pred (famSets j) k)) leftProof)))) ,
                               pred (tc (sup B g)) j ⟩ ,
                             pred a (fst (fst (snd (fam₁Property j) (pred (famSets j) k)) leftProof)) ⟩ ∈ fst lem₁
              subsublem₁ = snd (fst (snd (fst (snd (fam₁Property j) (pred (famSets j) k)) leftProof)))

              subsublem₂ : F (pred (a ×𝕍 tc (sup B g)) (fst (snd (snd lem₁) (fst subsublem₁)))) (pred (fst lem₁) (fst subsublem₁))
              subsublem₂ = snd (snd (snd lem₁) (fst subsublem₁))
          in fst subsublem₂ ,
             fst (snd subsublem₂) ,
             fst (αInacc-inv (fst subsublem₂)
                             (fst (snd subsublem₂))
                             (pred (tc (sup B g)) (fst (snd (snd (snd (snd subsublem₂))))))
                             {a = fst (snd (snd subsublem₂))}
                             {b = pred (famSets j) k}
                             (≐trans (fst (snd (snd subsublem₂)))
                                     (fst (snd (snd (z-inacc-ub-in-a (fst (fst subsublem₁)) (snd (fst subsublem₁))))))
                                     (pred (famSets j) k)
                                     (≐sym (fst (snd (snd (z-inacc-ub-in-a (fst (fst subsublem₁)) (snd (fst subsublem₁))))))
                                           (fst (snd (snd subsublem₂)))
                                           (snd (fst OPairAx (snd (fst (fst (fst (snd (snd (snd (snd (snd subsublem₂))))))))))))
                                     (≐trans (fst (snd (snd (z-inacc-ub-in-a (fst (fst subsublem₁)) (snd (fst subsublem₁))))))
                                             (pred a (fst (fst (snd (fam₁Property j) (pred (famSets j) k)) leftProof)))
                                             (pred (famSets j) k)
                                             (≐sym (pred a (fst (fst (snd (fam₁Property j) (pred (famSets j) k)) leftProof)))
                                                   (fst (snd (snd (z-inacc-ub-in-a (fst (fst subsublem₁)) (snd (fst subsublem₁))))))
                                                   (snd (fst OPairAx (snd subsublem₁))))
                                             (≐sym (pred (famSets j) k)
                                                   (pred a (fst (fst (snd (fam₁Property j) (pred (famSets j) k)) leftProof)))
                                                   (snd (snd (fst (snd (fam₁Property j) (pred (famSets j) k)) leftProof))))))
                             (snd (snd (snd (snd (snd (snd subsublem₂)))))))

        sublem₃ : pred (famSets j) k ∈ famSets₂ j → Σ Set (λ U' → Σ (U' → Set) (λ T' → [ U' , T' , pred (famSets j) k ]-isInacc))
        sublem₃ rightProof =
          let subsublem₁ : ∃𝕧∈ (fst (fam₂Property j)) λ x → pred (famSets j) k ∈ x
              subsublem₁ = fst (∪-proof (fst (fam₂Property j)) (pred (famSets j) k)) rightProof
              
              eq : pred (famSets j) k ≐ pred (pred (fst (fam₂Property j)) (fst subsublem₁)) (fst (snd subsublem₁))
              eq = snd (snd subsublem₁)
              
              idx : index (∪ (∪ (∪ (fst lem₄))))
              idx = fst (fst (snd (fam₂Property j) (pred (fst (fam₂Property j)) (fst subsublem₁)))
                               (fst subsublem₁ , ≐refl (pred (fst (fam₂Property j)) (fst subsublem₁))))
              
              subsublem₂ : (∃𝕧∈ (fst lem₄) λ rel → ∃𝕧∈ (dom (dom rel)) λ v₁ → ∃𝕧∈ (dom (ran (dom rel))) λ v₂ →
                             ⟨ ⟨ v₁ , ⟨ v₂ , pred (tc (sup B g)) j ⟩ ⟩ , pred (∪ (∪ (∪ (fst lem₄)))) idx ⟩ ∈ rel) ×
                           (pred (fst (fam₂Property j)) (fst subsublem₁) ≐ pred (∪ (∪ (∪ (fst lem₄)))) idx)
              subsublem₂ =  snd (fst (snd (fam₂Property j) (pred (fst (fam₂Property j)) (fst subsublem₁)))
                                     (fst subsublem₁ , ≐refl (pred (fst (fam₂Property j)) (fst subsublem₁))))
              
              subsublem₃ : Σ 𝕍 λ y → ⟨ y , pred (∪ (∪ (∪ (fst lem₄)))) idx ⟩ ∈ pred (fst lem₄) (fst (fst subsublem₂))
              subsublem₃ = ⟨ pred (dom (dom (pred (fst lem₄) (fst (fst subsublem₂))))) (fst (snd (fst subsublem₂))) ,
                             ⟨ pred (dom (ran (dom (pred (fst lem₄) (fst (fst subsublem₂)))))) (fst (snd (snd (fst subsublem₂)))) ,
                               pred (tc (sup B g)) j ⟩ ⟩ ,
                             snd (snd (snd (fst subsublem₂)))

              t : 𝕍
              t = fst (snd (snd (snd (lem₂ (fst (fst subsublem₂)) (fst (fst (snd subsublem₃))))))) (snd (fst (snd subsublem₃)))

              subsublem₄ : pred (famSets j) k ∈ t
              subsublem₄ = fst (ExtAx2 {pred (fst (fam₂Property j)) (fst subsublem₁)}
                                       {t}
                                       (≐trans (pred (fst (fam₂Property j)) (fst subsublem₁))
                                               (pred (∪ (∪ (∪ (fst lem₄)))) idx)
                                               t
                                               (snd subsublem₂)
                                               (snd (fst OPairAx (snd (snd subsublem₃)))))
                                       (pred (famSets j) k))
                               (snd subsublem₁)
                               
              subsublem₅ : Σ Set λ U' → Σ (U' → Set) λ T' → [ U' , T' , pred t (fst subsublem₄) ]-isInacc
              subsublem₅ = snd (fst (snd (snd (snd (snd (snd (lem₂ (fst (fst subsublem₂)) (fst (fst (snd subsublem₃))))))))
                                           (snd (fst (snd subsublem₃)))))
                                 (fst subsublem₄)              
          in fst subsublem₅ , fst (snd subsublem₅) ,
             Inacc-inv (fst subsublem₅) (fst (snd subsublem₅))
                       {pred t (fst subsublem₄)} {pred (famSets j) k}
                       (≐sym (pred (famSets j) k)
                             (pred t (fst subsublem₄))
                             (snd subsublem₄))
                       (snd (snd subsublem₅)) 

    in ⊕elim (λ _ → Σ Set (λ U' → Σ (U' → Set) (λ T' → [ U' , T' , pred (famSets j) k ]-isInacc)))
             sublem₂
             sublem₃
             sublem₁


  module _
    (j : index (tc (sup B g)))
    (k : index (famSets j))
    where


    leftSublemma : pred (famSets j) k ∈ famSets₁ j → (j' : index (tc (pred (tc (sup B g)) j))) →
                     famSets (index-trans (sup B g) j j') isUnboundedIn pred (famSets j) k
    leftSublemma leftProof j' i =
      let famSets' : index (tc (pred (tc (sup B g)) j)) → 𝕍
          famSets' = fst (snd (snd (snd (lem₂ j (fst leftProof)))))

          subsublem₁ : famSets' j' isUnboundedIn pred (famSets j) k
          subsublem₁ = unbounded-inv' (famSets' j')
                                      (≐sym (pred (famSets j) k) (pred (famSets₁ j) (fst leftProof)) (snd leftProof))
                                      (fst (fst ((snd (snd (snd (snd (snd (lem₂ j (fst leftProof))))))) j')))

          helper : ∃𝕧∈ (pred (fst lem₄) (fst (fst (snd lem₄) j))) λ triple →
                         F' j (pred (famSets₁ j ×𝕍 tc (pred (tc (sup B g)) j)) (fst leftProof , j')) triple
          helper = fst (snd (fst (snd lem₄) j)) (fst leftProof , j')

          t₁ : 𝕍
          t₁ = ⟨ pred (tc (sup B g)) j  ,
                 ⟨ pred (famSets₁ j) (fst (snd helper)) , pred (tc (pred (tc (sup B g)) j)) (fst (snd (snd helper))) ⟩ ⟩

          subsublem₂ : famSets' j' ∈ pair-set t₁ (famSets' j')
          subsublem₂ = snd (pair-set-proof t₁ (famSets' j') (famSets' j')) (injr (≐refl (famSets' j')))

          subsublem₃ : pair-set t₁ (famSets' j') ∈ ⟨ t₁ , famSets' j' ⟩
          subsublem₃ = snd (pair-set-proof (sglt t₁) (pair-set t₁ (famSets' j')) (pair-set t₁ (famSets' j'))) (injr (≐refl (pair-set t₁ (famSets' j'))))

          subsublem₄ : ⟨ t₁ , famSets' j' ⟩ ∈ pred (fst lem₄) (fst (fst (snd lem₄) j))
          subsublem₄ = ExtAx1 {x = pred (fst lem₄) (fst (fst (snd lem₄) j))}
                              (snd (snd (snd (snd helper))))
                              (fst helper , ≐refl (pred (pred (fst lem₄) (fst (fst (snd lem₄) j))) (fst helper)))

          subsublem₅ : famSets' j' ∈ ∪ (∪ (∪ (fst lem₄)))
          subsublem₅ = snd (∪-proof (∪ (∪ (fst lem₄))) (famSets' j'))
                           (fst (snd (∪-proof (∪ (fst lem₄)) (pair-set t₁ (famSets' j')))
                                     (fst (snd (∪-proof (fst lem₄) ⟨ t₁ , famSets' j' ⟩)
                                               (fst (fst (snd lem₄) j) ,
                                                ExtAx1 (snd (snd (snd (snd helper))))
                                                       (fst helper , ≐refl (pred (pred (fst lem₄) (fst (fst (snd lem₄) j))) (fst helper))))) ,
                                           fst (ExtAx2 {⟨ t₁ , famSets' j' ⟩}
                                                       {pred (∪ (fst lem₄))
                                                             (fst (snd (∪-proof (fst lem₄) ⟨ t₁ , famSets' j' ⟩) (fst (fst (snd lem₄) j) , subsublem₄)))}
                                                       (snd (snd (∪-proof (fst lem₄) ⟨ t₁ , famSets' j' ⟩) (fst (fst (snd lem₄) j) , subsublem₄)))
                                                       (pair-set t₁ (famSets' j')))
                                           subsublem₃)) ,
                                fst (ExtAx2 {pair-set t₁ (famSets' j')} (snd subsublem₃) (famSets' j')) subsublem₂)

          t₂ : 𝕍  -- t₂ is definitionally equal to famSets' j'
          t₂ = fst (snd (snd (snd (lem₂ j (fst (snd helper)))))) (fst (snd (snd helper)))

          helper' : ⟨ ⟨ pred (tc (sup B g)) j  , ⟨ pred (famSets₁ j) (fst leftProof) , pred (tc (pred (tc (sup B g)) j)) j' ⟩ ⟩ , t₂ ⟩ ∈
                      pred (fst lem₄) (fst (fst (snd lem₄) j))
          helper' = ExtAx1 {x = pred (fst lem₄) (fst (fst (snd lem₄) j))}
                           (snd (snd (snd (snd helper))))
                           (fst helper , ≐refl (pred (pred (fst lem₄) (fst (fst (snd lem₄) j))) (fst helper)))

          subsublem₆ : pred (tc (sup B g)) j ∈  dom (dom (pred (fst lem₄) (fst (fst (snd lem₄) j))))
          subsublem₆ = snd (dom-proof (dom (pred (fst lem₄) (fst (fst (snd lem₄) j)))) (pred (tc (sup B g)) j))
                           (⟨ pred (famSets₁ j) (fst leftProof) , pred (tc (pred (tc (sup B g)) j)) j' ⟩ ,
                            snd (dom-proof (pred (fst lem₄) (fst (fst (snd lem₄) j)))
                                           ⟨ pred (tc (sup B g)) j  ,
                                             ⟨ pred (famSets₁ j) (fst leftProof) ,
                                               pred (tc (pred (tc (sup B g)) j)) j' ⟩ ⟩)
                                (t₂ , helper'))

          subsublem₇ : pred (famSets₁ j) (fst leftProof) ∈ dom (ran (dom (pred (fst lem₄) (fst (fst (snd lem₄) j)))))
          subsublem₇ = snd (dom-proof (ran (dom (pred (fst lem₄) (fst (fst (snd lem₄) j)))))
                                       (pred (famSets₁ j) (fst leftProof)))
                           (pred (tc (pred (tc (sup B g)) j)) j' ,
                            snd (ran-proof (dom (pred (fst lem₄) (fst (fst (snd lem₄) j))))
                                            ⟨ pred (famSets₁ j) (fst leftProof) , pred (tc (pred (tc (sup B g)) j)) j' ⟩)
                                (pred (tc (sup B g)) j ,
                                 snd (dom-proof (pred (fst lem₄) (fst (fst (snd lem₄) j)))
                                                ⟨ pred (tc (sup B g)) j  ,
                                                  ⟨ pred (famSets₁ j) (fst leftProof) ,
                                                    pred (tc (pred (tc (sup B g)) j)) j' ⟩ ⟩)
                                     (t₂ , helper')))

          subsublem₈ : famSets' j' ∈ fst (fam₂Property (index-trans (sup B g) j j'))
          subsublem₈ = snd (snd (fam₂Property (index-trans (sup B g) j j')) (famSets' j'))
                           (fst subsublem₅ ,
                            (fst (fst (snd lem₄) j) ,
                             fst subsublem₆ ,
                             fst subsublem₇ ,
                             ExtAx1 {x = pred (fst lem₄) (fst (fst (snd lem₄) j))}
                                    (snd OPairAx (snd OPairAx (snd subsublem₆ ,
                                                               snd OPairAx (snd subsublem₇ ,
                                                                            index-trans≐ (sup B g) j j')) ,
                                                  snd subsublem₅))
                                    helper') ,
                            snd subsublem₅)

          subsublem₉ : pred (famSets' j') (fst (subsublem₁ i)) ∈ famSets (index-trans (sup B g) j j')
          subsublem₉ = snd (∪b-proof (famSets₁ (index-trans (sup B g) j j'))
                                     (famSets₂ (index-trans (sup B g) j j'))
                                     (pred (famSets' j') (fst (subsublem₁ i))))
                           (injr (snd (∪-proof (fst (fam₂Property (index-trans (sup B g) j j')))
                                               (pred (famSets' j') (fst (subsublem₁ i))))
                                      (fst subsublem₈ , fst (ExtAx2 (snd subsublem₈) (pred (famSets' j') (fst (subsublem₁ i))))
                                                            (fst (subsublem₁ i) , ≐refl (pred (famSets' j') (fst (subsublem₁ i)))))))
      in fst subsublem₉ ,
           fst (ExtAx2 (snd subsublem₉) (pred (pred (famSets j) k) i)) (fst (snd (subsublem₁ i))) ,
           ExtAx1 {x = pred (famSets j) k} (snd subsublem₉) (snd (snd (subsublem₁ i)))


  module _
    (j : index (tc (sup B g)))
    (k : index (famSets j))
    (rightProof : pred (famSets j) k ∈ famSets₂ j)
    (j' : index (tc (pred (tc (sup B g)) j)))
    where


    t₁ : 𝕍
    t₁ = pred (fst (fam₂Property j)) (fst (fst (∪-proof (fst (fam₂Property j)) (pred (famSets j) k)) rightProof))

    k∈t₁ : pred (famSets j) k ∈ t₁
    k∈t₁ = snd (fst (∪-proof (fst (fam₂Property j)) (pred (famSets j) k)) rightProof)

    subsublem₁ : ∃𝕧∈ (∪ (∪ (∪ (fst lem₄)))) λ y → (∃𝕧∈ (fst lem₄) λ rel →
                                                     ∃𝕧∈ (dom (dom rel)) λ v₁ →
                                                       ∃𝕧∈ (dom (ran (dom rel))) λ v₂ →
                                                         ⟨ ⟨ v₁ , ⟨ v₂ , pred (tc (sup B g)) j ⟩ ⟩ , y ⟩ ∈ rel) ×
                                                  (t₁ ≐ y)
    subsublem₁ = fst (snd (fam₂Property j) t₁) (fst (fst (∪-proof (fst (fam₂Property j)) (pred (famSets j) k)) rightProof) , ≐refl t₁)

    rel' : 𝕍
    rel' = pred (fst lem₄) (fst (fst (snd subsublem₁)))

    idx₁ : index (tc (sup B g))
    idx₁ = fst (snd (snd lem₄) (fst (fst (snd subsublem₁))))

    pair' : 𝕍
    pair' = pred (famSets₁ idx₁ ×𝕍 tc (pred (tc (sup B g)) idx₁))
              (fst (snd (snd (snd (snd lem₄) (fst (fst (snd subsublem₁))))) (fst (snd (snd (snd (fst (snd subsublem₁))))))))

    triple₁ : 𝕍
    triple₁ = pred rel' (fst (snd (snd (snd (fst (snd subsublem₁))))))

    subsublem₂ : F' idx₁ pair' triple₁
    subsublem₂ = snd (snd (snd (snd (snd lem₄) (fst (fst (snd subsublem₁))))) (fst (snd (snd (snd (fst (snd subsublem₁)))))))

    idx₂ : index (famSets₁ idx₁)
    idx₂ = fst subsublem₂

    idx₃ : index (tc (pred (tc (sup B g)) idx₁))
    idx₃ = fst (snd subsublem₂)

    t₂ : 𝕍
    t₂ = fst (snd (snd (snd (lem₂ idx₁ idx₂)))) idx₃

    subsublem₃ : t₁ ≐ t₂
    subsublem₃ = ≐trans t₁
                        (pred (∪ (∪ (∪ (fst lem₄)))) (fst subsublem₁))
                        t₂
                        (snd (snd subsublem₁))
                        (≐trans (pred (∪ (∪ (∪ (fst lem₄)))) (fst subsublem₁))
                                (fst (snd (snd (snd (lem₂ (fst (fst (snd subsublem₁)))
                                                          (fst (fst (snd (snd (snd (fst (snd subsublem₁)))))))))))
                                     (snd (fst (snd (snd (snd (fst (snd subsublem₁))))))))
                                t₂
                                (snd (fst OPairAx (snd (snd (snd (snd (fst (snd subsublem₁))))))))
                                (snd (fst OPairAx (snd (snd (snd subsublem₂))))))

    subsublem₄ : pred (famSets j) k ∈ t₂
    subsublem₄ = fst (ExtAx2 {t₁} {t₂} subsublem₃ (pred (famSets j) k)) k∈t₁

    subsublem₅ : pred (tc (sup B g)) j ≐ pred (tc (pred (tc (sup B g)) idx₁)) idx₃
    subsublem₅ = ≐trans (pred (tc (sup B g)) j)
                        (pred (tc (pred (tc (sup B g)) (fst (fst (snd subsublem₁)))))
                              (snd (fst (snd (snd (snd (fst (snd subsublem₁))))))))
                        (pred (tc (pred (tc (sup B g)) idx₁)) idx₃)
                        (snd (fst OPairAx (snd (fst OPairAx (fst (fst OPairAx (snd (snd (snd (snd (fst (snd subsublem₁))))))))))))
                        (snd (fst OPairAx (snd (fst OPairAx (fst (fst OPairAx (snd (snd (snd subsublem₂)))))))))

    subsublem₆ : Σ (index (tc (pred (tc (pred (tc (sup B g)) idx₁)) idx₃))) λ j₁ →
                   pred (tc (pred (tc (sup B g)) j)) j' ≐ pred (tc (pred (tc (pred (tc (sup B g)) idx₁)) idx₃)) j₁
    subsublem₆ = ip-compat (tc-cong' subsublem₅) j'

    t₃ : 𝕍
    t₃ = fst (snd (snd (snd (lem₂ idx₁ idx₂)))) (index-trans (pred (tc (sup B g)) idx₁) idx₃ (fst subsublem₆))

    subsublem₇ : t₃ isUnboundedIn pred (famSets j) k
    subsublem₇ = unbounded-inv' t₃
                                (≐sym (pred (famSets j) k)
                                      (pred t₂ (fst subsublem₄))
                                      (snd subsublem₄))
                                (snd (snd (snd (snd (snd (snd (lem₂ idx₁ idx₂))))) idx₃) (fst subsublem₄) (fst subsublem₆))

    helper : F' idx₁
                (pred (famSets₁ idx₁ ×𝕍 tc (pred (tc (sup B g)) idx₁)) (idx₂ , index-trans (pred (tc (sup B g)) idx₁) idx₃ (fst subsublem₆)))
                (pred (pred (fst lem₄) (fst (fst (snd lem₄) idx₁)))
                  (fst (fst (snd (fst (snd lem₄) idx₁)) (idx₂ , index-trans (pred (tc (sup B g)) idx₁) idx₃ (fst subsublem₆)))))
    helper = snd (fst (snd (fst (snd lem₄) idx₁)) (idx₂ , (index-trans (pred (tc (sup B g)) idx₁) idx₃ (fst subsublem₆))))

    idx₄ : index (famSets₁ idx₁)
    idx₄ = fst (snd (fst (snd (fst (snd lem₄) idx₁)) (idx₂ , index-trans (pred (tc (sup B g)) idx₁) idx₃ (fst subsublem₆))))

    idx₅ : index (tc (pred (tc (sup B g)) idx₁))
    idx₅ = fst (snd (snd (fst (snd (fst (snd lem₄) idx₁)) (idx₂ , index-trans (pred (tc (sup B g)) idx₁) idx₃ (fst subsublem₆)))))

    -- t₃ is definitionally equal to fst (snd (snd (snd (lem₂ idx₁ idx₄)))) idx₅

    helper' : index (pred (fst lem₄) (fst (fst (snd lem₄) idx₁)))
    helper' = fst (fst (snd (fst (snd lem₄) idx₁)) (idx₂ , (index-trans (pred (tc (sup B g)) idx₁) idx₃ (fst subsublem₆))))

    subsublem₈ : pred (tc (sup B g)) (index-trans (sup B g) j j') ≐ pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper')
    subsublem₈ = ≐trans (pred (tc (sup B g)) (index-trans (sup B g) j j'))
                        (pred (tc (pred (tc (sup B g)) idx₁)) (fst (snd helper)))
                        (pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper'))
                        (≐trans (pred (tc (sup B g)) (index-trans (sup B g) j j'))
                                (pred (tc (pred (tc (sup B g)) j)) j')
                                (pred (tc (pred (tc (sup B g)) idx₁)) (fst (snd helper)))
                                (≐sym (pred (tc (pred (tc (sup B g)) j)) j')
                                      (pred (tc (sup B g)) (index-trans (sup B g) j j'))
                                      (index-trans≐ (sup B g) j j'))
                                (≐trans (pred (tc (pred (tc (sup B g)) j)) j')
                                        (pred (tc (pred (tc (pred (tc (sup B g)) idx₁)) idx₃)) (fst subsublem₆))
                                        (pred (tc (pred (tc (sup B g)) idx₁)) (fst (snd helper)))
                                        (snd subsublem₆)
                                        (≐trans (pred (tc (pred (tc (pred (tc (sup B g)) idx₁)) idx₃)) (fst subsublem₆))
                                                (pred (tc (pred (tc (sup B g)) idx₁)) (index-trans (pred (tc (sup B g)) idx₁) idx₃ (fst subsublem₆)))
                                                (pred (tc (pred (tc (sup B g)) idx₁)) (fst (snd helper)))
                                                (index-trans≐ (pred (tc (sup B g)) idx₁) idx₃ (fst subsublem₆))
                                                (snd (fst OPairAx (fst (snd (snd helper))))))))
                        (≐sym (pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper'))
                              (pred (tc (pred (tc (sup B g)) idx₁)) (fst (snd helper)))
                              (snd (fst OPairAx (snd (fst OPairAx (fst (fst OPairAx (snd (snd (snd helper))))))))))

    triple₂ : 𝕍
    triple₂ = ⟨ pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)) ,
                ⟨ pred (famSets₁ (fst (fst (snd lem₄) idx₁))) (fst helper') ,
                  pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper') ⟩ ⟩

    subsublem₉ : t₃ ∈ pair-set triple₂ t₃
    subsublem₉ = snd (pair-set-proof triple₂ t₃ t₃) (injr (≐refl t₃))

    subsublem₁₀ : pair-set triple₂ t₃ ∈ ⟨ triple₂ , t₃ ⟩
    subsublem₁₀ = snd (pair-set-proof (sglt triple₂) (pair-set triple₂ t₃) (pair-set triple₂ t₃)) (injr (≐refl (pair-set triple₂ t₃)))

    subsublem₁₁ : pair-set triple₂ t₃ ∈ ∪ (∪ (fst lem₄))
    subsublem₁₁ = snd (∪-proof (∪ (fst lem₄)) (pair-set triple₂ t₃))
                        (fst (snd (∪-proof (fst lem₄) ⟨ triple₂ , t₃ ⟩) (fst (fst (snd lem₄) idx₁) , helper' , ≐refl ⟨ triple₂ , t₃ ⟩)) ,
                         fst (ExtAx2 {⟨ triple₂ , t₃ ⟩}
                                     {pred (∪ (fst lem₄)) (fst (snd (∪-proof (fst lem₄) ⟨ triple₂ , t₃ ⟩)
                                                                      (fst (fst (snd lem₄) idx₁) , helper' , ≐refl ⟨ triple₂ , t₃ ⟩)))}
                                     (snd (snd (∪-proof (fst lem₄) ⟨ triple₂ , t₃ ⟩) (fst (fst (snd lem₄) idx₁) , helper' , ≐refl ⟨ triple₂ , t₃ ⟩)))
                                     (pair-set triple₂ t₃))
                             subsublem₁₀)

    subsublem₁₂ : t₃ ∈ ∪ (∪ (∪ (fst lem₄)))
    subsublem₁₂ = snd (∪-proof (∪ (∪ (fst lem₄))) t₃)
                        (fst subsublem₁₁ ,
                         fst (ExtAx2 {pair-set triple₂ t₃} {pred (∪ (∪ (fst lem₄))) (fst subsublem₁₁)} (snd subsublem₁₁) t₃) subsublem₉)

    subsublem₁₃ : pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)) ∈ dom (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁))))
    subsublem₁₃ = snd (dom-proof (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁))))
                                  (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁))))
                      (⟨ pred (famSets₁ (fst (fst (snd lem₄) idx₁))) (fst helper') ,
                         pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper') ⟩ ,
                       snd (dom-proof (pred (fst lem₄) (fst (fst (snd lem₄) idx₁)))
                                      triple₂)
                           (t₃ , helper' , ≐refl ⟨ triple₂ , t₃ ⟩))

    subsublem₁₄ : pred (famSets₁ (fst (fst (snd lem₄) idx₁))) (fst helper') ∈ dom (ran (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁)))))
    subsublem₁₄ = snd (dom-proof (ran (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁)))))
                                 (pred (famSets₁ (fst (fst (snd lem₄) idx₁))) (fst helper')))
                      (pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper') ,
                       snd (ran-proof (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁))))
                                      ⟨ pred (famSets₁ (fst (fst (snd lem₄) idx₁))) (fst helper') ,
                                        pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper') ⟩)
                           (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)) ,
                            snd (dom-proof (pred (fst lem₄) (fst (fst (snd lem₄) idx₁)))
                                           triple₂)
                                (t₃ , helper' , ≐refl ⟨ triple₂ , t₃ ⟩)))

    pairEq₁ : ⟨ pred (famSets₁ (fst (fst (snd lem₄) idx₁))) (fst helper') ,
                pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper') ⟩
              ≐
              ⟨ pred (dom (ran (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁)))))) (fst subsublem₁₄) ,
                pred (tc (sup B g)) (index-trans (sup B g) j j') ⟩
    pairEq₁ = snd OPairAx (snd subsublem₁₄ ,
                           ≐sym (pred (tc (sup B g)) (index-trans (sup B g) j j'))
                                (pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper'))
                                 subsublem₈)

    pairEq₂ : ⟨ pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)) ,
                ⟨ pred (famSets₁ (fst (fst (snd lem₄) idx₁))) (fst helper') ,
                  pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper') ⟩ ⟩
              ≐
              ⟨ pred (dom (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁))))) (fst subsublem₁₃) ,
                ⟨ pred (dom (ran (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁)))))) (fst subsublem₁₄) ,
                  pred (tc (sup B g)) (index-trans (sup B g) j j') ⟩ ⟩
    pairEq₂ = snd OPairAx (snd subsublem₁₃ , pairEq₁)

    pairEq₃ : ⟨ ⟨ pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)) ,
                  ⟨ pred (famSets₁ (fst (fst (snd lem₄) idx₁))) (fst helper') ,
                    pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper') ⟩ ⟩ ,
                t₃ ⟩
              ≐
              ⟨ ⟨ pred (dom (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁))))) (fst subsublem₁₃) ,
                  ⟨ pred (dom (ran (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁)))))) (fst subsublem₁₄) ,
                    pred (tc (sup B g)) (index-trans (sup B g) j j') ⟩ ⟩ ,
                pred (∪ (∪ (∪ (fst lem₄)))) (fst subsublem₁₂) ⟩
    pairEq₃ = snd OPairAx (pairEq₂ , snd subsublem₁₂)

    subsublem₁₅ : t₃ ∈ fst (fam₂Property (index-trans (sup B g) j j'))
    subsublem₁₅ = snd (snd (fam₂Property (index-trans (sup B g) j j')) t₃)
                     (fst subsublem₁₂ ,
                      (fst (fst (snd lem₄) idx₁) ,
                       fst subsublem₁₃ ,
                       fst subsublem₁₄ ,
                       ExtAx1 {⟨ ⟨ pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)) ,
                                   ⟨ pred (famSets₁ (fst (fst (snd lem₄) idx₁))) (fst helper') ,
                                     pred (tc (pred (tc (sup B g)) (fst (fst (snd lem₄) idx₁)))) (snd helper') ⟩ ⟩ ,
                                 t₃ ⟩}
                              {⟨ ⟨ pred (dom (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁))))) (fst subsublem₁₃) ,
                                   ⟨ pred (dom (ran (dom (pred (fst lem₄) (fst (fst (snd lem₄) idx₁)))))) (fst subsublem₁₄) ,
                                     pred (tc (sup B g)) (index-trans (sup B g) j j') ⟩ ⟩ ,
                                 pred (∪ (∪ (∪ (fst lem₄)))) (fst subsublem₁₂) ⟩}
                              {pred (fst lem₄) (fst (fst (snd lem₄) idx₁))}
                              pairEq₃
                              (helper' , ≐refl ⟨ triple₂ , t₃ ⟩)) ,
                      snd subsublem₁₂)

    famSetsSublemma : (x : index (pred (famSets j) k)) → pred t₃ (fst (subsublem₇ x)) ∈ famSets (index-trans (sup B g) j j')
    famSetsSublemma x = snd (∪b-proof (famSets₁ (index-trans (sup B g) j j'))
                                  (famSets₂ (index-trans (sup B g) j j'))
                                  (pred t₃ (fst (subsublem₇ x))))
                          (injr (snd (∪-proof (fst (fam₂Property (index-trans (sup B g) j j')))
                                              (pred t₃ (fst (subsublem₇ x))))
                                       (fst subsublem₁₅ ,
                                        fst (ExtAx2 {t₃}
                                                    {pred (fst (fam₂Property (index-trans (sup B g) j j'))) (fst subsublem₁₅)}
                                                    (snd subsublem₁₅)
                                                    (pred t₃ (fst (subsublem₇ x))))
                                              (fst (subsublem₇ x) , ≐refl (pred t₃ (fst (subsublem₇ x)))))))
