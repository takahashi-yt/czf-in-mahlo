{-# OPTIONS --cubical-compatible #-}

module PiNumbersAxiom where

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
open import Inaccessibles.HierarchyLemma

private variable
  a : 𝕍
  t : Acc a
  c : 𝔽 0


sgltV : (v : 𝕍) → v ∈ V a t c → sglt v ∈ V a t c
sgltV {a} {prog f} {c} v d =
  sgltV̂ a (prog f) c (fst d) ,
    (λ _ → tt , snd d) , (λ _ → tt , snd d)

mainLemma : {a v : 𝕍} {f : (x : index (tc a)) → Acc (pred (tc a) x)} {c : 𝔽 0} →
              v ∈ V a (prog f) c → (u : index (tc a)) →
                Σ (Û a (prog f) c) λ b → Σ (T̂ a (prog f) c b → Û a (prog f) c) λ g →
                  v ∈ V (pred (tc a) u) (f u) (T̂ a (prog f) c b , λ x → T̂ a (prog f) c (g x)) ×
                  V (pred (tc a) u) (f u) (T̂ a (prog f) c b , λ x → T̂ a (prog f) c (g x)) ∈ V a (prog f) c
mainLemma {a} {v} {f} {c} v∈V u =
  index βindex , (λ z → index (pred βindex z)) , v∈𝕍̂ ,
    ExtAx1 β'≐𝕍̂ (sup (codeW code𝕌̂ decode𝕌̂) β'pred , ≐refl β')
  where
  βindex : V̂ a (prog f) c
  βindex = fst (V-REA {a} {prog f} {c} (fst (sgltV v v∈V)))

  β : 𝕍
  β = h a (prog f) c βindex

  β-transitive : isTransitive β
  β-transitive = snd (fst (snd (snd (V-REA {a} {prog f} {c} (fst (sgltV v v∈V))))))

  β≐ : β ≐ sup (T̂ a (prog f) c (index βindex)) λ y → h a (prog f) c (pred βindex y)
  β≐ = fst (h-iso {a} {prog f} {c} {βindex} {sup (index βindex) (pred βindex)})
         (≐'eta {a} {prog f} {c} βindex)

  b' : Set
  b' = T̂ a (prog f) c (index βindex)

  g' : T̂ a (prog f) c (index βindex) → Set
  g' w = T̂ a (prog f) c (index (pred βindex w))

  𝕍̂ : 𝕍
  𝕍̂ = V (pred (tc a) u) (f u) (b' , g')

  β⊆𝕍̂ : (w : 𝕍) → w ∈ β → w ∈ 𝕍̂
  β⊆𝕍̂ (sup x l) w∈β =
    let z' : T̂ a (prog f) c (index βindex)
        z' = fst (ip-compat (fst (h-iso {a} {prog f} {c} {βindex} {sup (index βindex) (pred βindex)})
                                   (≐'eta {a} {prog f} {c} βindex)) (fst w∈β))

        C' : Û a (prog f) c
        C' = index (pred βindex z')

        eq₁ : sup x l ≐ h a (prog f) c (pred βindex z')
        eq₁ = ≐trans (sup x l)
                     (pred β (fst w∈β))
                     (h a (prog f) c (pred βindex z'))
                     (snd w∈β)
                     (snd (ip-compat (fst (h-iso {a} {prog f} {c} {βindex} {sup (index βindex) (pred βindex)})
                                            (≐'eta {a} {prog f} {c} βindex)) (fst w∈β)))
        
        eq₂ : h a (prog f) c (pred βindex z') ≐
                sup (T̂ a (prog f) c (index (pred βindex z'))) λ y → h a (prog f) c (pred (pred βindex z') y)
        eq₂ = fst (h-iso {a} {prog f} {c} {pred βindex z'} {sup (index (pred βindex z')) (pred (pred βindex z'))})
                    (≐'eta {a} {prog f} {c} (pred βindex z'))

        lem₁ : (z : T̂ a (prog f) c C') →
                 h a (prog f) c (pred (pred βindex z') z) ∈ (sup x l)
        lem₁ z = snd (ExtAx2 (≐trans (sup x l)
                                     (h a (prog f) c (pred βindex z') )
                                     (sup (T̂ a (prog f) c (index (pred βindex z'))) λ y → h a (prog f) c (pred (pred βindex z') y))
                                     eq₁
                                     eq₂)
                             (h a (prog f) c (pred (pred βindex z') z)))
                       (z , ≐refl (h a (prog f) c (pred (pred βindex z') z)))

        lem₂ : Σ (T̂ a (prog f) c C' → V̂ (pred (tc a) u) (f u) (b' , g')) λ g →
                 (z : T̂ a (prog f) c C') → h a (prog f) c (pred (pred βindex z') z) ≐ h (pred (tc a) u) (f u) (b' , g') (g z)
        lem₂ = AC λ z → ExtAx1 (≐sym (h a (prog f) c (pred (pred βindex z') z))
                                     (l (fst (lem₁ z)))
                                     (snd (lem₁ z)))
                               (β⊆𝕍̂ (l (fst (lem₁ z)))
                                    (β-transitive (sup x l) (l (fst (lem₁ z))) w∈β (fst (lem₁ z) , ≐refl (l (fst (lem₁ z))))))

        C : Û (pred (tc a) u) (f u) (b' , g')
        C = fst (codeForFamSets (pred (tc a) u) (f u) (b' , g') z')

        p' : T̂ (pred (tc a) u) (f u) (b' , g') C ≡ T̂ a (prog f) c C'
        p' = snd (codeForFamSets (pred (tc a) u) (f u) (b' , g') z')

        lem₃ : h (pred (tc a) u) (f u) (b' , g') (sup C (λ y → fst lem₂ (transp (λ A → A) p' y))) ∈ 𝕍̂
        lem₃ = sup C (λ y → fst lem₂ (transp (λ A → A) p' y)) ,
               ≐refl (h (pred (tc a) u) (f u) (b' , g') (sup C (λ y → fst lem₂ (transp (λ A → A) p' y))))

    in ExtAx1 (≐trans (h (pred (tc a) u) (f u) (b' , g') (sup C (λ y → fst lem₂ (transp (λ A → A) p' y))))
                      (sup (T̂ a (prog f) c C') λ y → h a (prog f) c (pred (pred βindex z') y))
                      (sup x l)
                      (≐trans (h (pred (tc a) u) (f u) (b' , g') (sup C (λ y → fst lem₂ (transp (λ A → A) p' y))))
                              (sup (T̂ (pred (tc a) u) (f u) (b' , g') C) λ y → h a (prog f) c (pred (pred βindex z') (transp (λ A → A) p' y)))
                              (sup (T̂ a (prog f) c C') λ y → h a (prog f) c (pred (pred βindex z') y))
                              (≐cong λ y → ≐sym (h a (prog f) c (pred (pred βindex z') (transp (λ A → A) p' y)))
                                                 (h (pred (tc a) u) (f u) (b' , g') (fst lem₂ (transp (λ A → A) p' y)))
                                                 (snd lem₂ (transp (λ A → A) p' y)))
                              (≡-≐ (λ z → h a (prog f) c (pred (pred βindex z') z)) p'))
                      (≐sym (sup x l)
                            (sup (T̂ a (prog f) c C') λ y → h a (prog f) c (pred (pred βindex z') y))
                            (≐trans (sup x l)
                                    (h a (prog f) c (pred βindex z'))
                                    (sup (T̂ a (prog f) c C') λ y → h a (prog f) c (pred (pred βindex z') y))
                                    eq₁ eq₂)))
              lem₃

  v∈𝕍̂ : v ∈ 𝕍̂ 
  v∈𝕍̂ = β⊆𝕍̂ v (fst (fst (snd (V-REA {a} {prog f} {c} (fst (sgltV v v∈V)))) tt) ,
              ≐trans v (h a (prog f) c (fst v∈V)) (pred β (fst (fst (snd (V-REA {a} {prog f} {c} (fst (sgltV v v∈V)))) tt)))
                     (snd v∈V) (snd (fst (snd (V-REA {a} {prog f} {c} (fst (sgltV v v∈V)))) tt)))

  code𝕌̂ : Û a (prog f) c
  code𝕌̂ = code₂ (index βindex , λ z → index (pred βindex z)) (injl (injr u))

  decode𝕌̂ : T̂ a (prog f) c code𝕌̂  → Û a (prog f) c
  decode𝕌̂ z = code₂ (index βindex , λ z → index (pred βindex z)) (injr (u , z))

  β'pred : T̂ a (prog f) c (codeW code𝕌̂ decode𝕌̂) → V̂ a (prog f) c
  β'pred (sup x l) = sup (decode𝕌̂ x) λ z → β'pred (l z)
  
  β' : 𝕍
  β' = h a (prog f) c (sup (codeW code𝕌̂ decode𝕌̂) β'pred)

  h-lem : (w : T̂ a (prog f) c (codeW code𝕌̂ decode𝕌̂)) →
            h a (prog f) c (β'pred w) ≐ h (pred (tc a) u) (f u) (b' , g') w
  h-lem (sup x l) = ≐cong λ z → h-lem (l z)

  β'≐𝕍̂ : β' ≐ 𝕍̂
  β'≐𝕍̂ = ExtAx2' λ x → (λ d → fst d , ≐trans x (h a (prog f) c (β'pred (fst d))) (h (pred (tc a) u) (f u) (b' , g') (fst d))
                                             (snd d) (h-lem (fst d))) ,
                       λ e → fst e , ≐trans x (h (pred (tc a) u) (f u) (b' , g') (fst e)) (h a (prog f) c (β'pred (fst e)))
                                            (snd e)
                                            (≐sym (h a (prog f) c (β'pred (fst e)))
                                                  (h (pred (tc a) u) (f u) (b' , g') (fst e))
                                                  (h-lem (fst e)))


V-αInacc : [ Û a t c , T̂ a t c , V a t c ]-is a Inacc
V-αInacc {sup A f} {prog f'} {c} =
  let indexSet : index (sup A f) → V̂ (sup A f) (prog f') c → Set
      indexSet x w = T̂ (sup A f) (prog f') c (fst (mainLemma (w , ≐refl (pred (V (sup A f) (prog f') c) w)) (injl x)))

      famSets : (x : index (sup A f)) → (w : V̂ (sup A f) (prog f') c) → indexSet x w → Set
      famSets x w z = T̂ (sup A f) (prog f') c (fst (snd (mainLemma (w , ≐refl (pred (V (sup A f) (prog f') c) w)) (injl x))) z)

      lem : (x : index (sup A f)) → (w : V̂ (sup A f) (prog f') c) →
               h (sup A f) (prog f') c w ∈ V (pred (tc (sup A f)) (injl x)) (f' (injl x)) (indexSet x w , famSets x w) ×
               V (pred (tc (sup A f)) (injl x)) (f' (injl x)) (indexSet x w , famSets x w) ∈ V (sup A f) (prog f') c
      lem x w = snd (snd (mainLemma (w , ≐refl (pred (V (sup A f) (prog f') c) w)) (injl x)))
  in snd (inaccHierarchy (Û (sup A f) (prog f') c)
                    (T̂ (sup A f) (prog f') c)
                    (V (sup A f) (prog f') c)
                    (sup A f)
                    V-Inacc)
           λ x w → Û (pred (tc (sup A f)) (injl x)) (f' (injl x)) (indexSet x w , famSets x w) ,
                   T̂ (pred (tc (sup A f)) (injl x)) (f' (injl x)) (indexSet x w , famSets x w) ,
                   V (pred (tc (sup A f)) (injl x)) (f' (injl x)) (indexSet x w , famSets x w) ,
                   (V-αInacc {pred (tc (sup A f)) (injl x)} {f' (injl x)} {indexSet x w , famSets x w} ,
                     fst (lem x w)) ,
                   snd (lem x w)


Û[_,_,_] : (a : 𝕍) (t : Acc a) → 𝕍 → Set
Û[ a , t , b ] = fst (ϕ a t (index b , λ x → index (pred b x)))

T̂[_,_,_] : (a : 𝕍) (t : Acc a) (b : 𝕍) → Û[ a , t , b ] → Set
T̂[ a , t , b ] = snd (ϕ a t (index b , λ x → index (pred b x)))

V̂[_,_,_] : (a : 𝕍) (t : Acc a) → 𝕍 → Set
V̂[ a , t , b ] = W Û[ a , t , b ] T̂[ a , t , b ]

h[_,_,_] : (a : 𝕍) (t : Acc a) (b : 𝕍) → V̂[ a , t , b ] → 𝕍
h[ a , t , b ] (sup x f) = sup (T̂[ a , t , b ] x) λ y → h[ a , t , b ] (f y)

h-cong : (a : 𝕍) (t : Acc a) (b : 𝕍) →
           (x : V̂[ a , t , b ]) → h a t (index b , λ x → index (pred b x)) x ≐ h[ a , t , b ] x
h-cong a t b (sup z f) = ≐cong λ y → h-cong a t b (f y)

V[_,_,_] : (a : 𝕍) (t : Acc a) → 𝕍 → 𝕍
V[ a , t , b ] = sup V̂[ a , t , b ] h[ a , t , b ]

V-cong : (a : 𝕍) (t : Acc a) (b : 𝕍) → V a t (index b , λ x → index (pred b x)) ≐ V[ a , t , b ]
V-cong a t b = ≐cong (h-cong a t b)

V-αInacc' : (a : 𝕍) (t : Acc a) (b : 𝕍) →
              [ Û[ a , t , b ] , T̂[ a , t , b ] , V[ a , t , b ] ]-is a Inacc
V-αInacc' a t b = αInacc-inv Û[ a , t , b ]
                             T̂[ a , t , b ]
                             a
                             (V-cong a t b)
                             (V-αInacc {a} {t} {index b , λ x → index (pred b x)}) 


V-base : {b : 𝕍} → isTransitive b → (a : 𝕍) (t : Acc a) →
           (v : 𝕍) → v ∈ b → v ∈ V[ a , t , b ]
V-base {b} b-trans a t =
  ∈-tcTI {F = λ v → v ∈ b → v ∈ V[ a , t , b ]}
         (λ v IH v∈b →
           sup (fst (lem₂ v∈b)) (λ x → (fst (lem₁ v∈b IH) (transp (λ A → A) (snd (lem₂ v∈b)) x))) ,
           ≐trans v
                   (sup (index (ξ v∈b)) λ y → h[ a , t , b ] (fst (lem₁ v∈b IH) y))
                   (sup (T̂[ a , t , b ] (fst (lem₂ v∈b)))
                        (λ x → h[ a , t , b ] (fst (lem₁ v∈b IH) (transp (λ A → A) (snd (lem₂ v∈b)) x))))
                   (≐trans v
                           (sup (index (ξ v∈b)) (pred (ξ v∈b)))
                           (sup (index (ξ v∈b)) (λ y → h[ a , t , b ] (fst (lem₁ v∈b IH) y)))
                           (≐trans v (ξ v∈b) (sup (index (ξ v∈b)) (pred (ξ v∈b))) (snd v∈b) (≐eta (ξ v∈b)))
                           (≐cong (snd (lem₁ v∈b IH))))
                   (lem₃ v∈b IH))
  where
  ξ : {v : 𝕍} → v ∈ b → 𝕍
  ξ v∈b = pred b (fst v∈b)

  ξ⊆v : {v : 𝕍} → (d : v ∈ b) → (x : index (ξ d)) → pred (ξ d) x ∈ v
  ξ⊆v d x = snd (ExtAx2 (snd d) (pred (ξ d) x)) (x , ≐refl (pred (ξ d) x))

  lem₁ : {v : 𝕍} → (d : v ∈ b) → ∀𝕧∈ (tc v) (λ w → w ∈ b → w ∈ V[ a , t , b ]) →
           Σ (index (ξ d) → V̂[ a , t , b ]) λ g →
             (x : index (ξ d)) → pred (ξ d) x ≐ h[ a , t , b ] (g x)
  lem₁ {sup A f} d IH = AC {C = λ x w → pred (ξ d) x ≐ h[ a , t , b ] w}
                             λ x → ExtAx1 {f (fst (ξ⊆v d x))} {pred (ξ d) x} {V[ a , t , b ]}
                                          (≐sym (pred (ξ d) x) (f (fst (ξ⊆v d x))) (snd (ξ⊆v d x)))
                                          (IH (injl (fst (ξ⊆v d x)))
                                          (b-trans (sup A f) (f (fst (ξ⊆v d x))) d (fst (ξ⊆v d x) , ≐refl (f (fst (ξ⊆v d x))))))

  lem₂ : {v : 𝕍} → (d : v ∈ b) →
           Σ (Û a t (index b , (λ x → index (pred b x))))
             (λ y →
               T̂ a t (index b , (λ z → index (pred b z))) y ≡ index (ξ d))
  lem₂ d = codeForFamSets a t (index b , λ x → index (pred b x)) (fst d)

  lem₃ : {v : 𝕍} → (d : v ∈ b) → (IH : ∀𝕧∈ (tc v) (λ w → w ∈ b → w ∈ V[ a , t , b ])) →
           sup (index (ξ d)) (λ y → h[ a , t , b ] (fst (lem₁ d IH) y)) ≐
           sup (T̂[ a , t , b ] (fst (lem₂ d))) (λ x → h[ a , t , b ] (fst (lem₁ d IH) (transp (λ A → A) (snd (lem₂ d)) x)))
  lem₃ {sup A f} d IH = ≐sym (sup (T̂[ a , t , b ] (fst (lem₂ d)))
                                  (λ x → h[ a , t , b ] (fst (lem₁ d IH) (transp (λ A → A) (snd (lem₂ d)) x))))
                             (sup (index (ξ d)) λ y → h[ a , t , b ] (fst (lem₁ d IH) y))
                             (≡-≐ (λ z → h[ a , t , b ] (fst (lem₁ d IH) z)) (snd (lem₂ d)))

  
PiNumbersAx : (x a : 𝕍) → Σ Set λ U → Σ (U → Set) λ T → Σ 𝕍 λ b →
                x ∈ b × [ U , T , b ]-is a Inacc
PiNumbersAx x a = Û[ a , 𝕍⊆Acc a , tc x' ] , T̂[ a , 𝕍⊆Acc a , tc x' ] , V[ a , 𝕍⊆Acc a , tc x' ] ,
                    V-base (tc-is-trans x') a (𝕍⊆Acc a) x (injl tt , ≐refl x) ,
                    V-αInacc' a (𝕍⊆Acc a) (tc x')
  where
  x' : 𝕍
  x' = sup ⊤ λ _ → x
