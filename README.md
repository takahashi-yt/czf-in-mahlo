# CZF-in-Mahlo

This repository contains the Agda code for [the following paper](https://doi.org/10.48550/arXiv.2402.15074):

Yuta Takahashi. Interpretation of Inaccessible Sets in Martin-Löf Type Theory with One Mahlo Universe. Preprint. CoRR abs/2402.15074 (2024)

Specifically, we formalise the main part of this paper's result that Aczel's constructive set theory (CZF) with inaccessible sets of all transfinite orders is interpretable in Martin-Löf type theory (MLTT) with one Mahlo universe and the accessibility predicate. We simulate Setzer's Mahlo universe with the external Mahlo universe, following the work by Dybjer and Setzer on induction-recursion.

## Outline

`Preliminaries.agda`:
Several notions (e.g., W-types) of the core type theory are defined.

`CZFBasics.agda`:
Basic facts for Aczel's interpretation of CZF in MLTT are provided. For instance, the type of iterative sets is defined.

`CZFAxioms.agda`:
All axioms of CZF are validated in MLTT.

`ExternalMahlo.agda`:
The external Mahlo universe is defined by induction-recursion, and a higher-order universe operator is defined by the reflection property of the external Mahlo universe.

`TypeHierarchy.agda`:
The accessibility predicate Acc is defined, and the hierarchy of types of iterative sets is constructed by iterating the higher-order universe operator along the accessibility.

`IterativeSetHierarchy.agda`:
Each type of iterative sets in the hierarchy above is transformed into an iterative set V a t c. Moreover, it is verified that V a t c validates all axiom of CZF.

`RegularExtensionAxiom.agda`:
Each V a t c is shown to be a regular set. In addition, Regular Extension Axiom is postulated.

`Inaccessibles/Basics.agda, FamSetsSublemma.agda, UnboundednessSublemma.agda, HierarchyLemma.agda`:
A lemma on the hierarchy of inaccessible sets of transfinite orders is proved. For reasons of type-checking performance, we divide the proof into four Agda files.

`PiNumbersAxiom.agda`:
It is shown that inaccessible sets of all transfinite orders are interpretable in MLTT with one Mahlo universe and the accessibility predicate.