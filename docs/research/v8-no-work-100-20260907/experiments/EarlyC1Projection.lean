import NearGammaFibreBridge
import EarlyC1Support
import EarlyC1Arithmetic

/-!
An early mathematical C1 object from the fixed, totalized received C1 word.
The generic uniqueness theorem is proved in EarlyC1Support; the final
concrete identification application remains in the explicitly unverified
draft, not in this retained leaf.
This is deliberately an Option: no candidate is not silently replaced by zero.
The later width29 tuple is used to prove that the Option is populated, never
to define it. No semantic challenge, C2 word, gamma or provider is an input.

The object is noncomputable. It establishes causal mathematical uniqueness,
not adversary access, decoder runtime, proof acceptance or payment validity.
-/
set_option autoImplicit false

namespace AspisV8.EarlyC1Projection
open Finset
noncomputable section
local instance projectionDecision (p : Prop) : Decidable p := Classical.propDecidable p
-- In particular, do not synthesize executable equality on a finite QM31
-- function space while elaborating the symbolic support sets below.



open AspisV8.NearGammaFibreBridge
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact

abbrev Message := InitialMessage QM31Exact
abbrev C1Messages := Fin 26 → Message
abbrev C1Received := Fin 26 → Fin 1048576 → QM31Exact

noncomputable def fibreEncode (message : Message) : Fin 262144 → (Fin 4 → QM31Exact) :=
  fun f s => exactInitialEncoder message (fibreEmbed (f,s))

noncomputable def receivedFibres (received : C1Received) :
    Fin 26 → Fin 262144 → (Fin 4 → QM31Exact) :=
  fun lane f s => received lane (fibreEmbed (f,s))

theorem exact_fibre_overlap (left right : Message) (different : left ≠ right) :
    (univ.filter fun f => fibreEncode left f = fibreEncode right f).card ≤ 256 := by
  calc
    _ = (fullFibreAgreement left right).card := by
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro f _
      exact funext_iff
    _ ≤ 256 := full_fibre_overlap_le_256 left right different

#print axioms exact_fibre_overlap
noncomputable def earlyC1 (received : C1Received) : Option C1Messages :=
  early fibreEncode (receivedFibres received) 245609

/-- Concrete totalized V7 C1 symbols are embedded M31 values. This does
not assert that the word was recovered from a root or accepting proof. -/
theorem extracted_totalized_C1_base
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords) :
    ∀ column index, projectBase (c1Received words column index) =
      c1Received words column index := projectBase_c1Received words
#print axioms extracted_totalized_C1_base

end
end AspisV8.EarlyC1Projection
