import D18S4ConcreteWidth29KernelV1
import S4V10CandidateQueryFieldEvidenceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4FourSlotCurrentArraySemanticsV1

open AspisR1D18S4ConcreteWidth29KernelV1
open AspisR1FastDotsLiteralCallbackValueRootV1
open AspisR1FastDotsForwardLiteralValueRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1.ExactBaseProjection
open AspisR1.MixedLeafEncoding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV8R15.ExactTowerBase

abbrev Wide := AspisR1FastDotsLiteralHeadSumRootV1.Wide
abbrev TowerWide := AspisR1FastDotsTailFieldProductRootV1.TowerWide
abbrev C1 := AspisR1.MixedLeafEncoding.C1
abbrev C2 := AspisR1.MixedLeafEncoding.C2

private def decodedCurrent (x : Wide) : TowerWide :=
  AspisR1CurrentWide.Proof.decodeWide
    (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)

/-- The four values in one successful returned Current array are the four
first-fold fibres of the same decoded opening and the same 29 powers.  The
four callback witnesses remain tied to the same byte array and coefficient
array throughout. -/
theorem four_slot_values_are_first_fold_fibres
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (currentValues : Array Wide 4#usize) (v0 v1 v2 v3 : Wide)
    (hvalues : currentValues.val = [v0,v1,v2,v3])
    (gamma : TowerWide) (c1 : C1) (c2 : C2)
    (hbytes : a.val.map AspisR1.ExtractedRecordByteValue.rawByte =
      encodeC1 c1 ++ encodeC2 c2)
    (hpowers : ∀ j : Fin 29,
      AspisR1FastDotsTailFieldProductRootV1.wideDecoded
        (g.val[j.val]'(by scalar_tac)) = gamma ^ j.val)
    (hf0 : LiteralFieldResult (literalOps concreteOps) a g 0#usize v0)
    (hf1 : LiteralFieldResult (literalOps concreteOps) a g 1#usize v1)
    (hf2 : LiteralFieldResult (literalOps concreteOps) a g 2#usize v2)
    (hf3 : LiteralFieldResult (literalOps concreteOps) a g 3#usize v3) :
    List.map decodedCurrent currentValues.val =
      List.ofFn (fun slot : Fin 4 =>
        AspisV6Width29CorrelatedAgreement.width29Batch
          (AspisR1D18S4ConcreteWidth29KernelV1.localWord c1 c2 slot) gamma) := by
  have h0 := literal_field_result_concrete_width29 a g 0#usize
    ⟨0, by decide⟩ v0 gamma c1 c2 rfl hbytes hpowers hf0
  have h1 := literal_field_result_concrete_width29 a g 1#usize
    ⟨1, by decide⟩ v1 gamma c1 c2 rfl hbytes hpowers hf1
  have h2 := literal_field_result_concrete_width29 a g 2#usize
    ⟨2, by decide⟩ v2 gamma c1 c2 rfl hbytes hpowers hf2
  have h3 := literal_field_result_concrete_width29 a g 3#usize
    ⟨3, by decide⟩ v3 gamma c1 c2 rfl hbytes hpowers hf3
  rw [hvalues]
  simp [decodedCurrent, h0, h1, h2, h3, List.ofFn,
    Fin.foldr_succ, Fin.foldr_zero]

#print axioms four_slot_values_are_first_fold_fibres

end AspisR1S4FourSlotCurrentArraySemanticsV1
