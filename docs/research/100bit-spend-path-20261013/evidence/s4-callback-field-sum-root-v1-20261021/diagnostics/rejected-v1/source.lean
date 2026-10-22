import S4AllFourCallbackHeadTailDecodeV1
import S4HeadBatchFieldRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsCallbackFieldSumRootV1
open AspisR1FastDotsAllFourCallbackHeadTailDecodeV1
abbrev TowerWide := AspisR1FastDotsTailFieldProductRootV1.TowerWide

theorem batch_residue_definitions_agree (ds : List (List Contribution)) :
    AspisR1FastDotsAllFourHeadResidueJoinV1.decodedBatchResidues ds =
      AspisR1FastDotsHeadBatchFieldRootV1.headBatchResidues ds := by
  rfl

/-- The head residues retained by the same callback are literal source
products, with coefficient/limb correspondence derived from its ExactTrace. -/
theorem exact_head_residues_are_source_products
    {ops : Ops} {a : Array Std.U8 608#usize} {g : Array Wide 29#usize} {slot : Usize}
    {it : AspisR1FastDotsOuterFoldTraceV2.StepBy}
    {limbs out : Array Std.U64 8#usize} {ds : List (List Contribution)} {starts : List Nat}
    (h : ExactTrace ops a g slot it limbs out ds starts) :
    AspisR1FastDotsAllFourHeadResidueJoinV1.decodedBatchResidues ds =
      (ds.flatten.map AspisR1FastDotsHeadFieldAlgebraRootV1.sourceProduct).sum := by
  rw [batch_residue_definitions_agree]
  exact AspisR1FastDotsHeadBatchFieldRootV1.exact_trace_head_field_sum h

/-- Retains the entire decoded callback witness while exposing an equality
for its actual returned value in terms of both literal source product sums. -/
theorem callback_actual_value_field_sum
    {base ops : Ops} {a : Array Std.U8 608#usize} {g : Array Wide 29#usize}
    {slot : Usize} {value : Wide} (h : CallbackDecodedTrace base ops a g slot value) :
    CallbackDecodedTrace base ops a g slot value ∧
    ∃ ds : List (List Contribution), ∃ starts : List Nat,
    ∃ limbs : Array Std.U64 8#usize,
    ∃ wide28 : Wide, ∃ q : AspisR1EbyKPushDotBackend.PushQm,
    ∃ cs : List AspisR1FastDotsActualTailBodyTraceRootV1.Contribution,
      ExactTrace (AspisR1FastDotsConcreteTailInstallRootV1.install base) a g slot
        AspisR1FastDotsStepSchedule.startBy (Array.repeat 8#usize 0#u64) limbs ds starts ∧
      ds.length = 7 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) =
      (ds.flatten.map AspisR1FastDotsHeadFieldAlgebraRootV1.sourceProduct).sum +
        (((wide28,q)::cs.map (fun c => (c.coefficient,c.scalar))).map
          (fun p => AspisR1FastDotsTailFieldProductRootV1.wideDecoded p.1 *
            AspisR1FastDotsTailLiteralProductsRootV1.embedQM p.2)).sum := by
  refine ⟨h, ?_⟩
  rcases h with ⟨ds,starts,limbs,body,tailValue,wide28,q,tailStart,tail2,cs,
    hc,ht,hlen,hfirst,hwide,hrun,hfinish,haccepted,hproduct,hwords,hdecode⟩
  refine ⟨ds,starts,limbs,wide28,q,cs,ht,hlen,?_⟩
  rw [exact_head_residues_are_source_products ht] at hdecode
  exact hdecode

#print axioms batch_residue_definitions_agree
#print axioms exact_head_residues_are_source_products
#print axioms callback_actual_value_field_sum
end AspisR1FastDotsCallbackFieldSumRootV1
