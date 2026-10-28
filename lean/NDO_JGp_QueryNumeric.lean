import NDO_JGg_QueryDecode
import RPt_JFq_Queries
set_option autoImplicit false
namespace AspisR1.JGp_QueryNumeric
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge
open Query31ExplicitListLoop Query31ExplicitScanBody
attribute [local irreducible] encodeState

theorem words_injective (xs ys : List U32)
    (same : xs.map (fun x=>x.val)=ys.map (fun x=>x.val)) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => cases same
    | cons y ys =>
      have h : x.val=y.val ∧ xs.map (fun x=>x.val)=ys.map (fun x=>x.val) := List.cons.inj same
      exact congrArg₂ List.cons (UScalar.eq_of_val_eq h.1) (ih ys h.2)
#print axioms words_injective

theorem identified (q : Array U32 22#usize)
    (run : Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState JGg_QueryDecode.blocks JGg_QueryDecode.advances=
      ok (.Ok (q,encodeState JGg_Opening31.next2))) : q=JFq_Queries.value := by
  obtain ⟨s1,call1,valid1,state1⟩ := JGg_QueryScan0.source
  obtain ⟨s2,call2,valid2,state2⟩ := JGg_QueryScan1.source s1 valid1 state1
  obtain ⟨s3,call3,valid3,state3⟩ := JGg_QueryScan2.source s2 valid2 state2
  have count : s3.accepted_len=22#usize := by
    apply UScalar.eq_of_val_eq
    have hp := congrArg (fun s : AspisV8R19.Q22WordScan.ScanState => s.accepted.length) state3
    have len := valid3.2.2
    change (acceptedPrefix s3).length=22 at hp
    change s3.accepted_len.val=22
    omega
  have numeric : s3.accepted=JFq_Queries.value := by
    have hp := congrArg (fun s : AspisV8R19.Q22WordScan.ScanState => s.accepted) state3
    change acceptedPrefix s3=_ at hp
    unfold acceptedPrefix at hp
    rw [count] at hp
    have take : s3.accepted.val.take 22=s3.accepted.val := by
      apply List.take_of_length_le
      exact le_of_eq s3.accepted.property
    erw [take] at hp
    apply Subtype.ext
    apply words_injective
    exact hp
  have finish : AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s3=ok (.Ok s3.accepted) := by
    simp only [AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish,count,
      AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT,if_pos rfl]
    rfl
  have at0 : Array.index_usize JGg_QueryDecode.blocks 0#usize=ok (encodeState JGg_Opening31.block0) := rfl
  have at1 : Array.index_usize JGg_QueryDecode.blocks 1#usize=ok (encodeState JGg_Opening31.block1) := rfl
  have at2 : Array.index_usize JGg_QueryDecode.blocks 2#usize=ok (encodeState JGg_Opening31.block2) := rfl
  have selected : Array.index_usize JGg_QueryDecode.advances 2#usize=ok (encodeState JGg_Opening31.next2) := rfl
  unfold Query31ConcreteMaterializedSchedule.actualConcreteDecode at run
  have driver := Query31ConcreteMaterializedSchedule.adaptScanResult_success run
  unfold AspisR1Query31Transcript.queries_from_pairs_with_scan at driver
  rw [at0,bind_tc_ok] at driver
  try simp only [Aeneas.Std.uncurry] at driver
  rw [call1,bind_tc_ok] at driver
  try simp only [Aeneas.Std.uncurry] at driver
  rw [if_neg Bool.false_ne_true,at1,bind_tc_ok] at driver
  try simp only [Aeneas.Std.uncurry] at driver
  rw [call2,bind_tc_ok] at driver
  try simp only [Aeneas.Std.uncurry] at driver
  rw [if_neg Bool.false_ne_true,at2,bind_tc_ok] at driver
  try simp only [Aeneas.Std.uncurry] at driver
  rw [call3,bind_tc_ok] at driver
  try simp only [Aeneas.Std.uncurry] at driver
  rw [finish,bind_tc_ok] at driver
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at driver
  rw [selected,bind_tc_ok] at driver
  simp only [ite_true] at driver
  have same : s3.accepted=q := congrArg Prod.fst (core.result.Result.Ok.inj (Result.ok.inj driver))
  exact same.symm.trans numeric
#print axioms identified

theorem source : Query31ConcreteMaterializedSchedule.actualConcreteDecode
    Query31ConcreteDriverTraceFacts.sourceDefaultState JGg_QueryDecode.blocks JGg_QueryDecode.advances=
    ok (.Ok (JFq_Queries.value,encodeState JGg_Opening31.next2)) := by
  obtain ⟨q,run⟩ := JGg_QueryDecode.source
  exact identified q run ▸ run
#print axioms source
end AspisR1.JGp_QueryNumeric
