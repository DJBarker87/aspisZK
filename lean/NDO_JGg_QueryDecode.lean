import NDO_JGg_QueryScan0
import NDO_JGg_QueryScan1
import NDO_JGg_QueryScan2
set_option autoImplicit false
namespace AspisR1.JGg_QueryDecode
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge

def blocks : Array (Array U8 32#usize) 8#usize := Array.make 8#usize
  [encodeState JGg_Opening31.block0,encodeState JGg_Opening31.block1,encodeState JGg_Opening31.block2,
   encodeState JGg_Opening31.block3,encodeState JGg_Opening31.block4,encodeState JGg_Opening31.block5,
   encodeState JGg_Opening31.block6,encodeState JGg_Opening31.block7]
def advances : Array (Array U8 32#usize) 8#usize := Array.make 8#usize
  [encodeState JGg_Opening31.next0,encodeState JGg_Opening31.next1,encodeState JGg_Opening31.next2,
   encodeState JGg_Opening31.next3,encodeState JGg_Opening31.next4,encodeState JGg_Opening31.next5,
   encodeState JGg_Opening31.next6,encodeState JGg_Opening31.next7]

theorem pair_let {A B C : Type} (a : A) (b : B) (f : A → B → C) :
    (let (x,y):=(a,b);f x y)=f a b := rfl
#print axioms pair_let

theorem source : ∃ q, Query31ConcreteMaterializedSchedule.actualConcreteDecode
    Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances=
      ok (.Ok (q,encodeState JGg_Opening31.next2)) := by
  obtain ⟨s1,call1,valid1,state1⟩ := JGg_QueryScan0.source
  obtain ⟨s2,call2,valid2,state2⟩ := JGg_QueryScan1.source s1 valid1 state1
  obtain ⟨s3,call3,valid3,state3⟩ := JGg_QueryScan2.source s2 valid2 state2
  have count : s3.accepted_len=22#usize := by
    apply UScalar.eq_of_val_eq
    have hp := congrArg (fun s : AspisV8R19.Q22WordScan.ScanState => s.accepted.length) state3
    have len := valid3.2.2
    change (Query31ExplicitScanBody.acceptedPrefix s3).length=22 at hp
    change s3.accepted_len.val=22
    omega
  have finish : AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s3=ok (.Ok s3.accepted) := by
    simp only [AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish,count,
      AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT,if_pos rfl]
    rfl
  have at0 : Array.index_usize blocks 0#usize=ok (encodeState JGg_Opening31.block0) := rfl
  have at1 : Array.index_usize blocks 1#usize=ok (encodeState JGg_Opening31.block1) := rfl
  have at2 : Array.index_usize blocks 2#usize=ok (encodeState JGg_Opening31.block2) := rfl
  have selected : Array.index_usize advances 2#usize=ok (encodeState JGg_Opening31.next2) := rfl
  refine ⟨s3.accepted,?_⟩
  unfold Query31ConcreteMaterializedSchedule.actualConcreteDecode
  have driver : AspisR1Query31Transcript.queries_from_pairs_with_scan
      (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
      Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances=
      ok (.Ok (s3.accepted,encodeState JGg_Opening31.next2)) := by
    unfold AspisR1Query31Transcript.queries_from_pairs_with_scan
    rw [at0,bind_tc_ok]
    try simp (config := {zeta := true,zetaDelta := true}) only [Aeneas.Std.uncurry]
    rw [call1,bind_tc_ok]
    try simp (config := {zeta := true,zetaDelta := true}) only [Aeneas.Std.uncurry]
    rw [if_neg Bool.false_ne_true,at1,bind_tc_ok]
    try simp (config := {zeta := true,zetaDelta := true}) only [Aeneas.Std.uncurry]
    rw [call2,bind_tc_ok]
    try simp (config := {zeta := true,zetaDelta := true}) only [Aeneas.Std.uncurry]
    rw [if_neg Bool.false_ne_true,at2,bind_tc_ok]
    try simp (config := {zeta := true,zetaDelta := true}) only [Aeneas.Std.uncurry]
    rw [call3,bind_tc_ok]
    try simp (config := {zeta := true,zetaDelta := true}) only [Aeneas.Std.uncurry]
    rw [finish,bind_tc_ok]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    rw [selected,bind_tc_ok]
    simp only [ite_true]
  rw [driver]
  rfl
#print axioms source
end AspisR1.JGg_QueryDecode
