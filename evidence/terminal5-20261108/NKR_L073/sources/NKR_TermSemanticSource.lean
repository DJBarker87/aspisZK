import NKR_ScheduleRoot
import NKI_ValueAssociation
import NJL_PathParent
import NJL_OccupancyParent
import NKR_DigestOldSource
import NKR_TermScalar
import RPv_JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermSemanticSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public Openings Selectors)
open pool_v1.pair_forest_semantic_terminal
abbrev Packed := Array NQ 24#usize
def zero : Packed := Array.repeat 24#usize field.QM31.ZERO
structure Packet (pub : Public) (o : Openings) (s : Selectors) where
 schedule : Packed
 path : Packed
 value : Packed
 occupancy : Packed
 digests : Array NQ 8#usize
 packedDigests : Packed
 out : Packed
 schedule_call : add_schedule_lanes zero pub o s=ok schedule
 path_call : add_path_lanes schedule o s=ok path
 value_call : add_value_lanes path o s=ok value
 occupancy_call : add_occupancy_lanes value pub o s=ok occupancy
 digest_call : public_digest_lanes pub o s=ok digests
 packed_digest_call : add_preweighted occupancy 84#usize digests=ok packedDigests
 scalar_call : FIw_ScalarSuffix.run pub o s packedDigests=ok out
 canonical_schedule : canonical schedule
 canonical_path : canonical path
 canonical_value : canonical value
 canonical_occupancy : canonical occupancy
 canonical_digests : canonical digests
 canonical_packedDigests : canonical packedDigests
 canonical_out : canonical out
/-- Complete generic261 EMITTED-source composition, every child at identical
actual arguments. This is SOURCE SUPPORT: optimized250's packed-vs-eight-lane
association and261 native windows remain mandatory before row credit.
NKI260/233 and NKR232 candidates remain conditional on next-ledger adoption. -/
theorem source (pub : Public) (o : Openings) (s : Selectors)
 (hd : NKR_DigestChildren.Domain pub)
 (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
 (hh : canonical s.high) (hl : canonical s.low)
 (asset : pub.asset_id.val<2147483647)
 (amount : (core.option.Option.unwrap_or pub.withdrawal_amount 0#u32).val<2147483647) :
 ∃ p : Packet pub o s,semantic_packed pub o s=ok p.out := by
 have hzero : canonical zero := JFy_ZeroArrays.source 24#usize
 obtain ⟨l,absorption,middle,schedule,_,_,_,_,_,sc,cs,_⟩ := NKR_ScheduleRoot.source zero pub o s hzero hz hh hl
 obtain ⟨path,pc,_⟩ := NJL_PathParent.source schedule o s cs hh hl hz hs
 obtain ⟨t,vmiddle,value,_,_,_,_,_,_,cv,_,vc⟩ := NKI_ValueAssociation.source path.after o s path.canonical hz hs hx hh hl
 obtain ⟨occupancy,oc,_⟩ := NJL_OccupancyParent.source value pub o s cv hh hl hz
 obtain ⟨digests,dc,cd,_⟩ := NKR_DigestOldSource.source pub o s hd hz hh hl
 obtain ⟨packedDigests,pdc,cpd,_⟩ := NHU_Preweighted.result occupancy.after 84#usize digests (by decide) (by decide) occupancy.canonical cd
 obtain ⟨out,call,co⟩ := NKR_TermScalar.source pub o s packedDigests hz hh hl cpd asset amount
 let p : Packet pub o s := ⟨schedule,path.after,value,occupancy.after,digests,packedDigests,out,sc,pc,vc,oc,dc,pdc,call,cs,path.canonical,cv,occupancy.canonical,cd,cpd,co⟩
 refine ⟨p,?_⟩
 unfold semantic_packed
 change (do
  let a←add_schedule_lanes zero pub o s
  let b←add_path_lanes a o s
  let c←add_value_lanes b o s
  let d←add_occupancy_lanes c pub o s
  let e←public_digest_lanes pub o s
  let f←add_preweighted d 84#usize e
  FIw_ScalarSuffix.run pub o s f)=ok out
 rw [sc,bind_tc_ok,pc,bind_tc_ok,vc,bind_tc_ok,oc,bind_tc_ok,dc,bind_tc_ok,pdc,bind_tc_ok,call]
#print source
#print axioms source
end AspisR1.NKR_TermSemanticSource
end
