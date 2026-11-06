import NLH_TermDigestFrame
import NKR_TermScalarCut
import NKR_DigestWrapper
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_TermSemanticRoot
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_TermSemanticCut (Pair)
open pool_v1.pair_forest_semantic_terminal
/-- Deployed261 control: zero24,232,229,233,228,250, two scalar additions at
21/22, then the actual scalar258/preweighted230at92 tail. -/
def reference (pub : Public) (o : Openings) (s : Selectors) := do
 let schedule←add_schedule_lanes NKR_TermSemanticSource.zero pub o s
 let path←add_path_lanes schedule o s
 let value←add_value_lanes path o s
 let occupancy←add_occupancy_lanes value pub o s
 let digests←NKR_DigestWrapper.reference pub o s
 let packed←NKR_TermSemanticCut.digest_reference occupancy digests
 FIw_ScalarSuffix.run pub o s packed

/-- Complete261 SAME-argument typed-cut/source/cohort composition. The
packing clause of the generic digest bridge is discharged INTERNALLY from
the actual250/251 source result; no endpoint,child-success,Run or Ops premise
is retained. Candidate children232/233/250 remain next-ledger conditional.
Native certificate credit requires all named261 windows and matched controls. -/
theorem source (pub : Public) (o : Openings) (s : Selectors)
 (hd : NKR_DigestChildren.Domain pub) (hz : canonical o.z) (hs : canonical o.succ_z)
 (hx : canonical o.xor12_z) (hh : canonical s.high) (hl : canonical s.low)
 (asset : pub.asset_id.val<2147483647)
 (amount : (core.option.Option.unwrap_or pub.withdrawal_amount 0#u32).val<2147483647) :
 ∃ p : NKR_TermSemanticSource.Packet pub o s,
 ∃ digests : Pair, ∃ replies : Pair,
 ∃ scalar : NKR_TermScalarInvocation.Packet pub o s p.packedDigests,
 NKR_DigestWrapper.reference pub o s=ok digests ∧ (∀ g,Canon (digests g)) ∧
 NKR_TermSemanticCut.Trace pub o s (List.finRange 4) NKR_TermSemanticSource.zero p.occupancy ∧
 NKR_TermSemanticCut.DigestCut pub o s p.occupancy digests replies
  (NKR_TermSemanticCut.digestObservation pub o s p.occupancy p.packedDigests digests) ∧
 NKR_TermScalarCut.Cut pub o s p.packedDigests scalar (NKR_TermScalarCut.observations scalar) ∧
 scalar.out=p.out ∧ NKR_TermSemanticCut.digest_reference p.occupancy digests=ok p.packedDigests ∧
 reference pub o s=ok p.out ∧ semantic_packed pub o s=ok p.out := by
 obtain ⟨p,parent⟩:=NKR_TermSemanticSource.source pub o s hd hz hs hx hh hl asset amount
 obtain ⟨c,sums,digests,old,_,_,_,_,dc,cd,oldCall,cold,values⟩:=NKR_DigestRoot.source pub o s hd hz hh hl
 have sameOld : old=p.digests:=Result.ok.inj (oldCall.symm.trans p.digest_call)
 have pairing (g : Fin 2) : FIv_NativeValue.decode (digests g)=NLH_TermDigestFrame.packed p.digests g := by
  rw [values,sameOld]
  rfl
 obtain ⟨packed,direct,oldPacked,cp⟩:=NLH_TermDigestFrame.source pub o s p.occupancy p.digests digests p.canonical_occupancy p.canonical_digests cd pairing
 have samePacked : packed=p.packedDigests:=Result.ok.inj (oldPacked.symm.trans p.packed_digest_call)
 rw [samePacked] at direct
 obtain ⟨replies,packed',direct',_,_,digestCut,_⟩:=NKR_TermSemanticCut.digest_source pub o s p.occupancy digests p.canonical_occupancy cd
 have samePacked' : packed'=p.packedDigests:=Result.ok.inj (direct'.symm.trans direct)
 rw [samePacked'] at digestCut
 obtain ⟨scalar,scalarCall,scalarCut⟩:=NKR_TermScalarCut.source pub o s p.packedDigests hz hh hl p.canonical_packedDigests asset amount
 have sameOut : scalar.out=p.out:=Result.ok.inj (scalarCall.symm.trans p.scalar_call)
 have wrapper : NKR_DigestWrapper.reference pub o s=ok digests:=dc
 refine ⟨p,digests,replies,scalar,wrapper,cd,NKR_TermSemanticCut.prefix_source pub o s p,digestCut,scalarCut,sameOut,direct,?_,parent⟩
 simp only [reference,p.schedule_call,p.path_call,p.value_call,p.occupancy_call,wrapper,direct,p.scalar_call,bind_tc_ok]
#print source
#print axioms source
end AspisR1.NLH_TermSemanticRoot
end
