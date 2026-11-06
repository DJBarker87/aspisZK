import NKI_ValueCuts
import NKI_ValueAssociation
import NKI_RangeAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueRoot
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
open NKI_ValuePrefix (Openings Selectors)
/-- Complete233 candidate: SAME selector/prefix/reconstruction fields,
ZERO33three-loop native induction and full raw emitted-array association,
all tail frames, actual shared49/conservation82calls and full24poststate.
Every child Result is derived internally; no Ops/Run/success premise. -/
theorem source (packed : Array NQ 24#usize) (o : Openings) (s : Selectors)
 (hp : canonical packed) (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
 (hh : canonical s.high) (hl : canonical s.low) :
 ∃ (l : NKI_ValueTrace.Locals) (c : NKI_ConservationInvocation.Locals)
 (a b r3 : NJX_RangeStep.State) (middle out : Array NQ 24#usize),
 NKI_ValueTrace.Clauses o s l ∧ NKI_ValueTrace.Canonical o l ∧ NKI_ValueFields.Reads o l ∧
 (∀ g : Fin 3,pool_v1.pair_forest_copy_terminal.Selectors.row s (NKI_ValueFields.row g)=ok (NJB_ArrayCarrier.cell l.value_selectors g)) ∧
 NJX_RangeFold.Trace 0 (NJX_RangeInvocation.xs o 0) (List.finRange 10) NJX_RangeInvocation.zero a ∧
 NJX_RangeFold.Trace 1 (NJX_RangeInvocation.xs o 1) (List.finRange 10) a b ∧
 NJX_RangeFold.Trace 2 (NJX_RangeInvocation.xs o 2) (List.finRange 10) b r3 ∧
 l.range3=NJB_ArrayCarrier.array (N:=33#usize) r3 ∧ l.i=1024#u32 ∧ l.i1=1048576#u32 ∧
 NKI_ValueCuts.Cut packed o s l c middle out (NKI_ValueCuts.observations packed o s l c middle out) ![3,3,8,1,5,1] ∧
 NJL_SharedRoot.reference packed l.range6 l.range_selector=ok middle ∧
 NKI_ConservationInvocation.Clauses middle o s out c ∧
 NKI_ValueAssociation.reference packed o s=ok out ∧
 pool_v1.pair_forest_semantic_terminal.add_value_lanes packed o s=ok out ∧ canonical middle ∧ canonical out := by
 obtain ⟨l,trace,hc⟩ := WP.spec_imp_exists (NKI_ValueTrace.source o s hz hs hx hh hl)
 have calls:=NKI_ValueTraceFactor.clauses o s l trace
 have prefixCall : NKI_ValuePrefix.run o s=ok (NKI_ValueTrace.output l) := by
  rw [←NKI_ValueTraceFactor.source o s,trace,bind_tc_ok]
 obtain ⟨t,middle,out,ct,ot,ht,cm,co,hm,ho,cr,cs⟩ := NKI_ValueAssociation.source packed o s hp hz hs hx hh hl
 have same : t=NKI_ValueTrace.output l := Result.ok.inj (ct.symm.trans prefixCall)
 subst t
 obtain ⟨c,cc⟩ := NKI_ConservationInvocation.source middle o s out co
 obtain ⟨a,b,r3,ca,ta,cb,tb,cc3,tc,h3,loops⟩ := NKI_RangeAssociation.source o hz hs hx
 have sameRange : l.range3=NJB_ArrayCarrier.array (N:=33#usize) r3 :=
  congrArg Prod.snd (Result.ok.inj ((NKI_ValueFields.loops o s l calls hc).symm.trans loops))
 have tail:=NKI_ValueFrames.source o s l calls
 exact ⟨l,c,a,b,r3,middle,out,calls,hc,NKI_ValueFields.reads o s l calls hc,NKI_ValueFields.rows o s l calls hh hl,
  ta,tb,tc,sameRange,tail.1,tail.2.1,NKI_ValueCuts.source packed o s l c middle out calls,cm,cc,cr,cs,hm,ho⟩
#print source
#print axioms source
end AspisR1.NKI_ValueRoot
end
