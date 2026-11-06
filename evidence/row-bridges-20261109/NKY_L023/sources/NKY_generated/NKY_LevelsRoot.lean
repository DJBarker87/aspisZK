import NKY_LevelsLoop
import NKY_CanonicalLift
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_LevelsRoot
open Aeneas Aeneas.Std Result
open NJX_AppendDomains (Frontier High)
open NJX_DigestCohort (O dc)
open FIv_NativeValue (Canon)
/-- The complete literal Result, four returned field values and native frame,
with concrete CLOSED234 at each SAME reached child. Only input canonicality;
no child-success, Run/Ops, returned-output or endpoint premise. The caller
body is the retained emission port in NKY_LevelsLiteral with the sole child
slot instantiated by the NKI source/cut packet under (y)(3). -/
theorem source (index : U64) (f : Frontier) (o : O) (s : High)
 (hf : ∀ d∈f.val,dc d) (ho : FIw_ArrayValue.canonical o)
 (hs : FIw_ArrayValue.canonical s) :
 ∃ (packets : NKI_LevelsChildren.Family index f o s) (out : NJX_AppendFold.State),
 NKY_LevelsLiteral.append_levels_packed_selector_tensor NKY_LevelsLiteral.child index f o s=
  ok (NKY_CanonicalLift.cohort index f o s packets) ∧
 NKI_LevelsFrame.run index f o s (List.finRange 20) NKI_LevelsRoot.zero=ok out ∧
 NKY_LevelCarrier.pair out=NKY_CanonicalLift.cohort index f o s packets ∧
 NKI_LevelsNative.Trace index f o s (fun i=>NKI_AppendPacket.output (packets i))
  (List.finRange 20) NKI_LevelsRoot.zero out ∧
 (∀ j,Canon (out j)) := by
 obtain ⟨packets,out,_children,run,tr,hout,values⟩:=NKI_LevelsComplete.source index f o s hf ho hs
 have pair_eq:=NKY_CanonicalLift.result index f o s packets out hout values
 refine ⟨packets,out,?_,run,pair_eq,tr,hout⟩
 rw [NKY_LevelsLoop.entry,run,bind_tc_ok,pair_eq]
#print source
#print axioms source
end AspisR1.NKY_LevelsRoot
end
