import NOC_Run5bHost
import NNH_Run5bCurrentView
import NNV_ViewInverse
import NNX_PreparedValue
import LIBC_WideView
import LIBC_ParseShape
import LIBC_ExpandValues
import LIBC_ExpandSemantic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_ConvLeaves
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

abbrev cur {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
 DrvC_Installation.currentInstalled (NOC_Run5bCtx.configuration c)

/-- Converse, filled (TX1:064): an Ok allocation reply forces the granted
reservation and the zero buffer. -/
theorem filled {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (n : Usize) (v : alloc.vec.Vec U8)
 (h : (cur c).op1 core.marker.CopyU8 n 0#u8 = .ok (.Ok v)) :
 (NNH_HostCtx.envOf c).reservation = true ∧
 v.val = List.replicate n.val 0#u8 := by
 change NOC_HostSeed.filled (NNH_HostCtx.envOf c).reservation core.marker.CopyU8 n 0#u8 = _ at h
 unfold NOC_HostSeed.filled at h
 rw [LIBC_Filled.model n (NNH_HostCtx.envOf c)] at h
 cases hr : (NNH_HostCtx.envOf c).reservation with
 | false => rw [hr] at h; simp at h
 | true =>
  rw [hr] at h
  simp only [↓reduceIte,bind_tc_ok] at h
  refine ⟨rfl,?_⟩
  injection h with h
  injection h with h
  rw [← h]

/-- Converse, library filled value at a granted reservation. -/
theorem filled_value (env : RSL.Env) (n : Nat) (granted : env.reservation = true) :
 LIBC_Filled.value n env = .ok (List.replicate n (0 : UInt8)) := by
 unfold LIBC_Filled.value; rw [granted]; rfl

/-- Converse, expand_semantic: the library value is total. -/
theorem expand_semantic (x : RSL.Bytes × RSL.Bytes) (env : RSL.Env) :
 LIBC_ExpandSemantic.value x env =
 .ok (LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output (LIBC_Bytes.raw x.1))) := rfl

/-- Converse, expand_values on the fixed prepare windows. -/
theorem expand_values (x : RSL.Bytes × RSL.Bytes) (env : RSL.Env)
 (l1 : x.1.length = 464) (l2 : x.2.length = 928) :
 LIBC_ExpandValues.value x env = .ok (LIB_Carriers.bytes
  (LIBC_ExpandValuesModel.output (LIBC_Bytes.raw x.1) (LIBC_Bytes.raw x.2))) := by
 unfold LIBC_ExpandValues.value
 rw [if_pos ⟨by rw [l1],by rw [l1,l2]⟩]

/-- Converse, parse_shape (op3): an Ok installed parse is an ok library parse. -/
theorem parse (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) (variant : transport.Variant)
 (h : (NNH_Run5bCurrentShape.current m env err r).op3 proof = .ok (.Ok variant)) (env' : RSL.Env) :
 LIBC_ParseShape.value (LIB_Carriers.bytes proof) env' = .ok () := by
 rw [NNH_Run5bCurrentShape.slot] at h
 unfold Op3I_Install.sourceBody at h
 unfold LIBC_ParseShape.value LIBC_ParseShape.model
 rw [LIBC_Bytes.from_native]
 cases hp : Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof with
 | ok reply =>
  cases reply with
  | Ok v => rfl
  | Err e => rw [hp] at h; simp at h
 | fail e => rw [hp] at h; simp at h
 | div => rw [hp] at h; simp at h

/-- Converse, wide view (op5): an Ok installed view is the SAME library view. -/
theorem view (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof semantic y1 : Slice U8)
 (width : proof.val.length=57607) (ls : semantic.val.length=13831) (ly : y1.val.length=928)
 (v' : verifier.View)
 (h : (NNH_Run5bCurrentShape.current m env err r).op5 proof semantic y1 = .ok (.Ok v')) (env' : RSL.Env) :
 ∃ v, LIB_VLib.wideViewValue (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) env' = .ok v ∧
 NNV_PreparedInputs.view v = v' := by
 rw [NNH_Run5bCurrentView.slot] at h
 unfold InstalledPreparation.sourceView at h
 have domain : LIBC_WideView.Domain (LIB_Carriers.bytes proof,LIB_Carriers.bytes semantic,LIB_Carriers.bytes y1) := by
  simpa only [LIBC_WideView.Domain,LIB_Carriers.bytes,NMS_R2N_RSLScalars.bytes,List.length_map] using
   And.intro width (And.intro ls ly)
 have mapped := LIBC_WideView.model_port _ env' domain
 simp only [LIBC_Bytes.from_native] at mapped
 cases hn : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1 with
 | ok reply =>
  cases reply with
  | Ok native =>
   rw [hn] at h mapped
   simp only [bind_tc_ok] at h mapped
   injection h with h
   injection h with h
   subst h
   refine ⟨AspisR1SelectedWideViewV1.preparedView native,?_,?_⟩
   · exact (Result.ok.inj mapped).symm
   · rw [← LIBC_WideView.emitted_copy native,NNV_ViewInverse.source]
  | Err e => rw [hn] at h; simp at h
 | fail e => rw [hn] at h; simp at h
 | div => rw [hn] at h; simp at h

/-- Converse, prepared (op8): an Ok installed Prepared::new is the SAME
library LIB_Prepared value, scratch included. -/
theorem prepared {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx)
 (sem : RSL.Verified LIB_VLib.library) (v : LIB_VCarriers.View) (g : LIB_VCarriers.E29)
 (p' : verifier.Prepared) (g'' : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (h : (cur c).op8 (NNV_PreparedAtHost.digest c) (NNV_PreparedInputs.sem sem)
   (NNV_PreparedInputs.view v) () (NNV_PreparedInputs.scratch g) = .ok (.Ok p',g'')) :
 ∃ p after, LIB_Prepared.value (sem,v,g) (NNH_Run5bCtx.envOf c) = (.ok p,after) ∧
 p' = InstalledPreparation.currentPrepared p ∧ g'' = NNV_PreparedInputs.scratch after := by
 have h' : (DrvC_Installation.currentInstalled (NNH_Run5bCtx.configuration c)).op8 (NNV_PreparedAtHost.digest c)
   (NNV_PreparedInputs.sem sem) (NNV_PreparedInputs.view v) () (NNV_PreparedInputs.scratch g) = .ok (.Ok p',g'') := h
 rw [NNV_PreparedAtHost.source,NNV_PreparedInputs.semantic,NNV_PreparedInputs.view_input,
  NNV_PreparedInputs.scratch_input] at h'
 have val : LIB_Prepared.value (sem,v,g) (NNH_Run5bCtx.envOf c) =
   (match NGN_Emitted.prepared NHL_PreparedScalars.actual (LIBC_PreparedLog.digest (NNH_Run5bCtx.envOf c))
     (LIBC_PreparedCarriers.verified LIB_Prepared.types sem) v () g with
    | .ok r => LIBC_PreparedLaw.port r
    | _ => (.error .Parse,g)) := by
  change LIB_Prepared.output (LIBC_PreparedLaw.value (LIB_Prepared.input (sem,v,g)) (NNH_Run5bCtx.envOf c)) = _
  rw [NNX_PreparedValue.identity]
  unfold LIBC_PreparedLaw.value
  rw [LIBC_PreparedLaw.native_result]
  rfl
 cases hn : NGN_Emitted.prepared NHL_PreparedScalars.actual (LIBC_PreparedLog.digest (NNH_Run5bCtx.envOf c))
   (LIBC_PreparedCarriers.verified LIB_Prepared.types sem) v () g with
 | ok pair =>
  rcases pair with ⟨reply,scratch⟩
  rw [hn] at h' val
  simp only [bind_tc_ok] at h'
  cases reply with
  | Ok prep =>
   injection h' with h'
   injection h' with h1 h2
   injection h1 with h1
   exact ⟨prep,scratch,val,h1.symm,h2.symm⟩
  | Err e => simp at h'
 | fail e => rw [hn] at h'; simp at h'
 | div => rw [hn] at h'; simp at h'
#print axioms filled
#print axioms filled_value
#print axioms expand_semantic
#print axioms expand_values
#print axioms parse
#print axioms view
#print axioms prepared
end AspisR1.NOC_ConvLeaves
end
