import R1Z.PV_Inv_TripleNorm
import R1Z.PV_Inv_DecodedNativeTests
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_PackedNormSafety
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitNativeQ48 (source)
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open R0P R0Z.HonestValidity PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_EntryReference
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_MapGlobalStep PV_Inv_GlobalSafety
variable {W : Type} [Zero W] [DecidableEq W]

theorem norms_at_slot (chi : Old.Q) (hc : Canonical chi)
    (banks : Banks QM31Exact) (t : Trace QM31Exact) (join : P_banks banks t) (lambda : QM31Exact)
    (weight : SourceLink QM31Exact → W) (registry : List (SourceLink QM31Exact)) (enumeration : P_registry registry)
    (es : List (Key × Entry Old.Q W)) (entry_join : es.map (keyed decode)=entries banks lambda weight registry)
    (canon : ∀ e ∈ es, Canonical e.2.value)
    (s : State Key Old.Q W) (run : PV_Inv_GlobalSlots.run (empty zero) es=some s)
    (safe : NoPole t lambda (decode chi)) (key : Key) (v : Old.Q)
    (hv : v ∈ PV_Inv_RawInvoke.reached (s key)) :
    ∃ d : Old.Q, field.QM31.sub (source chi) (source v)=ok (source d) ∧
      Canonical d ∧ decode d ≠ 0 ∧ PV_Inv_TripleNorm.SafeTower d := by
  obtain ⟨e,he,_,hval⟩ := PV_Inv_GlobalOrigin.origin zero es s run key v hv
  have cv : Canonical v := by rw [←hval];exact canon e he
  have nz := sub_ne_zero.mp (PV_Inv_DecodedSafety.reached_nonzero decode zero rfl banks t join lambda
    (decode chi) weight registry enumeration es entry_join s run safe key v hv)
  obtain ⟨d,inv,hd,hcd,hnd,_,_,_⟩ := PV_Inv_NativeQ.subtract_nonzero chi v hc cv nz
  exact ⟨d,hd,hcd,hnd,PV_Inv_TripleNorm.nonzero_tower d hcd hnd⟩

#print axioms norms_at_slot
end R1Z.PV_Inv_PackedNormSafety
