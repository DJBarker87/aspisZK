import NMT_345StepTagExpected
import NMT_R2_PlainObservation
set_option autoImplicit false
noncomputable section
namespace NMT_R2_345AtTag
open Aeneas Aeneas.Std NMT_345 RSL
abbrev Variant := NMT_stage1_owned.aspis_r1_cost_probe.transport.Variant

def tagCall (v : Variant) : Result U8 :=
 AspisR1PublicPreparation.transport.Variant.tag
  (match v with | .S1 => .S1 | .S2 => .S2 | .D => .D)

theorem tag_s2 : tagCall .S2 = .ok 2#u8 := by
 unfold tagCall
 rw [NFY_NBG_Transport.tag_result]
 rfl

def install (c : Calls) : Calls := {c with c3 := tagCall}

theorem boundary {W : Type} (c : Calls) (s : TagByte W) :
 tailTagExpected (install c) s = tailTagReply (install c) ⟨s,2#u8⟩ := by
 rw [stepTagExpected]
 change (do let tag ← tagCall .S2; tailTagReply (install c) ⟨s,tag⟩) = _
 rw [tag_s2]
 rfl

theorem observation (env : Env) :
 Spec.pure NMT_R2.TX1_345.S2_TAG env (NMT_R2_PlainObservation.observe byte (tagCall .S2)) := by
 rw [tag_s2]
 rfl
#print axioms tag_s2
#print axioms boundary
#print axioms observation
end NMT_R2_345AtTag
end
