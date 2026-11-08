import PV_LIB_SPEC_Boundary
import PV_LIB_Box458
import PV_THR2_OwnInitSourceCodec
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Composition
open PV_STX2_Syntax PV_OWN2_Codec

/-- Literal source Box constructor retained by CLOSED458/537. Cast/source/binary
binding must still be derived at the actual14756; this term alone is no history. -/
def taggedPayload (unique allocator thread : Data) : Data :=
  PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
    [thread,PV_THR2_Box537Suffix13.boxed unique allocator]

def Legacy14756 (payload : Data) : Prop :=
  ∃ words, PV_THR2_OwnInitSourceCodec.decode payload = some words

theorem tagged_rejects_legacy (unique allocator thread : Data) :
    PV_THR2_OwnInitSourceCodec.decode (taggedPayload unique allocator thread) = none := rfl

/-- Checked contradiction for the OLD source/value premise combination only.
The frozen specification uses decodeBridged and does not have this premise. -/
theorem legacy_joint_contradiction (unique allocator thread : Data) :
    ¬ ∃ payload, payload = taggedPayload unique allocator thread ∧ Legacy14756 payload := by
  rintro ⟨payload,rfl,words,decoded⟩
  rw [tagged_rejects_legacy] at decoded
  cases decoded

/-- Premises for a concrete composed instance must all hold on ONE instance.
This proposition is a target, not a theorem inhabiting it. The dependent family
prevents taking the machine and the entry from unrelated existential witnesses. -/
def JointNonempty {Instance : Type} (machine entry bindings : Instance → Prop) : Prop :=
  ∃ x, machine x ∧ entry x ∧ bindings x

/-- A conjunction of separately nonempty sets is not joint nonemptiness. -/
theorem separate_witnesses_insufficient :
    (∃ n : Nat, n = 0) ∧ (∃ n : Nat, n = 1) ∧ ¬ (∃ n : Nat, n = 0 ∧ n = 1) := by
  refine ⟨⟨0,rfl⟩,⟨1,rfl⟩,?_⟩
  rintro ⟨n,rfl,h⟩
  cases h

#print axioms tagged_rejects_legacy
#print axioms legacy_joint_contradiction
#print axioms JointNonempty
#print axioms separate_witnesses_insufficient
end PV_LIB_SPEC_Composition
