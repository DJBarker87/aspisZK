import NHL_PrepareStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PrepareModel
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NHL_PrepareStages
/-- Only the two OPEN child semantics may change; CLOSED packet slots stay fixed. -/
def children (base expected : Ops) : Ops :=
 {base with op8:=expected.op8,op9:=expected.op9}

theorem buffers_children (base expected : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) : buffers (children base expected) D proof=buffers base D proof := by
 simp only [buffers,children]

#print axioms buffers_children
end AspisR1.NHL_PrepareModel
