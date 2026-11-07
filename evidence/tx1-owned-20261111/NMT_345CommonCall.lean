import NMT_345EncoderCall
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- The single common() occurrence; encoder remains opaque in this step. -/
theorem common_call {W : Type} (c : Calls) (s : Decoded W) :
 raw08 c s = (c.c6 s.statement >>= fun common => callEncoder c ⟨s,common⟩) := rfl
#print axioms common_call
end NMT_345
