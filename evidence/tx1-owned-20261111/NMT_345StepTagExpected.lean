import NMT_345TailTagExpected
import NMT_345TailTagReply
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepTagExpected {W : Type} (c : Calls) (s : TagByte W) :
 tailTagExpected c s = (do let tag ← c.c3 NMT_stage1_owned.aspis_r1_cost_probe.transport.Variant.S2; tailTagReply c ⟨s,tag⟩) := rfl
#print axioms stepTagExpected
end NMT_345
