import NMT_345TailSplitCast
import NMT_345TailChild
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepSplitCast {W : Type} (c : Calls) (s : HasSplitByte W) :
 tailSplitCast c s = (do let k ← lift (UScalar.cast .Usize s.splitByte); tailChild c ⟨s,k⟩) := rfl
#print axioms stepSplitCast
end NMT_345
