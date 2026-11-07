import NMX_R3_PrimaryFrontierRun
import NMX_R3_FrontierWords
set_option autoImplicit false
namespace NMX_R3_FrontierPositive
open Aeneas Aeneas.Std Result NMX_R3_FrontierWords
local instance : Inhabited Row := ⟨Array.repeat 8#usize 0#u32⟩
/-- Complete success induction over the actual emitted reference loop.
Each step theorem was proved for an arbitrary accumulator/pre-state. -/
theorem value (t : Slice U8) (next : U64) (cap : t.val.length ≤ 768)
 (extent : 688 ≤ t.val.length) (valid : Valid t next) :
 NCV_Reference.decode_frontier t next = ok (.Ok (target t)) := by
 apply NMX_R3_PrimaryFrontierRun.value t next (target t)
 · intro i hi addr same
   exact field t next cap extent i hi (valid i.val hi) addr same
 · intro i hi
   exact guard t next i hi (valid i.val hi)
#print axioms value
end NMX_R3_FrontierPositive
