import NMX_R3_FrontierTotal
import NMX_R3_FrontierCanonicalTotal
set_option autoImplicit false
namespace NMX_R3_FrontierBridge
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_FrontierWords
local instance : Inhabited Row := ⟨Array.repeat 8#usize 0#u32⟩

def result (r : core.result.Result Frontier Unit) : Option (List Digest) :=
 match r with
 | .Ok a => some (a.val.map (fun r => r.val.map word))
 | .Err () => none

/-- Both complete loops agree, by their arbitrary-step inductions, at the same
bytes and next-leaf index. No successful-child or fixed-data hypothesis. -/
theorem value (t : Slice U8) (next : U64) (cap : t.val.length ≤ 768)
 (extent : 688 ≤ t.val.length) :
 ∃ r, NCV_Reference.decode_frontier t next = ok r ∧
  result r = TX2_217.frontierLoop (t.val.map byte) (long next) 20 := by
 classical
 refine ⟨NMX_R3_FrontierTotal.outcome t next,
  NMX_R3_FrontierTotal.value t next cap extent, ?_⟩
 rw [NMX_R3_FrontierCanonicalTotal.value]
 unfold NMX_R3_FrontierTotal.outcome
 split
 · simp only [result, NMX_R3_FrontierCarrier.rows_exact]
 · rfl
#print axioms value
end NMX_R3_FrontierBridge
