import NDG_ZeroRun
import NDM_Reference.Funs
set_option autoImplicit false
namespace NDM_ZeroSuffix
open Aeneas Aeneas.Std Result

theorem byte_drop (base tail : Slice U8) (start index : Nat)
 (same : tail.val=base.val.drop start) :
 NDG_ZeroStep.byte tail index = NDG_ZeroStep.byte base (start+index) := by
 simp only [NDG_ZeroStep.byte,same,List.getElem?_drop]

theorem tail_length (base tail : Slice U8) (start : Nat)
 (same : tail.val=base.val.drop start) : tail.val.length=base.val.length-start := by
 simp only [same,List.length_drop]

theorem advance (base tail next : Slice U8) (start : Nat)
 (same : tail.val=base.val.drop start) (step : next.val=tail.val.drop 1) :
 next.val=base.val.drop (start+1) := by
 simp only [step,same,List.drop_drop]

theorem allZero (base tail : Slice U8) (start : Nat)
 (same : tail.val=base.val.drop start) :
 NDG_ZeroRun.AllZero tail 0 ↔ NDG_ZeroRun.AllZero base start := by
 have size := tail_length base tail start same
 constructor
 · intro h j lo hi
   have hj : j-start<tail.val.length := by omega
   have value := h (j-start) (by omega) hj
   rw [byte_drop base tail start (j-start) same] at value
   simpa only [Nat.add_sub_of_le lo] using value
 · intro h j lo hi
   have hj : start+j<base.val.length := by omega
   have value := h (start+j) (by omega) hj
   rw [byte_drop base tail start j same]
   exact value

def resume (base : Slice U8) (i : Usize) : Result
 (core.result.Result Unit AdapterRw.solana_program_error.ProgramError) := do
 let pending ← AdapterRw.r1_pool_adapter.owned.require_zero_loop base i
 match pending with
 | none => ok (.Ok ())
 | some r => ok r

/-- Reuses the NDG induction; supplies the previously missing suffix/index model association. -/
theorem resume_suffix (base tail : Slice U8) (i : Usize)
 (cap : base.val.length≤65536) (bound : i.val≤base.val.length)
 (same : tail.val=base.val.drop i.val) :
 resume base i = AdapterRw.r1_pool_adapter.owned.require_zero tail := by
 classical
 have tc : tail.val.length≤65536 := by rw [tail_length base tail i.val same];omega
 unfold resume
 rw [NDG_ZeroRun.run base i cap bound,NDG_ZeroRun.value tail tc]
 have zeros := allZero base tail i.val same
 by_cases good : NDG_ZeroRun.AllZero base i.val
 · simp only [if_pos good,bind_tc_ok,if_pos (zeros.mpr good)]
 · simp only [if_neg good,bind_tc_ok,if_neg (mt zeros.mp good)]

#print axioms byte_drop
#print axioms tail_length
#print axioms advance
#print axioms allZero
#print axioms resume_suffix
end NDM_ZeroSuffix
