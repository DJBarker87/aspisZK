import NCG_TailLog
import LPf_ReductionWord
set_option autoImplicit false
namespace NCG_ReduceLog
open Aeneas Aeneas.Std Result
/-- Interpret the SAME logged reducer reply using the existing all-U64 law. -/
theorem substitute (input : U64) (reply : U32)
    (association : FIo_Native.fast_pairing.canonical.reduce input = ok reply) :
    reply.val = input.val % 2147483647 ∧ reply.val < 2147483647 := by
  obtain ⟨out,run,value,canonical⟩ := AspisR1.LPf_ReductionWord.native_reduce input
  have same : out = reply := Result.ok.inj (run.symm.trans association)
  exact same ▸ ⟨value,canonical⟩
#print axioms substitute
end NCG_ReduceLog
