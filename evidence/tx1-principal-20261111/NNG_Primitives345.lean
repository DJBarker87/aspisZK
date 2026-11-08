import NNG_Calls345
import NNG_Model345
import NMT_R2_DistinctValue
import NMT_345ZeroSource
import NMT_R2_ByteEquality
import NNG_Observe345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Primitives345
open Aeneas Aeneas.Std NMT_345 RSL

theorem distinct {W : Type} (s : Selected W) (env : Env) :
 RS.ofExcept (requireDistinct [account s.proofAccount,account s.publicAccount,account s.checkpointAccount]) env
 (NNG_Observe345.observe id ((NNG_Calls345.calls env).c15 (selectedArray s))) := by
 change RS.ofExcept _ env (NNG_Observe345.observe id (distinctCall s))
 rw [NMT_R2_DistinctValue.source]
 have key_eq (a b : Key) : key a=key b ↔ a=b :=
  ⟨fun h=>key_injective h,fun h=>congrArg key h⟩
 by_cases h01 : s.proofAccount.key=s.publicAccount.key <;>
  by_cases h02 : s.proofAccount.key=s.checkpointAccount.key <;>
  by_cases h12 : s.publicAccount.key=s.checkpointAccount.key <;>
  simp [requireDistinct,distinctKeys,account,key_eq,eq_comm,h01,h02,h12,
   RS.ofExcept,Spec.pure,NNG_Observe345.observe,rustResult,pe]

#print axioms distinct

theorem readonly (a : Account) (env : Env) :
 RS.ofExcept (readonlyBuffer (account a)) env
 (NNG_Observe345.observe id ((NNG_Calls345.calls env).c13 a)) := by
 change RS.ofExcept _ env (NNG_Observe345.observe id (readonlyCall a))
 rw [readonly_closed]
 unfold readonlyBuffer account
 cases a.is_signer <;> cases a.is_writable <;> cases a.executable <;> rfl
#print axioms readonly

/-- Generic symbolic zero-loop supplement, not an expansion of the bounded
native CLOSED342 packet's domain. -/
theorem zero (b : Slice U8) (env : Env) :
 RS.ofExcept (requireZero (b.val.map byte)) env
 (NNG_Observe345.observe id ((NNG_Calls345.calls env).c16 b)) := by
 change RS.ofExcept _ env (NNG_Observe345.observe id (zeroCall b))
 rw [zero_value]
 unfold requireZero
 rw [NMT_R2_ByteEquality.zeros]
 cases b.val.all (· == 0#u8) <;> rfl

#print axioms zero
end AspisR1.NNG_Primitives345
