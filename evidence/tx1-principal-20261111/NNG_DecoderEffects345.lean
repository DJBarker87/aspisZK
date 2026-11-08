import NNG_DecoderGraph345
import NNG_Model345
import NNG_Observe345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DecoderEffects345
open Aeneas Aeneas.Std NMT_345 RSL NNG_Obs345 NNG_Pure345

def reference (b : Bytes) : RS Statement :=
 RS.seq (RS.lift (Spec.allocIf (LIBC_S1.reaches b)))
 (RS.bind (RS.ofOption (LIBC_S1.decode b) .invalidAccountData)
 (fun st=>RS.seq (RS.lift Spec.alloc) (RS.pure st)))

def run (internal outer : Bool) (b : Slice U8) : Obs (Except ProgramError Statement) :=
 tryObs (allocationIf (LIBC_S1.reaches (LIB_Carriers.bytes b)) internal) fun _=>
 tryObs (NNG_Observe345.observe id (decodeCall b)) fun st=>
 tryObs (allocation outer) fun _=>silent (.ok st)

theorem value (b : Slice U8) (env : Env) :
 RS.ofOption (LIBC_S1.decode (LIB_Carriers.bytes b)) .invalidAccountData env
 (NNG_Observe345.observe id (decodeCall b)) := by
 rw [NNG_DecoderGraph345.source]
 cases LIBC_S1.decode (LIB_Carriers.bytes b) <;> rfl
#print axioms value

/-- Complete delivered-field decoder observation, including internal allocation
before decoder Err and the outer allocation only after Ok. Source-site reach
is supplied by LIBC_FirstBox and is not inferred from eventual success. -/
theorem law (internal outer : Bool) (b : Slice U8) (env : Env) :
 reference (LIB_Carriers.bytes b) env (run internal outer b) := by
 apply try_valid _ _ _ _ env (allocationIf_valid _ _ env)
 intro _
 apply try_valid _ _ _ _ env (value b env)
 intro st
 apply try_valid _ _ _ _ env (allocation_valid outer env)
 intro _
 rfl
#print axioms law
end AspisR1.NNG_DecoderEffects345
