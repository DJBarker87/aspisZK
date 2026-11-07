import NNG_PrepareInput087
import LIBC_Slices
set_option autoImplicit false
namespace AspisR1.NNG_Slices087
open Aeneas Aeneas.Std Result
abbrev Args := NNG_PrepareInput087.Args

theorem proof_length (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) :
 (NNG_PrepareInput087.input a obs env).bytes.val.length=57607 := by
 have h := congrArg List.length (NNG_PrepareInput087.proof_exact a obs env domain)
 rw [NMS_R2N_RSLScalars.bytes_length] at h
 exact h.trans domain.1

theorem semantic_bytes (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) :
 LIB_Carriers.bytes (MultiproofConeSlices.sub (NNG_PrepareInput087.input a obs env).bytes 16#usize 7031#usize)=
 RSL.slice a.proof RSL.OFF_SEMANTIC RSL.OFF_Y1 := by
 rw [LIBC_Slices.bytes_sub,NNG_PrepareInput087.proof_exact a obs env domain]
 rfl

theorem values_bytes (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) :
 LIB_Carriers.bytes (MultiproofConeSlices.sub (NNG_PrepareInput087.input a obs env).bytes 7031#usize 7495#usize)=
 RSL.slice a.proof RSL.OFF_Y1 RSL.OFF_INACTIVE := by
 rw [LIBC_Slices.bytes_sub,NNG_PrepareInput087.proof_exact a obs env domain]
 rfl

theorem r4 (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) :
 NFU_Retarget.compact.check_values
  (MultiproofConeSlices.sub (NNG_PrepareInput087.input a obs env).bytes 7031#usize 7495#usize)=.ok (.Ok ()) := by
 apply (LIBC_CheckValuesDomain.native _).mp
 rw [values_bytes a obs env domain]
 exact domain.2.2.2
#print axioms proof_length
#print axioms semantic_bytes
#print axioms values_bytes
#print axioms r4
end AspisR1.NNG_Slices087
