import NNG_PrepareCarriers087
import NNG_Context137
import LIB_Instances
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareInput087
open Aeneas Aeneas.Std NMP_prepare
open NMT_Transport (arr arr_inverse)
open NNG_PrepareCarriers087
abbrev Args := RSL.TX1_087.Args LIB_Instances.VL

def input (a : Args) (obs : RSL.Observer) (env : RSL.Env) : NMP_Emitted.Parent Unit Unit :=
 ⟨NNG_PublicSource137.digest env,NMP_Transport.fromT9 a.public_,NNG_Data137.bytes a.proof,(),
   NNG_Context137.observer obs,arr wideBack a.g,(),[]⟩

theorem proof_exact (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) :
 LIB_Carriers.bytes (input a obs env).bytes=a.proof := by
 unfold input NNG_Data137.bytes
 rw [dif_pos (show a.proof.length≤Usize.max by rw [domain.1]; scalar_tac)]
 exact LIB_Bytes.bytes_from _ _

theorem scratch_exact (a : Args) (obs : RSL.Observer) (env : RSL.Env) :
 arr wide (input a obs env).scratch=a.g := arr_inverse wideBack wide wideBack_inverse _

theorem no_observer (a : Args) (obs : RSL.Observer) (env : RSL.Env)
 (domain : RSL.TX1_087.Domain LIB_Instances.VL a obs) :
 (input a obs env).observer=none := by
 rw [domain.2.1]
 rfl
#print axioms proof_exact
#print axioms scratch_exact
#print axioms no_observer
end AspisR1.NNG_PrepareInput087
