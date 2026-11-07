import NNG_ConcreteGraph136
import NNG_LIBDecode
import NNG_LIBEvents136
import NNG_InstallState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteRecords136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_LIBScalar

theorem record25 (env : RSL.Env) (p : LIB_VCarriers.Prefix) :
    RSL.Spec.map NNG_LIBRecords.recordReply
      (NNG_Interpret136.call NNG_LIBEvents136.events "record25" (NNG_LIBData.lowerPrefix p,25#u8)
        (NNG_Install.validatedRecord (NNG_LIBData.lowerPrefix p) 25#u8)) env =
      (RSL.RE.ofExcept (LIB_VRecords.validatedRecord p 25)) env := by
  exact NNG_EnvCallGraph136.pure_at NNG_LIBRecords.recordReply NNG_LIBEvents136.events "record25" _ _ env _ _
    (NNG_LIBRecords.record p 25#u8) rfl
    (NNG_LIBEvents136.silent env "record25" _ _ (by decide) (by decide) (by decide))
#print axioms record25

theorem record26 (env : RSL.Env) (p : LIB_VCarriers.Prefix) :
    RSL.Spec.map NNG_LIBRecords.recordReply
      (NNG_Interpret136.call NNG_LIBEvents136.events "record26" (NNG_LIBData.lowerPrefix p,26#u8)
        (NNG_Install.validatedRecord (NNG_LIBData.lowerPrefix p) 26#u8)) env =
      (RSL.RE.ofExcept (LIB_VRecords.validatedRecord p 26)) env := by
  exact NNG_EnvCallGraph136.pure_at NNG_LIBRecords.recordReply NNG_LIBEvents136.events "record26" _ _ env _ _
    (NNG_LIBRecords.record p 26#u8) rfl
    (NNG_LIBEvents136.silent env "record26" _ _ (by decide) (by decide) (by decide))
#print axioms record26

theorem extra (fallback : Value) (env : RSL.Env) (r : r1_wire.ValidatedRecord)
    (domain : LIB_VDecode.Domain (toT14 r) 87) :
    RSL.Spec.map (NNG_LIBRecords.decodeReply fallback)
      (NNG_Interpret136.call NNG_LIBEvents136.events "extra" (r,87#usize)
        (NNG_ModelDecode.call 29#usize r 87#usize)) env =
      (RSL.RE.ofExcept (LIB_VRecordsAll.decodeK29 (toT14 r) 87)) env := by
  exact NNG_EnvCallGraph136.pure_at (NNG_LIBRecords.decodeReply fallback) NNG_LIBEvents136.events "extra" _ _ env _ _
    (NNG_LIBDecode.decode fallback r 87#usize domain.1 domain.2) rfl
    (NNG_LIBEvents136.silent env "extra" _ _ (by decide) (by decide) (by decide))
#print axioms extra

theorem beforeZ1 (fallback : Value) (env : RSL.Env) (r : r1_wire.ValidatedRecord)
    (domain : LIB_VDecode.Domain (toT14 r) 0) :
    RSL.Spec.map (NNG_LIBRecords.decodeReply fallback)
      (NNG_Interpret136.call NNG_LIBEvents136.events "beforeZ1" (r,0#usize)
        (NNG_ModelDecode.call 29#usize r 0#usize)) env =
      (RSL.RE.ofExcept (LIB_VRecordsAll.decodeK29 (toT14 r) 0)) env := by
  exact NNG_EnvCallGraph136.pure_at (NNG_LIBRecords.decodeReply fallback) NNG_LIBEvents136.events "beforeZ1" _ _ env _ _
    (NNG_LIBDecode.decode fallback r 0#usize domain.1 domain.2) rfl
    (NNG_LIBEvents136.silent env "beforeZ1" _ _ (by decide) (by decide) (by decide))
#print axioms beforeZ1

theorem payload2 (env : RSL.Env) (p : LIB_VCarriers.Prefix) :
    RSL.Spec.map NNG_LIBRecords.payloadReply
      (NNG_Interpret136.call NNG_LIBEvents136.events "payload2" (NNG_LIBData.lowerPrefix p,2#u8)
        (NNG_Install.payload (NNG_LIBData.lowerPrefix p) 2#u8)) env =
      (RSL.RE.ofExcept (LIB_VRecords.payload p 2)) env := by
  exact NNG_EnvCallGraph136.pure_at NNG_LIBRecords.payloadReply NNG_LIBEvents136.events "payload2" _ _ env _ _
    (NNG_LIBRecords.payload p 2#u8) rfl
    (NNG_LIBEvents136.silent env "payload2" _ _ (by decide) (by decide) (by decide))
#print axioms payload2

theorem state (env : RSL.Env) (t : r1_wire.SemanticTranscript Unit) :
    RSL.Spec.map LIB_Carriers.b32
      (NNG_Interpret136.call NNG_LIBEvents136.events "state" t
        (NNG_Install.state (NNG_LIBDigest.digest env) t)) env =
      (RSL.Spec.pure (LIB_VCarriers.state (toT10 t))) env := by
  apply NNG_EnvCallGraph136.pure_at LIB_Carriers.b32 NNG_LIBEvents136.events "state" t _ env _ _
  · rw [NNG_Install.state_source]
    rfl
  · rfl
  · exact NNG_LIBEvents136.silent env "state" _ _ (by decide) (by decide) (by decide)
#print axioms state
end AspisR1.NNG_ConcreteRecords136
