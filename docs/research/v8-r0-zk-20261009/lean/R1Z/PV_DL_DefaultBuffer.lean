import R1Z.PV_AL_BlockCodec
import R1Z.PV_CBL_WrapperReference
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_DefaultBuffer
open PV_CBL_GenericArrayPower PV_CBL_LibraryShapes
set_option autoImplicit false

def zeroStorage : Storage U8 6 := PV_AL_BlockCodec.encode 6 (List.replicate 64 0#u8)
def initial : Buffer (Storage U8 6) := ⟨zeroStorage,0#u8,()⟩
def model {T : Type} (core : Result T) : Result (Wrapper T (Storage U8 6)) :=
  PV_CBL_WrapperReference.makeDefault core (ok initial)

theorem bytes : flatten 6 zeroStorage=List.replicate 64 0#u8 :=
  PV_AL_BlockCodec.flatten_encode 6 _ (by simp)

theorem success {T : Type} (core : T) : model (ok core)=ok ⟨core,initial⟩ := rfl

theorem failure {T : Type} (e : Error) : model (.fail e : Result T)=.fail e := rfl

theorem divergence {T : Type} : model (.div : Result T)=.div := rfl

theorem nonvacuous {T : Type} (core : T) : ∃ v, model (ok core)=ok v :=
  ⟨⟨core,initial⟩,success core⟩

theorem position : initial.pos.val=0 := rfl

#print axioms zeroStorage
#print axioms initial
#print axioms model
#print axioms bytes
#print axioms success
#print axioms failure
#print axioms divergence
#print axioms nonvacuous
#print axioms position
end R1Z.PV_DL_DefaultBuffer
