import R1Z.PV_RunJoin_WeightInstalled46
import R1Z.PV_RunJoin_WideArithmetic44
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SamplerRaw49
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitWideOps48
open PV_B2_C_ArrayDigits (limb)

def raw (a : Array U32 8#usize) : Raw :=
  (⟨⟨limb a 0,limb a 1⟩,⟨limb a 2,limb a 3⟩⟩,
   ⟨⟨limb a 4,limb a 5⟩,⟨limb a 6,limb a 7⟩⟩)

theorem native (a : Array U32 8#usize) :
    PV_B2_E_OrdinaryOriginal.toNative (PV_B2_C_ArrayDigits.raw a)=
      ProverRwDictionaryTower.fromW (source (raw a)) := rfl

theorem canonical (a : Array U32 8#usize) (h : PV_B2_C_ArrayDigits.canonical a) :
    ProverCommitWideOps48.canonical (raw a) :=
  ⟨⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩,⟨⟨h 4,h 5⟩,⟨h 6,h 7⟩⟩⟩
#print axioms raw
#print axioms native
#print axioms canonical
end R1Z.PV_RunJoin_SamplerRaw49
