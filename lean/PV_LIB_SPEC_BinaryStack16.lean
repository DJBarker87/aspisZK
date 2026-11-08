import PV_LIB_SPEC_TlsAt85
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_BinaryStack16
open PV_STX2_Store

/-- ELF fc8808eb: fac90..fac9a saves6 qwords and subtracts0x98;
fad8b/fad8c pushes2 arguments, fad90 CALL pushes the return address;
e0450..e045a saves6 qwords and subtracts0x58. These are address arithmetic
facts only, NOT a proof of original-entry native stack allocation. -/
def scopeRsp (entryRsp : Nat) : Nat := entryRsp-200
def spawnRsp (entryRsp : Nat) : Nat := entryRsp-360

theorem prologues (entryRsp : Nat) (bound : 360 ≤ entryRsp) :
    scopeRsp entryRsp = entryRsp-6*8-0x98 ∧
    spawnRsp entryRsp = scopeRsp entryRsp-2*8-8-6*8-0x58 := by
  dsimp [scopeRsp,spawnRsp]
  omega

/-- e0602 loads the run argument from spawnRsp+0x90; e05fa loads k from+0x98.
Those are EXACTLY the two slots made by fad8c/fad8b. fac a9 saved the incoming
scope RSI at scopeRsp; fad8c reads that slot after the first push. -/
theorem argument_slots (entryRsp : Nat) (bound : 360 ≤ entryRsp) :
    spawnRsp entryRsp+0x90 = scopeRsp entryRsp-16 ∧
    spawnRsp entryRsp+0x98 = scopeRsp entryRsp-8 ∧
    (scopeRsp entryRsp-8)+8 = scopeRsp entryRsp := by
  dsimp [scopeRsp,spawnRsp]
  omega

/-- Finite coordinate construction from the incoming native scope argument.
The source0/local12 relation, the actual incoming RSI, entry rsp and stack
grant still need ORIGINAL-history source/binary adequacy. No local fixture
or successful decode is silently used to establish any of those facts. -/
def frame (entryRsp runArgument activation : Nat) : PV_LIB_SPEC_PhysicalStack12.Frame :=
  ⟨activation,spawnRsp entryRsp,⟨0,12,[]⟩,runArgument⟩

theorem coordinates (entryRsp runArgument activation : Nat) :
    (frame entryRsp runArgument activation).rsp = entryRsp-360 ∧
    (frame entryRsp runArgument activation).runPointer = runArgument ∧
    (frame entryRsp runArgument activation).runSource = ⟨0,12,[]⟩ := ⟨rfl,rfl,rfl⟩

#print axioms scopeRsp
#print axioms spawnRsp
#print axioms prologues
#print axioms argument_slots
#print axioms frame
#print axioms coordinates
end PV_LIB_SPEC_BinaryStack16
