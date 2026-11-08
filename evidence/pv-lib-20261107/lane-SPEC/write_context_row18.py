"""Emit ONE ordinary successor statement; compile it before the next invocation."""
from pathlib import Path
import sys
row=int(sys.argv[1]);assert row in [270,166,15,208,220,219,125,6,170,17,5,2,1]
p=Path(__file__).resolve().parents[3]/'lean'/f'PV_LIB_SPEC_ContextF{row}18.lean'
assert not p.exists(),p
p.write_text(f'''import PV_LIB_SPEC_ContextPost18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextF{row}18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
abbrev Input := F{row}.Input
abbrev Pre := F{row}.Pre
abbrev MachineSpec := PV_LIB_SPEC_ContextMachine18.MachineSpec
abbrev Before := F{row}.Contract

/-- SPEC-C14: unchanged full entry and source frame; actual context-bound v2
reference, full replies and every failure/pending/divergence arm. -/
def Post (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (i : Input)
    (issued : List Issued) (consumed : List Context) (candidate : Nat → Execution) : Prop :=
  PV_LIB_SPEC_ContextPost18.ordinary cut p PV_THR2_F{row}.live i issued consumed candidate

def Contract (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (implementation : PV_LIB_SPEC_ContextMachine18.Machine → Input →
      List Issued → List Context → Nat → Execution) : Prop :=
  ∀ m i issued consumed, MachineSpec cut p m → Pre p i →
    Post cut p i issued consumed (implementation m i issued consumed)

theorem pre_same (p : Parameters) (i : Input) : Pre p i ↔ F{row}.Pre p i := Iff.rfl

#print axioms Input
#print axioms Pre
#print axioms MachineSpec
#print axioms Before
#print axioms Post
#print axioms Contract
#print axioms pre_same
end PV_LIB_SPEC_ContextF{row}18
''')
