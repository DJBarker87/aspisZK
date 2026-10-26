import R1Z.PDict_SaltClear
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Fence
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_Publication.native

/-- Pinned compiler_fence source branches, including invalid Relaxed panic.
P6 checks the four valid native orders and the constant invalid-order panic.
This value interpretation asserts no cross-thread synchronization/ordering law. -/
def fence : core.sync.atomic.Ordering → Result Unit
  | .Relaxed => .fail .panic
  | _ => .ok ()

@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_SaltClear.selected base ops with op13 := fence }

theorem op13_installed (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    (selected base ops).op13 = fence := rfl

theorem relaxed_panics : fence .Relaxed = .fail .panic := rfl

theorem seqcst_returns : fence .SeqCst = .ok () := rfl

#print axioms op13_installed
#print axioms relaxed_panics
#print axioms seqcst_returns
end R1Z.PDict_Fence
