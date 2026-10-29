import R1Z.PV_RunJoin_NativeActual63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ResidualSuccess63
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
/-- Minimal outer and inner successful terminal result on some input. -/
def Op227Success : Prop :=
  ∃ (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (points : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (alpha : Array aspis_core.field.QM31 10#usize)
    (challenges : aspis_core.state_only_prefix.r0.Challenges) (q : aspis_core.field.QM31),
    aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      public1 points alpha challenges=ok (.Ok q)
/-- Minimal successful worker result on some input; no row law is smuggled in. -/
def Op257Success : Prop :=
  ∃ (T F : Type) (inst : core.ops.function.Fn F Usize T) (cost count : Usize)
    (f : F) (out : alloc.vec.Vec T), host_work.map inst cost count f=ok out

#print axioms Op227Success
#print axioms Op257Success
end R1Z.PV_RunJoin_ResidualSuccess63
