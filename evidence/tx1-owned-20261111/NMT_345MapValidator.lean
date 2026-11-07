import NMT_345Raw_07
import NMT_345Raw_08
import NMT_345Validator
import NMT_328Fold
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
structure ValidationReply (W : Type) extends Decoded W where
 reply : core.result.Result Unit FormatError

def mapValidator (c : Calls) {W : Type} (s : ValidationReply W) : Result Ret := do
 let r ← c.c2
  r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
  s.reply ()
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | core.ops.control_flow.ControlFlow.Continue _ => raw08 c s.toDecoded
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame PE) residual
/-- One validator occurrence, before its separate map_err call. -/
theorem validator_call {W : Type} (c : Calls) (s : Decoded W) :
 raw07 c s = (do let r ← c.c7 s.statement; mapValidator c ⟨s,r⟩) := rfl

def installMapErr (c : Calls) : Calls :=
 {c with c2 := fun inst r o => NMT_first.NMT_std_map_err inst r o}
/-- Exactly the emitted closure: every format error maps to InvalidAccountData;
no log is emitted here. Full outer Result propagation is in validator_call. -/
theorem validator_map_std {W : Type} (c : Calls) (s : ValidationReply W) :
 mapValidator (installMapErr c) s =
 match s.reply with
 | .Ok _ => raw08 (installMapErr c) s.toDecoded
 | .Err _ => .ok (.Err .InvalidAccountData) := by
 cases h : s.reply <;> rfl
#print axioms validator_call
#print axioms validator_map_std
end NMT_345
