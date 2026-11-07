import AdapterRwModel
set_option autoImplicit false
noncomputable section
namespace NND_FreshFirstDecoded
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
def fresh (ops : Ops)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize) :
  Result (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
  := do
  let o ← (observer ops)
  let r ←
    ops.op10
      (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) public1 public_bytes proof k
      () o
  core.result.Result.map_err (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error
    solana_program_error.ProgramError) r (ops.op44)

theorem source (ops : Ops)
 (p : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pub proof : Slice U8) (k : Usize) :
 fresh ops p pub proof k = first_decoded ops p pub proof k := rfl
#print axioms source
end NND_FreshFirstDecoded
end
