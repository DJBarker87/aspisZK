import NNH_Stage2Sizes
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2Suffix
open Aeneas Aeneas.Std Result AspisR1 AdapterRw

theorem source (ops : Ops) (val : r1_pool_adapter.ValidatedAsqa)
 (proof checkpoint segment : Slice U8) (encoded : Array U8 1880#usize)
 (proofSize : Slice.len proof=58295#usize) (validatedSize : val.proof_length=57607#usize)
 (late : ops.op19=.ok 1520#usize) (encode : ops.op22 val.statement=.ok (.Ok encoded))
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof ⟨688#usize,58295#usize⟩=.ok segment) :
 NNH_Stage2Fission.afterReads ops val proof checkpoint=(do
  let obs ← observer ops
  let reply ← ops.op11 (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) encoded.to_slice segment checkpoint () obs
  let mapped ← core.result.Result.map_err (BuiltinFnOnce aspis_r1_cost_probe.verifier.Error solana_program_error.ProgramError) reply ops.op44
  let cf ← core.result.Result.Insts.CoreOpsTry.branch mapped
  match cf with
  | .Continue _ => ops.op53 val.statement
  | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame solana_program_error.ProgramError) residual) := by
 have encodedSize : Slice.len encoded.to_slice=1880#usize := by
  apply UScalar.eq_of_val_eq
  exact encoded.property
 unfold NNH_Stage2Fission.afterReads
 rw [NNH_Stage2Sizes.afterstate]
 simp only [bind_tc_ok,validatedSize,NNH_Stage2Sizes.checkedEnd,lift,core.option.Option.ok_or,
  core.result.Result.Insts.CoreOpsTry.branch,proofSize,bne_self_eq_false,if_false,encode,
  core.result.Result.map_err,Port4C_GeometryStd.mapError]
 rw [NNH_Stage2Sizes.statement ops late]
 simp only [bind_tc_ok,encodedSize,bne_self_eq_false,if_false,range]
#print axioms source
end NNH_Stage2Suffix
