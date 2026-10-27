import R1Z.PV_RunJoin_BankIdentification20
import R1Z.PV_RunJoin_SingleOutput20
import R1Z.PV_RunJoin_SuperScan20
import R1Z.PV_RunJoin_ValueBits20
import R1Z.PV_RunJoin_CompilerChecks17
import R1Z.PV_RunJoin_LateAppend18
import R1Z.PV_RunJoin_SelectedCheck16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CompilerWithdrawal20
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 pair_forest_copy_builder
open PV_RunJoin_FixtureArguments PV_RunJoin_ReferenceFixtureResults
local instance : ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : Records := PV_RunJoin_CompilerDictionary16.shipped

def withdrawalCall := pair_forest_trace.compile_forest_from_copies witness 250#u32 none
  withdrawalChange (PV_Src_NativeInput.forestPublic withdrawalRequest) laneAnchor snapshot

theorem withdrawal : ∃ compiled, withdrawalCall = ok (.Ok compiled) ∧
    compiled.public_statement = ⟨snapshot,PV_RunJoin_LateAppend18.result
      PV_RunJoin_AppendNative17.withdrawal0 PV_RunJoin_AppendNative17.withdrawal20⟩ := by
  unfold withdrawalCall pair_forest_trace.compile_forest_from_copies
  rw [show (PV_Src_NativeInput.forestPublic withdrawalRequest).asset = 77#u32 from rfl]
  rw [PV_RunJoin_FixtureReturns16.withdrawal_new]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_SelectedCheck16.selected,PV_RunJoin_InputLeaf16.withdrawal]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_SelectedCheck16.comparison]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_PathChecks16.withdrawal_pair,PV_RunJoin_PairLeafCheck16.leaf]
  simp only [bind_tc_ok,BuilderForestStdPort.core.result.Result.map_err,BuilderAdmissionStd.mapErr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_PathChecks16.withdrawal_lane]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_Nullifier16.withdrawal]
  rw [show PV_RunJoin_RecordedTransfer.publicRecord.nullifier = PV_RunJoin_RecordedWithdrawal.publicRecord.nullifier from rfl]
  simp only [bind_tc_ok]
  simp only [PV_Src_NativeInput.forestPublic,withdrawalRequest]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_NullifierSource17.withdrawal]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_OutputChecks16.withdrawal_change]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_SingleOutput20.source]
  simp only [bind_tc_ok,BuilderForestStdPort.core.result.Result.map_err,BuilderAdmissionStd.mapErr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [PV_RunJoin_OutputPair17.withdrawal]
  simp only [bind_tc_ok]
  have he : PV_RunJoin_OutputPair17.withdrawalPair = PV_RunJoin_AppendNative17.withdrawal0 := by
    with_unfolding_all rfl
  rw [he,PV_RunJoin_LateAppend18.withdrawal]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,core.slice.Slice.iter,
    BuilderForestStdPort.core.iter.traits.iterator.Iterator.flatten.default,BuilderForestStd.flatten]
  have hscan := PV_RunJoin_SuperScan20.source
  dsimp only [PV_RunJoin_SuperScan20.iterator,PV_RunJoin_SuperScan20.predicate,
    PV_RunJoin_SuperScan20.initial,PV_RunJoin_SuperScan20.input,PV_RunJoin_SuperScan20.WordArray] at hscan
  simp only [BuilderForestStdPort.core.iter.traits.iterator.Iterator.any.default]
  rw [hscan]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_PathChecks16.withdrawal_anchor]
  rw [show PV_RunJoin_RecordedTransfer.publicRecord.anchor_root = PV_RunJoin_RecordedWithdrawal.publicRecord.anchor_root from rfl]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_SourceBanks19.withdrawal]
  simp only [bind_tc_ok,BuilderForestStdPort.core.option.Option.ok_or,BuilderForestStd.okOr,core.result.Result.Insts.CoreOpsTry.branch]
  rw [PV_RunJoin_BankIdentification20.withdrawal]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  rw [show BuilderForestStdPort.core.array.from_fn 24#usize
      pair_forest_trace.compile_forest_from_copies.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      (witness.pair,witness) = ok (BuilderRecordsPath.bits (PV_Src_NativeDirections.reference witness)) from
    PV_Src_NativeDirections.run_eq witness]
  simp only [bind_tc_ok,PV_RunJoin_ValueBits20.source]
  exact ⟨_,rfl,rfl⟩
#print axioms withdrawal
end R1Z.PV_RunJoin_CompilerWithdrawal20
