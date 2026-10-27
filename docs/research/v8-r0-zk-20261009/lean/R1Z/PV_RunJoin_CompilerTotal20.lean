import R1Z.PV_RunJoin_BankIdentification20
import R1Z.PV_RunJoin_OutputConstructor20
import R1Z.PV_RunJoin_SuperScan20
import R1Z.PV_RunJoin_ValueBits20
import R1Z.PV_RunJoin_CompilerChecks17
import R1Z.PV_RunJoin_LateAppend18
import R1Z.PV_RunJoin_SelectedCheck16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CompilerTotal20
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 pair_forest_copy_builder
open PV_RunJoin_FixtureArguments PV_RunJoin_ReferenceFixtureResults
local instance : ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : Records := PV_RunJoin_CompilerDictionary16.shipped

def transferCall := pair_forest_trace.compile_forest_from_copies witness 600#u32 (some recipient)
  transferChange (PV_Src_NativeInput.forestPublic transferRequest) laneAnchor snapshot

theorem transfer : ∃ compiled, transferCall = ok (.Ok compiled) ∧
    compiled.public_statement = ⟨snapshot,PV_RunJoin_LateAppend18.result
      PV_RunJoin_AppendNative17.transfer0 PV_RunJoin_AppendNative17.transfer20⟩ := by
  unfold transferCall pair_forest_trace.compile_forest_from_copies
  rw [show (PV_Src_NativeInput.forestPublic transferRequest).asset = 77#u32 from rfl]
  rw [PV_RunJoin_FixtureReturns16.transfer_new]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_SelectedCheck16.selected,PV_RunJoin_InputLeaf16.transfer]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_SelectedCheck16.comparison]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_PathChecks16.transfer_pair,PV_RunJoin_PairLeafCheck16.leaf]
  simp only [bind_tc_ok,BuilderForestStdPort.core.result.Result.map_err,BuilderAdmissionStd.mapErr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_PathChecks16.transfer_lane]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_Nullifier16.transfer]
  simp only [bind_tc_ok]
  simp only [PV_Src_NativeInput.forestPublic,transferRequest]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_NullifierSource17.transfer]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_OutputChecks16.transfer_change,PV_RunJoin_OutputChecks16.recipient]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_OutputConstructor20.source]
  simp only [bind_tc_ok,BuilderForestStdPort.core.result.Result.map_err,BuilderAdmissionStd.mapErr,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [PV_RunJoin_OutputPair17.transfer]
  simp only [bind_tc_ok]
  have he : PV_RunJoin_OutputPair17.transferPair = PV_RunJoin_AppendNative17.transfer0 := by
    with_unfolding_all rfl
  rw [he,PV_RunJoin_LateAppend18.transfer]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,core.slice.Slice.iter,
    BuilderForestStdPort.core.iter.traits.iterator.Iterator.flatten.default,BuilderForestStd.flatten]
  have hscan := PV_RunJoin_SuperScan20.source
  dsimp only [PV_RunJoin_SuperScan20.iterator,PV_RunJoin_SuperScan20.predicate,
    PV_RunJoin_SuperScan20.initial,PV_RunJoin_SuperScan20.input,PV_RunJoin_SuperScan20.WordArray] at hscan
  simp only [BuilderForestStdPort.core.iter.traits.iterator.Iterator.any.default]
  rw [hscan]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_PathChecks16.transfer_anchor]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_ZeroTree17.ne_self]
  simp only [bind_tc_ok,Bool.false_eq_true,if_false]
  rw [PV_RunJoin_SourceBanks19.transfer]
  simp only [bind_tc_ok,BuilderForestStdPort.core.option.Option.ok_or,BuilderForestStd.okOr,core.result.Result.Insts.CoreOpsTry.branch]
  rw [PV_RunJoin_BankIdentification20.transfer]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  rw [show BuilderForestStdPort.core.array.from_fn 24#usize
      pair_forest_trace.compile_forest_from_copies.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      (witness.pair,witness) = ok (BuilderRecordsPath.bits (PV_Src_NativeDirections.reference witness)) from
    PV_Src_NativeDirections.run_eq witness]
  simp only [bind_tc_ok,PV_RunJoin_ValueBits20.source]
  exact ⟨_,rfl,rfl⟩
#print axioms transfer
end R1Z.PV_RunJoin_CompilerTotal20
