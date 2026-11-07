import NNH_ValidateHeadStep
import NNH_ValidateTailPort
import NNH_RequestGuards
import NNH_ClockOk
set_option autoImplicit false
noncomputable section
namespace NNH_ValidatePort
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem value (base : Ops) (env : RSL.Env) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (clock : core.result.Result U64 solana_program_error.ProgramError) (out : RSL.TX2_242.Validated L)
 (success : NNH_ValidateEval.value L D LIBB_PoolLib.values ⟨key program,accounts xs,bytes data,reply slot clock⟩ env=.ok out) :
 ∃ native,r1_pool_adapter.owned.validate_asq8 (NNH_Tx2ModelSlots.install base env) program xs data clock=.ok (.Ok native) ∧ NNH_ValidatedCarrier.value native=out := by
 obtain ⟨packet⟩ := NNH_ValidateCut.produce L D LIBB_PoolLib.values _ env out success
 have length : data.val.length=320 := by
  simpa only [bytes,List.length_map,RSL.REQUEST_BYTES] using packet.length
 have decode := NNH_RequestOk.decode data packet.request packet.decode
 obtain ⟨profile,release,pool⟩ := NNH_RequestGuards.value packet.request packet.guards
 obtain ⟨lane,lane_ok,lane_eq⟩ := NNH_RequestOk.lane packet.request packet.lane packet.lane_ok
 obtain ⟨time,clock_ok,time_eq⟩ := NNH_ClockOk.value clock packet.slot packet.clock
 have auth_ok := packet.auth_ok
 rw [←lane_eq,←time_eq] at auth_ok
 obtain ⟨nativeAuth,auth_run,auth_eq⟩ := NNH_AuthPort.value base env program packet.request.pool_program xs lane time packet.auth auth_ok
 obtain ⟨native,scan_run,output⟩ := NNH_ValidateTailPort.value base env program xs data (reply slot clock) out packet nativeAuth auth_eq
 have authenticate : NNH_ValidateFission.authenticate (NNH_Tx2ModelSlots.install base env) program xs packet.request packet.request.pool_program lane time=
  NNH_ValidateFission.scan (NNH_Tx2ModelSlots.install base env) xs packet.request nativeAuth := by
  unfold NNH_ValidateFission.authenticate
  simp only [auth_run,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 refine ⟨native,?_,output⟩
 rw [NNH_ValidateFission.source,clock_ok,NNH_ValidateHeadStep.source base env program xs data packet.request lane time length decode profile release pool lane_ok,authenticate]
 exact scan_run
#print axioms value
end NNH_ValidatePort
