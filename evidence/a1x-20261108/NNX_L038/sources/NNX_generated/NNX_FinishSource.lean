import NNX_ClaimPorts
import NNX_Comparisons
import NNX_RootCopy
import NNX_FinishDecodePort
import NNV_FinishNativePorts
import LIB_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_FinishSource
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers RSL
abbrev V := NNH_FinishReturns.V
abbrev B := IDa_Deployed.boundaries (.Ok ())

theorem source (a : TX1_136.Args V) (env : Env) (sem : Verified V)
 (called : NNH_FinishReturns.value a env = .ok sem) :
 FinishModel.finish NJM_RoundJoin.R B (LIB_VCode.digest env) a.public_
  (prefixRaw a.prefix_) a.transcript (challengesRaw a.challenges) none =
 .ok (.Ok (LIBC_PreparedCarriers.verified LIB_Prepared.types sem)) := by
 obtain ⟨head⟩ := NNV_FinishCut.returned a env sem called
 obtain ⟨tail⟩ := NNV_FinishTail.returned a env sem head
 have rounds := NNV_FinishNativePorts.rounds a.prefix_ a.transcript env head.rounds head.rounded
 have claims := (NNV_FinishClaims.returned a.prefix_ env head.claims head.claimed).2
 have terminalOriginal : LIB_VLib.terminalQm31Value
  (a.public_,head.claims,head.rounds.2.1,V.origChallenges a.challenges) env = .ok tail.terminal := by
  have mapped := tail.terminal_ok
  cases h : LIB_VLib.terminalQm31Value
   (a.public_,head.claims,head.rounds.2.1,V.origChallenges a.challenges) env with
  | error e => rw [h] at mapped;cases mapped
  | ok q =>
   rw [h] at mapped
   exact congrArg Except.ok (Except.ok.inj mapped)
 have claimsAt : B.claims (prefixRaw a.prefix_) = .ok (.Ok (claimsRaw head.claims)) := claims
 have terminal := NNV_FinishTerminal.returned _ env tail.terminal terminalOriginal
 have record25 := NNV_FinishRecord.returned a.prefix_ 25#u8 tail.rec25 tail.record25
 have extra := NNX_FinishDecodePort.returned tail.rec25 87#usize tail.extra
  (NNV_FinishDecodeDomains.extra a.prefix_ tail.rec25 tail.record25) tail.decoded25
 have same25 : tail.rec25' = tail.rec25 := Except.ok.inj (tail.record25'.symm.trans tail.record25)
 have circle0 := NNV_FinishNativePorts.circle B head.rounds.2.2 tail.rec25' env tail.c0.1 tail.c0.2 tail.circle0
 rw [same25] at circle0
 have record26 := NNV_FinishRecord.returned a.prefix_ 26#u8 tail.rec26 tail.record26
 have before := NNX_FinishDecodePort.returned tail.rec26 0#usize tail.beforeZ1
  (NNV_FinishDecodeDomains.before a.prefix_ tail.rec26 tail.record26) tail.decoded26
 have same26 : tail.rec26' = tail.rec26 := Except.ok.inj (tail.record26'.symm.trans tail.record26)
 have circle1 := NNV_FinishNativePorts.circle B tail.c0.2 tail.rec26' env tail.c1.1 tail.c1.2 tail.circle1
 rw [same26] at circle1
 obtain ⟨payload,payloadCall,payloadBytes⟩ := NNX_FinishPayload.source a.prefix_ 2#u8 tail.payload tail.payload_ok
 have converted : TX1_136.toB32 (LIB_Carriers.bytes payload) = some tail.root1 := by
  rw [payloadBytes];exact tail.root_ok
 have rootCall := NNX_RootCopy.source payload tail.root1 converted
 have gate := congrArg LIB_VScalarCarriers.toRaw tail.gate
 have g16 := NNX_C1Gather.source (LIB_VCode.digest env) head.claims
 have g10 := NNX_Mask10.source (LIB_VCode.digest env) head.claims
 unfold FinishModel.finish
 rw [rounds]
 simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,VerifyPrefix.mark]
 rw [claimsAt]
 simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 rw [terminal]
 simp only [core.result.Result.map_err,FinishModel.closureFn11,FinishModel.closureFn10,
  bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,VerifyPrefix.mark]
 rw [g16,g10]
 simp only [bind_tc_ok]
 rw [NNX_ClaimPorts.row,NNX_ClaimPorts.at27]
 simp only [bind_tc_ok]
 rw [LIB_VField.mask_exact,record25,extra]
 simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 rw [LIB_VField.qmul_exact,LIB_VField.qadd_exact,NNX_Masked.extra,LIB_VField.qadd_exact]
 simp only [bind_tc_ok]
 rw [←gate,NNX_Comparisons.qm_ne]
 simp only [bind_tc_ok,Bool.false_eq_true,if_false,VerifyPrefix.mark]
 rw [LIB_VRecords.state_exact,circle0,record26,before,circle1]
 simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,VerifyPrefix.mark]
 rw [NNX_Comparisons.point _ _ tail.distinct]
 simp only [bind_tc_ok,Bool.false_eq_true,if_false]
 rw [payloadCall,rootCall]
 simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 rw [tail.semantic]
 simp only [LIBC_PreparedCarriers.verified,LIB_Prepared.types,NNX_RootCopy.key]
 rfl
#print axioms source
end AspisR1.NNX_FinishSource
end
