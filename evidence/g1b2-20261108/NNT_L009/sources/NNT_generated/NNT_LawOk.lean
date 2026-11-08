import NNT_Field
import NNS_064Value
import NNH_064Execute
set_option autoImplicit false
noncomputable section
namespace NNT_LawOk
open Aeneas Aeneas.Std AspisR1 VTop_Stages NLW_Full064

theorem native_of_ok {Ambient : Type} (env : RSL.Env) (pub proof ck : Slice U8)
 (len : proof.val.length = 57607) (world : NLM_PacketTypes.World Ambient)
 (o : RSL.Obs (Except verifier.Error Unit))
 (h : LIBB_ObservationModel.law pub proof ck env o) (ok : o.exit = .ret (.ok ())) :
 ∃ records events, NMN_064.Native (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩
  (.common (.resolved (.ok (.Ok ())) records)) events := by
 have accepted : NNH_064Execute.outcome env pub proof ck =
   .common (.resolved (.ok (.Ok ())) (NNH_064CommonRecords.records env pub proof ck)) := by
  unfold LIBB_ObservationModel.law at h
  cases parsed : NLE_ParseInstall.parse proof with
  | fail e =>
    rw [parsed] at h
    have ex := (congrArg RSL.Obs.exit h).symm.trans ok
    rw [LIBB_ObservationModel.observation_exit,LIBB_Tx2EnvCode.code,parsed] at ex
    cases ex
  | div =>
    rw [parsed] at h
    have ex := (congrArg RSL.Obs.exit h).symm.trans ok
    rw [LIBB_ObservationModel.observation_exit,LIBB_Tx2EnvCode.code,parsed] at ex
    cases ex
  | ok reply => cases reply with
    | Err e =>
      rw [parsed] at h
      have ex := (congrArg RSL.Obs.exit h).symm.trans ok
      rw [LIBB_ObservationModel.observation_exit,LIBB_Tx2EnvCode.code,parsed] at ex
      cases ex
    | Ok v =>
      rw [parsed] at h
      rcases h with done | ⟨before,pr,p,folded,reply,suffix,prior,inside,_,_,_,eq⟩
      · have exitEq := done.1.symm.trans ok
        have value : LIBB_Tx2EnvCode.common env pub proof ck = .ok (.Ok ()) := by
          cases valueEq : LIBB_Tx2EnvCode.common env pub proof ck with
          | fail e => rw [valueEq] at exitEq; cases exitEq
          | div => rw [valueEq] at exitEq; cases exitEq
          | ok reply => cases reply with
            | Err e => rw [valueEq] at exitEq; cases exitEq
            | Ok u => cases u; rfl
        simp only [NNH_064Execute.outcome,parsed,NNH_064Execute.common,
          NNS_064Value.common_result,value]
      · rw [eq] at ok
        cases ok
 obtain ⟨events,run⟩ := NNH_064Execute.native env pub proof ck world len
 exact ⟨_,events,accepted ▸ run⟩
#print axioms native_of_ok
end NNT_LawOk
