import NNH_064Execute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064Observe
open Aeneas Aeneas.Std VTop_Stages NLW_Full064 NNH_064Execute

theorem trace_source (env : RSL.Env) (pub proof ck : Slice U8) :
 NNC_ObservedWeak.TraceOf (outcome env pub proof ck) (trace env pub proof ck) := by
 cases parsed : NLE_ParseInstall.parse proof with
 | fail e => simp only [outcome,trace,parsed,NNC_ObservedWeak.TraceOf]
 | div => simp only [outcome,trace,parsed,NNC_ObservedWeak.TraceOf]
 | ok reply => cases reply with
   | Err e => simp only [outcome,trace,parsed,NNC_ObservedWeak.TraceOf]
   | Ok v =>
     simp only [outcome,trace,parsed,NNC_ObservedWeak.TraceOf,common,NNC_RecordTrace.FromEnd]
     exact NNH_064CommonTrace.source env pub proof ck

theorem observed {Ambient : Type} (env : RSL.Env) (pub proof ck : Slice U8)
 (world : NLM_PacketTypes.World Ambient) (len : proof.val.length=57607) :
 NNC_ObservedWeak.Observed (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩ (observation env pub proof ck) := by
 obtain ⟨events,native⟩ := NNH_064Execute.native env pub proof ck world len
 exact ⟨outcome env pub proof ck,events,trace env pub proof ck,native,
  trace_source env pub proof ck,rfl⟩

theorem weak {Ambient : Type} (env : RSL.Env) (pub proof ck : Slice U8)
 (world : NLM_PacketTypes.World Ambient) (len : proof.val.length=57607) :
 NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () world
  (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env
  (observation env pub proof ck) :=
 ⟨pub,proof,ck,rfl,rfl,rfl,observed env pub proof ck world len⟩

theorem bound (env : RSL.Env) (pub proof ck : Slice U8) :
 LIBB_ObservationFold.Bound064 env pub proof ck (outcome env pub proof ck) := by
 unfold outcome
 cases parsed : NLE_ParseInstall.parse proof with
 | fail e => exact True.intro
 | div => exact True.intro
 | ok reply => cases reply with
   | Err e => exact True.intro
   | Ok v => exact NNH_064CommonTrace.bound env pub proof ck _ (fun _ h=>h)

/-- Canonical fold at the unchanged Dom064, using the SAME constructed
execution and its exact computed trace. No library observation is selected. -/
theorem canonical {Ambient : Type} (env : RSL.Env) (pub proof ck : Slice U8)
 (world : NLM_PacketTypes.World Ambient)
 (domain : RSL.TX2_241.Dom064 NNH_Libraries.V0
  (LIB_Carriers.bytes pub,LIB_Carriers.bytes proof,LIB_Carriers.bytes ck)) :
 NNH_Libraries.V0.tx2auth (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof)
  (LIB_Carriers.bytes ck) env (observation env pub proof ck) := by
 have len : proof.val.length=57607 := by
  simpa only [LIB_Carriers.bytes,List.length_map,RSL.PROOF_BYTES] using domain.1
 obtain ⟨events,native⟩ := NNH_064Execute.native env pub proof ck world len
 exact (LIBB_Tx2Auth.native env pub proof ck world domain _ events native
  (bound env pub proof ck) (trace env pub proof ck) (trace_source env pub proof ck)).2.2
#print axioms trace_source
#print axioms observed
#print axioms weak
#print axioms bound
#print axioms canonical
end AspisR1.NNH_064Observe
