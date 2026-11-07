import NNH_064Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064PrefixCoverage
open Aeneas Aeneas.Std VTop_Stages
/-- No path is discarded: None means exactly that the actual parser and
resume succeeded, exposing the still-required continuation at the same pair. -/
theorem unfinished_iff (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8) :
 NNH_064Prefix.run env r pub proof ck=none ↔
 ∃ v p a, NLE_ParseInstall.parse proof=.ok (.Ok v) ∧
 NNH_064ResumeError.reply env r pub proof ck=.ok (.Ok (p,a)) := by
 constructor
 · exact NNH_064Prefix.remaining env r pub proof ck
 · rintro ⟨v,p,a,parsed,resumed⟩
   simp only [NNH_064Prefix.run,parsed,resumed]

/-- Full input-space prefix classification. The right alternative is an
unimplemented continuation, not an abort, attack exclusion or new hypothesis. -/
theorem classify {Ambient : Type} (env : RSL.Env) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (world : NLM_PacketTypes.World Ambient) :
 (∃ o, NNH_064Prefix.run env r pub proof ck=some o ∧
  NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () world
   (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env o) ∨
 (∃ v p a, NLE_ParseInstall.parse proof=.ok (.Ok v) ∧
  NNH_064ResumeError.reply env r pub proof ck=.ok (.Ok (p,a))) := by
 cases endpoint : NNH_064Prefix.run env r pub proof ck with
 | none => exact Or.inr ((unfinished_iff env r pub proof ck).mp endpoint)
 | some o => exact Or.inl ⟨o,rfl,NNH_064Prefix.weak env r pub proof ck world o endpoint⟩
#print axioms unfinished_iff
#print axioms classify
end AspisR1.NNH_064PrefixCoverage
