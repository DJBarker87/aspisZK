import R1Z.PV_RunJoin_BodyProjection
import R1Z.PV_RunJoin_GenericSourceCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CallerProjection
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open ProverCommitSemanticTransport26 PV_RunJoin_BindCongruence
variable [ExternalTypes] [ExternalFuns]

theorem caller (parametric : PV_RunJoin_StoreContinuationResidual.MapErrParametric)
    {S T : Type} (project : S → T)
    (left : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (right : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)
    (pub : Pub) (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (secret : Secret) (s : S)
    (callback : ∀ statement nonce,
      mapR (fun out => (out.1,project out.2)) (left.«reserve» s statement nonce) =
        right.«reserve» (project s) statement nonce) :
    mapR (fun out => (out.1,project out.2))
      (PV_RunJoin_GenericSourceCaller.caller left pub compiled variant hash secret s) =
    PV_RunJoin_GenericSourceCaller.caller right pub compiled variant hash secret (project s) := by
  unfold PV_RunJoin_GenericSourceCaller.caller
  simp only [map_bind,map_ok]
  repeat' first
    | exact PV_RunJoin_BodyProjection.body parametric project left right pub compiled
        variant hash _ _ secret s (callback _ _)
    | rfl
    | apply bind_same
      intro value
      try (change (_ × _) at value; rcases value with ⟨value1,value2⟩)
      try simp only [Aeneas.Std.uncurry,map_bind,map_ok,
        PV_RunJoin_PairElimination.cases_pair,bind_tc_ok]
    | split <;> try simp only [Aeneas.Std.uncurry,map_bind,map_ok,bind_tc_ok]

#print axioms caller
end R1Z.PV_RunJoin_CallerProjection
