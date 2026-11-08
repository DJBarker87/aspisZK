import NNG_ModelHead136
import NNG_LegacyDigest136
import LIBC_PreparedDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SemanticAt094
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Internal producer provenance with the SAME supplied Env digest retained.
This is stronger than the existential hashv forgotten by the CLOSED179 domain;
it is a derived source fact, never a new RowSpec input clause. -/
def SemanticAt (env : RSL.Env) (sem : r1_semantic.Verified Unit) : Prop :=
 ∃ (B : FinishModel.Boundaries) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pre : r1_wire.Prefix) (before : r1_wire.SemanticTranscript Unit) (ch : r1_wire.Challenges)
 (obs : Option (RPz7_PhaseIso.Phase → Result Unit)),
 FinishModel.finish AspisS1ExtractedRoundChildren.children
  {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
  (LIBC_PreparedLog.digest env) pub pre before ch obs=ok (.Ok sem)

theorem finish {W : Type} (env : RSL.Env) (s : NNG_Emitted.Parent Unit W)
 (out : NNG_verify_finish.r1_semantic.Verified Unit)
 (native : NNG_Emitted.emitted (NNG_ConcreteCalls136.calls env) s=.ok (.Ok out))
 (digestEq : s.digest=NNG_LIBDigest.digest env) (reserved : env.reservation=true) :
 SemanticAt env (NNG_Transport.toT11 out) := by
 have model := NNG_ModelSuccess136.finish env s out native
 have config : {NNG_LegacyConfig136.boundaries env with
  claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}=
  NNG_LegacyConfig136.boundaries env := by
  unfold NNG_LegacyConfig136.boundaries
  simp only [NNG_LIBClaims.reservation,reserved,if_true]
 have digest : NNG_Install.digest s.digest=LIBC_PreparedLog.digest env := by
  rw [digestEq]
  rfl
 refine ⟨NNG_LegacyConfig136.boundaries env,NNG_Transport.toT9 s.publicValue,
  NNG_Transport.toT12 s.prefixValue,NNG_Transport.toT10 s.transcript,NNG_Transport.toT3 s.challenges,none,?_⟩
 rw [config,←digest]
 exact model
#print axioms finish
end AspisR1.NNG_SemanticAt094
