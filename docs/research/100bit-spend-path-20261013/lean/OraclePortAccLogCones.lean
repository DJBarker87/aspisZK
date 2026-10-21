import OraclePortAccLogCore
import OraclePortJoinSplitCore

/-! Ordered observations compose through value-dependent calls. Accepted-only
Bool observations compose through the outer short-circuit conjunction. This
packet supplies rules, not inhabitants for the frozen per-cone obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortAccLog
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortJoinSplit

/-- Exact logs and intermediate result/state, including ordinary rejection. -/
def ValueJoin {α : Type} (source model : Program Bytes State α) : Prop :=
  ∀ H, eval H source = eval H model

def ConeLogJoin {σ : Signature} (source model : Implementation σ) (cone : Cone) : Prop :=
  ∀ site, site.owner = cone → ∀ args, ValueJoin (source site args) (model site args)

theorem coneJoin_logJoin {σ : Signature} (source model : Implementation σ) (cone : Cone)
    (h : ConeJoin source model cone) : ConeLogJoin source model cone := by
  intro site hs args H
  rw [h site hs args]

theorem bind_valueJoin {α β : Type} (p q : Program Bytes State α)
    (f g : α → Program Bytes State β) (hp : ValueJoin p q)
    (hf : ∀ a, ValueJoin (f a) (g a)) : ValueJoin (bind p f) (bind q g) := by
  intro H
  simp only [eval_bind,hp H,hf _ H]

theorem interpret_valueJoin {σ : Signature} {α : Type}
    (source model : Implementation σ)
    (h : ∀ cone, ConeLogJoin source model cone) (tree : Calls σ α) :
    ValueJoin (interpret source tree) (interpret model tree) := by
  induction tree with
  | done a => intro H; rfl
  | invoke site args next ih =>
      exact bind_valueJoin _ _ _ _ (h site.owner site rfl args) ih
  | oracle address next ih =>
      intro H
      simp only [interpret,eval,ih (H address) H]

/-- The continuation-sensitive raw whole-decision lift. All caller/source
and S10 inventory obligations remain explicit. No read permutation is used. -/
theorem acceptedVerifierJoin_of_cones {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (h_cones : ∀ cone, ConeLogJoin source model cone)
    (inventory : List Site) (_h_S10 : S10Join inventory tree)
    (h_source : ∀ i, rust i = interpret source (tree i))
    (h_model : ∀ i, interpret model (tree i) = verifier D OraclePortShortCircuit.outerDecision i) :
    AcceptedVerifierJoin rust (verifier D OraclePortShortCircuit.outerDecision) := by
  intro H i _
  rw [h_source i,← h_model i]
  exact interpret_valueJoin source model h_cones (tree i) H

/-- Accepted-only equality is sufficient at the AND's Bool child boundary.
It is not substituted for ValueJoin at arbitrary value-returning calls. -/
theorem short_accepted_eq (source model : List (Program Bytes State Bool))
    (h : List.Forall₂ (fun p q => ∀ H, (eval H p).2 = true → eval H p = eval H q) source model)
    (H : Bytes → State) (ha : (eval H (OraclePortShortCircuit.short source)).2 = true) :
    eval H (OraclePortShortCircuit.short source) = eval H (OraclePortShortCircuit.short model) := by
  induction h with
  | nil => rfl
  | @cons p q ps qs hp ht ih =>
      cases hv : (eval H p).2
      · simp [OraclePortShortCircuit.short,eval_bind,hv,eval] at ha
      · have tail : (eval H (OraclePortShortCircuit.short ps)).2 = true := by
          simpa only [OraclePortShortCircuit.short,eval_bind,hv,if_true] using ha
        have eq := hp H hv
        have hq : (eval H q).2 = true := (congrArg Prod.snd eq).symm.trans hv
        simp only [OraclePortShortCircuit.short,eval_bind,hv,hq,if_true,
          congrArg Prod.fst eq,ih tail]

/-- Both annotation passes are lifted when the source verdict is stable under
proof enrichment. Stability is a separate sufficient obligation, not an
extra premise hidden in the headline. -/
theorem acceptedRunJoin_of_cones {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (h_cones : ∀ cone, ConeLogJoin source model cone)
    (inventory : List Site) (h_S10 : S10Join inventory tree)
    (h_source : ∀ i, rust i = interpret source (tree i))
    (h_model : ∀ i, interpret model (tree i) = verifier D OraclePortShortCircuit.outerDecision i)
    (stable : ∀ w i H, (eval H (rust (enrich w i))).2 = (eval H (rust i)).2) :
    AcceptedRunJoin D rust :=
  acceptedRunJoin_of_stable D rust
    (acceptedVerifierJoin_of_cones D rust source model tree h_cones inventory h_S10 h_source h_model)
    stable

#print axioms coneJoin_logJoin
#print axioms bind_valueJoin
#print axioms interpret_valueJoin
#print axioms acceptedVerifierJoin_of_cones
#print axioms short_accepted_eq
#print axioms acceptedRunJoin_of_cones
end AspisR1.OraclePortAccLog
end
