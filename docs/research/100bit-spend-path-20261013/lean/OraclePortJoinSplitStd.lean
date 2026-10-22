import OraclePortJoinSplitCore

/-! Std/allocation extension of the substitution interface. No frozen implementation or caller tree is
constructed here. The source and model must share the *ordered* caller tree,
including rejection branches, repeated calls, all call arguments and reads.
S10 is coverage of its call sites, not an executable verifier stage. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortJoinSplitStd
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortStoredConsumerC7 OraclePortRuntimeBindingC7

/-- Additive owner extension: the thirteen existing cone obligations remain. -/
inductive Cone where
  | owned (cone : OraclePortJoinSplit.Cone)
  | trustedStd
  deriving DecidableEq

structure Site where
  owner : Cone
  declaration : String
  deriving DecidableEq

/-- Arguments include the complete pre-state; values include the complete
post-state and ordinary Rust rejection. Hiding mutable state loses the join.
The instantiator must fix these carriers from the adopted source extraction. -/
structure Signature where
  Args : Site → Type
  Value : Site → Type

abbrev Implementation (σ : Signature) :=
  (site : Site) → σ.Args site → Program Bytes State (σ.Value site)

inductive Calls (σ : Signature) (α : Type) where
  | done (value : α)
  | invoke (site : Site) (args : σ.Args site) (next : σ.Value site → Calls σ α)
  | oracle (address : Bytes) (next : State → Calls σ α)

def interpret {σ : Signature} {α : Type} (impl : Implementation σ) :
    Calls σ α → Program Bytes State α
  | .done value => .done value
  | .invoke site args next => bind (impl site args) fun value => interpret impl (next value)
  | .oracle address next => .ask address fun value => interpret impl (next value)

/-- Total full-program equality: no acceptance, successful-call, canonicality
or oracle-world antecedent. Rejected inputs and read order are included. -/
def ConeJoin {σ : Signature} (source model : Implementation σ) (cone : Cone) : Prop :=
  ∀ site, site.owner = cone → ∀ args, source site args = model site args

structure PerConeJoins {σ : Signature} (source model : Implementation σ) : Prop where
  owned : ∀ c, ConeJoin source model (.owned c)
  trustedStd : ConeJoin source model .trustedStd

/-- S10 must cover *all* return continuations, including rejection paths.
Membership alone is not source pin validation: that remains P6/S10 evidence. -/
def Covered {σ : Signature} {α : Type} (inventory : List Site) : Calls σ α → Prop
  | .done _ => True
  | .invoke site _ next => site ∈ inventory ∧ ∀ value, Covered inventory (next value)
  | .oracle _ next => ∀ value, Covered inventory (next value)

def S10Join {σ : Signature} (inventory : List Site) (tree : Input → Calls σ Bool) : Prop :=
  ∀ i, Covered inventory (tree i)

theorem perCone_at {σ : Signature} {source model : Implementation σ}
    (joins : PerConeJoins source model) (site : Site) (args : σ.Args site) :
    source site args = model site args := by
  cases h : site.owner with
  | owned c => exact joins.owned c site h args
  | trustedStd => exact joins.trustedStd site h args

/-- Structural composition: branch-dependent continuations are preserved;
there is no permutation or acceptance-only extensionality step. -/
theorem interpret_eq {σ : Signature} {α : Type} {source model : Implementation σ}
    (joins : PerConeJoins source model) (tree : Calls σ α) :
    interpret source tree = interpret model tree := by
  induction tree with
  | done value => rfl
  | invoke site args next ih =>
      simp only [interpret, perCone_at joins site args]
      exact congrArg (bind (model site args)) (funext ih)
  | oracle address next ih =>
      exact congrArg (Program.ask address) (funext ih)

/-- These are the two independent caller proofs still owed: decompose the
actual frozen execution, and identify the fully substituted model with dV.
This is not a proof that a tree or either identity exists for frozen Rust. -/
structure CompositionOrderingJoin {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool) : Prop where
  source_order : ∀ i, rust i = interpret source (tree i)
  model_order : ∀ i, interpret model (tree i) = verifier D dV i

theorem executionJoin_of_cones {σ : Signature} (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (source model : Implementation σ) (tree : Input → Calls σ Bool)
    (inventory : List Site) (h_cones : PerConeJoins source model)
    (_h_S10 : S10Join inventory tree)
    (h_order : CompositionOrderingJoin D rust source model tree) : ExecutionJoin D rust := by
  intro i
  exact (h_order.source_order i).trans ((interpret_eq h_cones (tree i)).trans
    (h_order.model_order i))

#print axioms perCone_at
#print axioms interpret_eq
#print axioms executionJoin_of_cones
end AspisR1.OraclePortJoinSplitStd
end
