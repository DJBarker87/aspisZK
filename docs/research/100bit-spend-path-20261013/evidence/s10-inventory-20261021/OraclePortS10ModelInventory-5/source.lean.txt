import OraclePortJoinSplitCore
import OraclePortFrozenOrderDecision

/-! S10 at the MODEL stage boundary. This is an actual Covered inhabitant and
an exact dV_frozen decomposition, NOT a frozen Rust declaration/call graph.
The opaque stage implementations below still require source refinements.
The source inventory's unresolved/error/inline frontiers cannot be discharged
by this finite model list. S10 and ordered-caller composition are not stages. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortS10ModelInventory
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredExperimentC4 OraclePortJoinSplit
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
attribute [local instance] Classical.propDecidable

abbrev Queries := Fin 22 → Fin 262144

def guardSite : Site := ⟨.s2, "AspisR1.OraclePortAdmission.Guard"⟩
def parserSite : Site := ⟨.parserCodec, "AspisR1.OraclePortStoredParserC4.parseReached"⟩
def querySite : Site := ⟨.s1, "AspisR1.OraclePortBatchDraft.queries"⟩
def merkleSite : Site := ⟨.multiproof, "AspisR1.OraclePortFrozenOrder.slotPrograms/short"⟩
def arithmeticSite : Site := ⟨.s5, "AspisR1.OraclePortStoredDecisionDraftC4.arithmetic"⟩

def inventory : List Site := [guardSite, parserSite, querySite, merkleSite, arithmeticSite]

def Args (owner : Cone) : Type := match owner with
  | .s2 | .s1 => ErasedPrefix
  | .parserCodec => Bytes × ErasedPrefix
  | .multiproof => Parsed × Queries
  | .s5 => Parsed × Queries × ErasedPrefix
  | _ => Unit

def Value (owner : Cone) : Type := match owner with
  | .parserCodec => Option Parsed
  | .s1 => Option Queries
  | _ => Bool

abbrev signature : Signature := ⟨fun site => Args site.owner, fun site => Value site.owner⟩

/-- These are the actual model bodies, not free callback hypotheses. -/
def modelCone (owner : Cone) : Args owner → Program Bytes State (Value owner) :=
  match owner with
  | .s2 => fun tr => .done (decide (OraclePortAdmission.Guard tr))
  | .parserCodec => fun args => .done (OraclePortStoredParserC4.parseReached args.1 args.2)
  | .s1 => fun tr => .done (queries tr)
  | .multiproof => fun args => OraclePortShortCircuit.short
      (OraclePortFrozenOrder.slotPrograms args.1 args.2 slots)
  | .s5 => fun args => .done
      (OraclePortStoredDecisionDraftC4.arithmetic args.1 args.2.1 args.2.2)
  | .s3 | .s4 | .s6 | .s7 | .s8 | .s9 | .checkpointAbi | .poolCaller =>
      fun _ => .done false

def model : Implementation signature := fun site => modelCone site.owner

def tree (stored : Bytes) (tr : ErasedPrefix) : Calls signature Bool :=
  .invoke guardSite tr fun guard =>
    if guard = true then
      .invoke parserSite (stored, tr) fun parsed =>
      .invoke querySite tr fun sampled =>
        match parsed, sampled with
        | some p, some q =>
          .invoke merkleSite (p,q) fun ok =>
          .invoke arithmeticSite (p,q,tr) fun arithmetic => .done (ok && arithmetic)
        | _, _ => .done false
    else .done false

/-- Every value continuation is covered, including rejection and arbitrary
outputs of the stage interface, not only outputs realized by `model`. -/
theorem covered (stored : Bytes) (tr : ErasedPrefix) : Covered inventory (tree stored tr) := by
  change guardSite ∈ inventory ∧ _
  refine ⟨by simp [inventory], ?_⟩
  intro guard
  cases guard with
  | false => simp [guardSite, signature, Value, Covered]
  | true =>
    simp only [guardSite, signature, Value]
    change parserSite ∈ inventory ∧ _
    refine ⟨by simp [inventory], ?_⟩
    intro parsed
    change querySite ∈ inventory ∧ _
    refine ⟨by simp [inventory], ?_⟩
    intro sampled
    cases parsed <;> cases sampled
    · trivial
    · trivial
    · trivial
    · change merkleSite ∈ inventory ∧ _
      refine ⟨by simp [inventory], ?_⟩
      intro ok
      change arithmeticSite ∈ inventory ∧ _
      exact ⟨by simp [inventory], fun _ => trivial⟩

/-- Exact full-program model-stage equality, preserving frozen slot read
order and early errors inside `short`; no global Padding stage is inserted. -/
theorem interpret_eq_frozen (stored : Bytes) (tr : ErasedPrefix) (m : ErasedMessage) :
    interpret model (tree stored tr) = OraclePortFrozenOrder.dV_frozen stored tr m := by
  by_cases hg : OraclePortAdmission.Guard tr
  · cases hp : OraclePortStoredParserC4.parseReached stored tr <;>
      cases hq : queries tr <;>
      simp [tree, interpret, model, modelCone, signature, Args, Value,
        guardSite, parserSite, querySite, merkleSite, arithmeticSite,
        AspisV8R19.OracleProgramOps.bind, OraclePortFrozenOrder.dV_frozen, hg, hp, hq]
  · simp [tree, interpret, model, modelCone, signature, Args, Value,
      guardSite, AspisV8R19.OracleProgramOps.bind, OraclePortFrozenOrder.dV_frozen, hg]

/-- The independent source obligation needed to upgrade the model inventory.
`sourceTree` must be a real frozen driver tree, including entrypoint, Pool,
checkpoint and all nested source declarations. This definition does not
assert that the diagnostic JSON graph supplies such a tree. -/
def SourceInventoryCompleteness {σ : Signature} (recorded : List Site)
    (sourceTree : Input → Calls σ Bool) : Prop := S10Join recorded sourceTree

#print axioms covered
#print axioms interpret_eq_frozen
end AspisR1.OraclePortS10ModelInventory
end
