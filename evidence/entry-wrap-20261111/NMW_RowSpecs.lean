import NMW_FullDispatch
set_option autoImplicit false
noncomputable section
namespace NMW_RowSpecs
open Aeneas Aeneas.Std AspisR1 NMW_Outcome NMW_FullDispatch
/-- Full-strength child packet at the frozen wrapper signature. Equality is
of the COMPLETE returned Result/world/effects OR stop reason/ordered prefix.
The native and model functions are total interpreters; there is no free
relation which can be chosen empty, and no post-world on stopped executions.
This is an intermediate interface, never a closed-row root premise. -/
def RowSpec {A W E : Type} (native model : Child A W E)
 (domain : Args A → W → Prop) : Prop :=
 ∀ args before, domain args before → native args before = model args before
abbrev RowSpec_344 {A W E : Type} := @RowSpec A W E
abbrev RowSpec_240 {A W E : Type} := @RowSpec A W E
/-- The child domain is established on the parent's own original inputs.
No child reply, success, endpoint, or global/headline predicate is allowed. -/
def CallerClause {A W : Type} (route : Slice U8 → Prop)
 (parentDomain childDomain : Args A → W → Prop) : Prop :=
 ∀ args before, parentDomain args before → route args.data → childDomain args before
/-- Own-input release domain for the TWO occurrences of process. -/
def Release (data : Slice U8) : Prop :=
 Hiq_ReleaseRoute.stage1 data ∨ Hiq_ReleaseRoute.asq8 data
/-- Complete wrapper claims, not only returned-value projections. All source
error variants, account/token/return-data/ambient fields and events survive. -/
def ProcessSpec {A W E : Type} (native model : Children A W E)
 (domain : Args A → W → Prop) : Prop :=
 ∀ args before, domain args before → Release args.data →
 process native args before = process model args before

def EntrySpec {A W E : Type} (native model : Children A W E)
 (domain : Args A → W → Prop) : Prop :=
 ∀ args before, domain args before → entry native args before = entry model args before
#print RowSpec
#print CallerClause
#print ProcessSpec
#print EntrySpec
end NMW_RowSpecs
end
