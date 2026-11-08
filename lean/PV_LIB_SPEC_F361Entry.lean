import PV_FN_THREAD_f361NameEntryValidity
import PV_FN_THREAD_f361ScopeEntryValidity
import PV_STX2_LiveNumbering
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F361Entry
open PV_FN_THREAD_f361
open PV_STX2_SliceMachine
/-- Literal package predicates, retaining the provider's opaque String codec
and Option constructors rather than a consumer-selected representation. -/
abbrev Representation := PV_THR2_LibrarySemantics_ThreadNew213.Representation
abbrev PackagePre := PV_FN_THREAD_f361.Pre
abbrev PackagePost := PV_FN_THREAD_f361.Post
/-- Thread25 over the actual active entry and every suspended intrinsic config.
It constrains no future configuration or cross-callee counter equality. -/
def Numbered (x : Input) : Prop :=
  (∀ c, (entry x).current.status = .running c → PV_STX2_LiveNumbering.Numbered c) ∧
    ∀ c ∈ (entry x).suspended, PV_STX2_LiveNumbering.Numbered c
/-- Compiled ENTRY COMPONENT of the frozen contract, not all common clauses or
MachineSpec/Post. Full allocation/reference validity and resource bindings
still have to be elaborated; this definition is not counted as a full Pre. -/
def EntryComponent (R : Representation) (x : Input) : Prop :=
  PV_FN_THREAD_f361NameEntryValidity.Pre' R x ∧
    PV_FN_THREAD_f361ScopeEntryValidity.Shape x.scope ∧ Numbered x
/-- Explicit comparison against the actual pinned package Pre, not a name or
prose comparison. No implication to the full new Post is asserted. -/
theorem before_after (R : Representation) (x : Input) :
    EntryComponent R x ↔
      PackagePre x ∧ PV_FN_THREAD_f361NameEntryValidity.EntryName R x ∧
        PV_FN_THREAD_f361ScopeEntryValidity.Shape x.scope ∧ Numbered x := by
  constructor
  · rintro ⟨⟨old,label⟩,scope,numbered⟩
    exact ⟨old,label,scope,numbered⟩
  · rintro ⟨old,label,scope,numbered⟩
    exact ⟨⟨old,label⟩,scope,numbered⟩
theorem implies_package (R : Representation) (x : Input)
    (pre : EntryComponent R x) : PackagePre x := pre.1.1
/-- Compatibility with the provider's already-stated typed-name refinement. -/
theorem implies_name (R : Representation) (x : Input)
    (pre : EntryComponent R x) : PV_FN_THREAD_f361NameEntryValidity.Pre' R x := pre.1
/-- Compatibility with the provider's already-stated scope refinement. -/
theorem implies_scope (R : Representation) (x : Input)
    (pre : EntryComponent R x) : PV_FN_THREAD_f361ScopeEntryValidity.ScopeEntry x :=
  ⟨pre.1.1,pre.2.1⟩
/-- The preserved package statement is merely aliased, never claimed proved. -/
theorem post_literal (x : Input) : PackagePost x ↔ PV_FN_THREAD_f361.Post x := Iff.rfl
#print axioms Representation
#print axioms PackagePre
#print axioms PackagePost
#print axioms Numbered
#print axioms EntryComponent
#print axioms before_after
#print axioms implies_package
#print axioms implies_name
#print axioms implies_scope
#print axioms post_literal
end PV_LIB_SPEC_F361Entry
