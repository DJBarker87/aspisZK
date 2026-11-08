import PV_LIB_A_AllocatorProvenance
set_option autoImplicit false
namespace PV_LIB_A_ValueDestruct9
open PV_STX2_Syntax PV_STX2_Store PV_LIB_A_TypedDestruct PV_LIB_A_CellSetBegin

/-- Retain the exact emitted witness. Only unresolved UntrackedDestruct gets
value-based Arc allocator recovery; explicit impl arguments always win. -/
def resolve {W : Type} (C : Carrier W Data) (ty witness value : Data) : Option Resolution :=
  match PV_LIB_A_ExactDestructMethods.resolve ty witness with
  | some d => some d
  | none => do
    let kind ← member "kind" witness
    let builtin ← member "BuiltinOrAuto" kind
    let .atom "UntrackedDestruct" ← member "builtin_data" builtin | none
    PV_LIB_A_AllocatorProvenance.arcGlue C ty value

/-- A raw Fun pointer is retained verbatim; a Trait Destruct0 keeps its self
and witness. Runtime values are only used to recover the missing allocator. -/
def token {W : Type} (C : Carrier W Data) (fn value : Data) : Option Resolution := do
  let normalized ← PV_LIB_A_GenericDropBinding.normalized fn
  let ptr ← member "Regular" normalized
  let kind ← member "kind" ptr
  match member "Fun" kind with
  | some _ => pure (.call ptr)
  | none =>
    let .array [witness,.number 0] ← member "Trait" kind | none
    let trait ← member "trait_decl_ref" witness
    let binder ← member "skip_binder" trait
    let .number 5 ← member "id" binder | none
    let raw ← member "generics" binder
    let g ← generics raw
    match g.types with
    | [ty] => resolve C ty witness value
    | _ => none

theorem inherited {W : Type} (C : Carrier W Data) (ty witness value : Data)
    (d : Resolution) (bound : PV_LIB_A_ExactDestructMethods.resolve ty witness = some d) :
    resolve C ty witness value = some d := by simp only [resolve,bound]

theorem untracked_arc {W : Type} (base : Carrier W Data) (payload ptr phantom : Data) :
    resolve (PV_THR2_KeyValues.carrier base) (PV_LIB_A_TypedBindingFacts.arcType payload)
      (PV_LIB_A_TypedBindingFacts.untracked (PV_LIB_A_TypedBindingFacts.arcType payload))
      (PV_LIB_A_AllocatorProvenance.constructed payload ptr phantom) =
        some (.call (fnPtr 405 ⟨[.atom "Erased"],[payload,PV_LIB_A_AllocatorProvenance.globalType],[],[]⟩)) := by
  change PV_LIB_A_AllocatorProvenance.arcGlue (PV_THR2_KeyValues.carrier base)
    (PV_LIB_A_TypedBindingFacts.arcType payload)
    (PV_LIB_A_AllocatorProvenance.constructed payload ptr phantom) = _
  exact PV_LIB_A_AllocatorProvenance.source_glue base payload ptr phantom

#print axioms resolve
#print axioms token
#print axioms inherited
#print axioms untracked_arc
end PV_LIB_A_ValueDestruct9
