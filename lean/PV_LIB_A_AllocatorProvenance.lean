import PV_LIB_A_TypedBody218
import PV_LIB_A_TypedBody315
import PV_LIB_A_TypedBindingFacts
import PV_THR2_KeyValues
set_option autoImplicit false
namespace PV_LIB_A_AllocatorProvenance
open PV_STX2_Syntax PV_LIB_A_TypedDestruct PV_LIB_A_CellSetBegin

/-- Taken from actual constructor218/9167, not from erased Arc<T>.
The default is confirmed by 1.94.1 from_inner and the typed315 call. -/
def globalKind : Data := match PV_LIB_A_TypedBody218.node4 [] with
  | .leaf (.aggregateMove _ _ kind _) => kind
  | _ => .null

def globalType : Data := match PV_LIB_A_TypedBody218.node5 [.null] with
  | .leaf (.call _ (.object [("Regular",ptr)]) _ _ _) =>
      ((member "generics" ptr >>= generics).map (fun g => g.types[1]?.getD .null)).getD .null
  | _ => .null

def globalValue : Data := PV_THR2_KeyValues.pack globalKind []

/-- Only the retained source Global constructor is decoded here. Other
allocator values remain missing; the erased Error marker never becomes Global. -/
def allocatorType : Data → Option Data
  | .object [("thread-aggregate-kind",.object [("Adt",.array
      [.object [("id",.object [("Adt",.number 1)]),("generics",.object
        [("regions",.array []),("types",.array []),("const_generics",.array []),
         ("trait_refs",.array [])])],.null,.null])]),
      ("thread-aggregate-slots",.array [])] => some globalType
  | _ => none

/-- A supplied Arc's actual field2 is required. Its pointer and phantom do not
select an allocator. This decoder never modifies a value or allocation image. -/
def arcAllocator {W : Type} (C : PV_STX2_Store.Carrier W Data) (value : Data) : Option Data := do
  let allocator ← C.field value 2
  allocatorType allocator

/-- Exact generic405 instantiation, preserving the payload. No global default
is inserted by inspecting Arc's erased ADT type alone. -/
def arcGlue {W : Type} (C : PV_STX2_Store.Carrier W Data) (ty value : Data) : Option Resolution := do
  let .object [("Adt",a)] := ty | none
  let .object [("Adt",.number 21)] ← member "id" a | none
  let raw ← member "generics" a
  let g ← generics raw
  let [payload] := g.types | none
  let allocator ← arcAllocator C value
  PV_LIB_A_ExactDestructMethods.concrete 76 ⟨[],[payload,allocator],[],[]⟩

def arcKind (payload : Data) : Data := match PV_LIB_A_TypedBody315.node7 [payload,globalType] with
  | .leaf (.aggregateMove _ _ kind _) => kind
  | _ => .null

def constructed (payload ptr phantom : Data) : Data :=
  PV_THR2_KeyValues.pack (arcKind payload) [ptr,phantom,globalValue]

theorem allocator_literal : globalType = .object [("Adt",.object
    [("id",.object [("Adt",.number 1)]),("generics",encode ⟨[],[],[],[]⟩)])] := rfl

theorem constructor315_moves_A (payload allocator : Data) :
    ∃ site kind, PV_LIB_A_TypedBody315.node7 [payload,allocator] =
      .leaf (.aggregateMove site (.local 0) kind
        [.move (.local 3),.move (.local 4),.move (.local 5)]) := ⟨_,_,rfl⟩

theorem from_inner (payload : Data) :
    ∃ site args unwind, PV_LIB_A_TypedBody218.node5 [payload] =
      .leaf (.call site (.object [("Regular",fnPtr 315 ⟨[],[payload,globalType],[],[]⟩)])
        args (.local 0) unwind) := ⟨_,_,_,rfl⟩

theorem global_decoded : allocatorType globalValue = some globalType := rfl

theorem marker_not_default : allocatorType (.object [("Error",.atom "removed allocator parameter")]) = none := rfl

theorem source_allocator {W : Type} (base : PV_STX2_Store.Carrier W Data)
    (payload ptr phantom : Data) :
    arcAllocator (PV_THR2_KeyValues.carrier base) (constructed payload ptr phantom) = some globalType := by
  change allocatorType globalValue = some globalType
  exact global_decoded

theorem source_glue {W : Type} (base : PV_STX2_Store.Carrier W Data)
    (payload ptr phantom : Data) :
    arcGlue (PV_THR2_KeyValues.carrier base) (PV_LIB_A_TypedBindingFacts.arcType payload)
      (constructed payload ptr phantom) =
        some (.call (fnPtr 405 ⟨[.atom "Erased"],[payload,globalType],[],[]⟩)) := by
  simp [arcGlue,PV_LIB_A_TypedBindingFacts.arcType,member,generics,encode,
    source_allocator,PV_LIB_A_ExactDestructMethods.concrete,
    PV_LIB_A_ExactDestructMethods.implementation,PV_LIB_A_ExactDestructMethods.methodGenerics,
    substitute,globalType]

#print axioms globalKind
#print axioms globalType
#print axioms globalValue
#print axioms allocatorType
#print axioms arcAllocator
#print axioms arcGlue
#print axioms arcKind
#print axioms constructed
#print axioms allocator_literal
#print axioms constructor315_moves_A
#print axioms from_inner
#print axioms global_decoded
#print axioms marker_not_default
#print axioms source_allocator
#print axioms source_glue
end PV_LIB_A_AllocatorProvenance
