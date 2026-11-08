import PV_STX2_AggregateKinds
import PV_STX2_Uc7Guards
set_option autoImplicit false
namespace PV_STX2_Aggregates
open PV_STX2_Syntax PV_STX2_Store PV_STX2_AggregateKinds

/-- Conditional worker-branch semantics pending owner acceptance of the
unadopted patch. A field slot distinguishes a live null value from a moved
field. Empty fields represent the emitted unit-like allocator, not failure. -/
def pack (kind : Data) (values : List Data) : Data :=
  .object [("aggregate-kind",kind),
    ("aggregate-slots",.array (values.map (fun v => .array [v])))]

/-- Conditional worker-branch semantics pending owner acceptance of the patch.
Interpret the emitted ADT kind and ordered fields. The four arities are the
source selections in AggregateKinds, not a success assumption on a carrier.
Other kinds stay undefined until their source interpretation is installed. -/
def aggregate (kind : Data) (values : List Data) : Option Data :=
  match kind with
  | .object [("Adt",.array [.object [("id",.object [("Adt",.number id)]),
      ("generics",.object [("regions",.array []),("types",.array []),
        ("const_generics",.array []),("trait_refs",.array [])])],.null,.null])] =>
    match id, values with
    | 16, [] | 4, [_,_] | 1, [_,_] | 0, [_] => some (pack kind values)
    | _, _ => none
  | _ => none

/-- Conditional worker-branch semantics pending owner acceptance of the patch.
Projection of a live field returns that exact payload, including Data.null. -/
def slotValue : Data → Option Data
  | .array [v] => some v
  | _ => none

/-- Conditional worker-branch semantics pending owner acceptance of the patch.
A move removes the addressed field slot; it never destroys its siblings. -/
def updateSlots : List Data → Nat → Option Data → Option (List Data)
  | [], _, _ => none
  | _ :: xs, 0, v => some ((.array v.toList) :: xs)
  | x :: xs, n+1, v => (updateSlots xs n v).map (x :: ·)

/-- Conditional worker-branch semantics pending owner acceptance of the patch.
Concrete aggregate/field store interpretation over the existing stx world W.
Unrelated primitive semantics remain the base carrier's, not new axioms.
This installs no OWNER decoder, allocation validity or source7 association. -/
def carrier {W : Type} (base : Carrier W Data) : Carrier W Data :=
  {PV_STX2_Uc7Guards.carrier base with
    aggregate := aggregate
    field := fun value n => match value with
      | .object [("aggregate-kind",_), ("aggregate-slots",.array xs)] =>
          xs[n]? >>= slotValue
      | _ => base.field value n
    replaceField := fun value n replacement => match value with
      | .object [("aggregate-kind",kind), ("aggregate-slots",.array xs)] =>
          (updateSlots xs n replacement).map (fun ys =>
            .object [("aggregate-kind",kind),("aggregate-slots",.array ys)])
      | _ => base.replaceField value n replacement
    constant := fun d => match d with
      | .object [("kind",.object [("Literal",.object [("Scalar",.object
          [("Unsigned",.array [.atom "Usize",.atom "0"])])])]),("ty",_)] =>
          some (.number 0)
      | _ => base.constant d}

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
The formerly failing empty-field case is the source's unit-like aggregate. -/
theorem allocator : aggregate allocatorKind [] = some (pack allocatorKind []) := rfl

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
RawVec preserves constructor reply then allocator in their emitted order. -/
theorem rawVec (inner alloc : Data) :
    aggregate rawVecKind [inner,alloc] = some (pack rawVecKind [inner,alloc]) := rfl

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
Vec preserves the RawVec and length fields. -/
theorem vec (raw len : Data) :
    aggregate vecKind [raw,len] = some (pack vecKind [raw,len]) := rfl

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
The return aggregate of function0 preserves its array-column reply. -/
theorem source7 (columns : Data) :
    aggregate source7Kind [columns] = some (pack source7Kind [columns]) := rfl

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
First projection is exact; no erased-value search is involved. -/
theorem first {W : Type} (base : Carrier W Data) (kind value : Data)
    (rest : List Data) : (carrier base).field (pack kind (value :: rest)) 0 = some value := rfl

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
Second projection is exact, including a null payload. -/
theorem second {W : Type} (base : Carrier W Data) (kind v w : Data)
    (rest : List Data) : (carrier base).field (pack kind (v :: w :: rest)) 1 = some w := rfl

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
The precise constructor aggregate destination succeeds at any initial store. -/
theorem bind_allocator {W : Type} (base : Carrier W Data) (s : Store Data)
    (w : W) (a : Nat) :
    PV_STX2_Store.bind (carrier base) s w a (.local 19)
      (.aggregate allocatorKind []) =
      some (write s ⟨a,19,[]⟩ (some (pack allocatorKind []))) := rfl

#print axioms pack
#print axioms aggregate
#print axioms slotValue
#print axioms updateSlots
#print axioms carrier
#print axioms allocator
#print axioms rawVec
#print axioms vec
#print axioms source7
#print axioms first
#print axioms second
#print axioms bind_allocator
end PV_STX2_Aggregates
