import PV_STX2_LengthBranch
set_option autoImplicit false
namespace PV_STX2_TypedReferences
open PV_STX2_Syntax PV_STX2_Store

/-- Conditional worker-branch interpretation pending owner acceptance of the
unadopted patch. Native address fields are decoded without erased-value search. -/
def fields : List Data → Option (List Nat)
  | [] => some []
  | .number n :: rest => (fields rest).map (n :: ·)
  | _ => none

/-- Conditional worker-branch evidence pending owner acceptance of the patch. -/
theorem fields_roundtrip (ns : List Nat) : fields (ns.map Data.number) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp only [List.map_cons,fields,ih,Option.map_some]

/-- Conditional worker-branch interpretation pending owner acceptance of the
patch. Metadata is the operand supplied by the emitted reference expression;
it is not guessed from a return value or replaced with a successful length. -/
def reference (p : Address) (metadata : Data) : Data :=
  .object [("native-reference",.array [.number p.activation,
    .number p.localIndex,.array (p.fields.map Data.number),metadata])]

/-- Conditional worker-branch interpretation pending owner acceptance of the patch. -/
def decode : Data → Option (Address × Data)
  | .object [("native-reference",.array [.number a,.number n,.array ns,m])] =>
      (fields ns).map (fun path => (⟨a,n,path⟩,m))
  | _ => none

/-- Conditional worker-branch evidence pending owner acceptance of the patch. -/
theorem roundtrip (p : Address) (metadata : Data) :
    decode (reference p metadata) = some (p,metadata) := by
  cases p
  simp only [reference,decode,fields_roundtrip,Option.map_some]

/-- Conditional worker-branch interpretation pending owner acceptance of the
patch. Install the reference constructor and its two destructors together.
Top-level Foundation lookup still belongs to the current caller's receiver;
this definition supplies no original Foundation place or input equality. -/
def carrier {W : Type} (base : Carrier W Data) : Carrier W Data :=
  {PV_STX2_LengthBranch.carrier base with
    reference := reference
    metadata := fun value => match decode value with
      | some (_,m) => some m
      | none => base.metadata value
    dereference := fun w value => match decode value with
      | some (p,_) => some p
      | none => base.dereference w value
    constant := fun value => match value with
      | .object [("kind",.object [("Adt",.array [.null,.array []])]),("ty",_)] =>
          some .null
      | _ => (PV_STX2_LengthBranch.carrier base).constant value}

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
Self-generated references have exact metadata, including thin unit metadata. -/
theorem metadata {W : Type} (base : Carrier W Data) (p : Address) (m : Data) :
    (carrier base).metadata (reference p m) = some m := by
  simp only [carrier,roundtrip]

/-- Conditional worker-branch evidence pending owner acceptance of the patch. -/
theorem dereference {W : Type} (base : Carrier W Data) (w : W)
    (p : Address) (m : Data) :
    (carrier base).dereference w (reference p m) = some p := by
  simp only [carrier,roundtrip]

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
The original reference's missing lookup is retained; it is never made success. -/
theorem original_lookup {W : Type} (base : Carrier W Data) (w : W) (input : Data)
    (original : decode input = none) :
    (carrier base).dereference w input = base.dereference w input := by
  simp only [carrier,original]

#print axioms fields
#print axioms fields_roundtrip
#print axioms reference
#print axioms decode
#print axioms roundtrip
#print axioms carrier
#print axioms metadata
#print axioms dereference
#print axioms original_lookup
end PV_STX2_TypedReferences
