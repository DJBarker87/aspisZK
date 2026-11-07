import PV_STX2_ChainCaptures
set_option autoImplicit false
namespace PV_STX2_SliceCapture
open PV_STX2_Syntax PV_STX2_Store PV_STX2_Native PV_STX2_ChainCaptures

/-- Conditional worker-branch evidence pending owner acceptance of the
unadopted patch. The to_vec activation is derived from f9's two moves; the
second read uses the store after the slice move, preserving move ordering. -/
theorem f9_to_f12 {W : Type} (base : Carrier W Data) (c : Config Data) (w : W) :
    entryAt base c w PV_STX2_Intermediate.function9.body[20]? = (do
      let (slice,s) ← operand (PV_STX2_TypedReferences.carrier base)
        c.store w c.activation (.move (.local 4))
      let (allocator,s') ← operand (PV_STX2_TypedReferences.carrier base)
        s w c.activation (.move (.local 2))
      pure (enter PV_STX2_Generated.function12 [slice,allocator] s')) := by
  change (do
    let (values,s) ← operands (PV_STX2_TypedReferences.carrier base)
      w c.activation [.move (.local 4),.move (.local 2)] c.store
    pure (enter PV_STX2_Generated.function12 values s)) = _
  cases h4 : operand (PV_STX2_TypedReferences.carrier base)
    c.store w c.activation (.move (.local 4)) with
  | none => simp [operands,h4]
  | some pair =>
    rcases pair with ⟨slice,s⟩
    cases h2 : operand (PV_STX2_TypedReferences.carrier base)
      s w c.activation (.move (.local 2)) with
    | none => simp [operands,h4,h2]
    | some pair => rcases pair with ⟨allocator,s'⟩; simp [operands,h4,h2]

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
Local metadata lookup after allocation reads the actual first capture. It
neither asserts this value is typed nor supplies a length for it. -/
theorem entry_metadata {W : Type} (base : Carrier W Data) (s : Store Data)
    (slice allocator : Data) (w : W) :
    let child := enter PV_STX2_Generated.function12 [slice,allocator] s
    PV_STX2_Store.read (PV_STX2_TypedReferences.carrier base) child.store w
      child.activation (.project (.local 1) .metadata) =
      (PV_STX2_TypedReferences.carrier base).metadata slice := by
  simp [enter,arguments,PV_STX2_Store.read,write]

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
The f12 metadata is obtained by dereading f9's moved Local4 after the exact
allocator move succeeds. All missing-cell/metadata cases remain none. -/
theorem f12_metadata_from_caller {W : Type} (base : Carrier W Data)
    (c : Config Data) (w : W) :
    ((entryAt base c w PV_STX2_Intermediate.function9.body[20]?).bind
      (fun child => PV_STX2_Store.read (PV_STX2_TypedReferences.carrier base)
        child.store w child.activation (.project (.local 1) .metadata))) = (do
      let (slice,s) ← operand (PV_STX2_TypedReferences.carrier base)
        c.store w c.activation (.move (.local 4))
      let _ ← operand (PV_STX2_TypedReferences.carrier base)
        s w c.activation (.move (.local 2))
      (PV_STX2_TypedReferences.carrier base).metadata slice) := by
  rw [f9_to_f12]
  cases h4 : operand (PV_STX2_TypedReferences.carrier base)
    c.store w c.activation (.move (.local 4)) with
  | none => simp [h4]
  | some pair =>
    rcases pair with ⟨slice,s⟩
    cases h2 : operand (PV_STX2_TypedReferences.carrier base)
      s w c.activation (.move (.local 2)) with
    | none => simp [h4,h2]
    | some pair =>
      rcases pair with ⟨allocator,s'⟩
      simp [h4,h2,entry_metadata]

/-- Conditional worker-branch evidence pending owner acceptance of the patch.
The source constructs Local4 by borrowing the pointer Local5 and copying
Local5's metadata. Neither the address nor the length is a free capture. -/
theorem slice_reference_operands :
    match PV_STX2_Intermediate.function9.body[18]? with
    | some (Instruction.bind _ destination (Expr.reference place metadata)) =>
      destination = .local 4 ∧ place = .project (.local 5) .deref ∧
        metadata = Operand.copy (.project (.local 5) .metadata)
    | _ => False := ⟨rfl,rfl,rfl⟩

#print axioms f9_to_f12
#print axioms entry_metadata
#print axioms f12_metadata_from_caller
#print axioms slice_reference_operands
end PV_STX2_SliceCapture
