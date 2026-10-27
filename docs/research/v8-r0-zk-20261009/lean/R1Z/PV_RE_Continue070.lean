import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue070
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.append_opening_base_row`.
Recursive calls remain the original extracted calls. -/
def continueAfter (out : alloc.vec.Vec Std.U8) (row : Array aspis_core.field.wide_exact.WideExact 29#usize) (out : Payload (prover.append_opening_base_row_loop out row 0#usize)) : Result (alloc.vec.Vec Std.U8) := do
  let out1 := out
  let we ← Array.index_usize row 28#usize
  let bytes ← aspis_core.field.wide_exact.WideExact.to_le_bytes we
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) bytes
      { «end» := 16#usize }
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (out : alloc.vec.Vec Std.U8) (row : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    prover.append_opening_base_row (out := out) (row := row) =
      (prover.append_opening_base_row_loop out row 0#usize >>= fun out => continueAfter (out := out) (row := row) out) := by
  rw [prover.append_opening_base_row]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (out : alloc.vec.Vec Std.U8) (row : Array aspis_core.field.wide_exact.WideExact 29#usize) (out : Payload (prover.append_opening_base_row_loop out row 0#usize))
    (h : (prover.append_opening_base_row_loop out row 0#usize) = .ok out) :
    prover.append_opening_base_row (out := out) (row := row) = continueAfter (out := out) (row := row) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (out : alloc.vec.Vec Std.U8) (row : Array aspis_core.field.wide_exact.WideExact 29#usize) (e : Error)
    (h : (prover.append_opening_base_row_loop out row 0#usize) = .fail e) :
    prover.append_opening_base_row (out := out) (row := row) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (out : alloc.vec.Vec Std.U8) (row : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (h : (prover.append_opening_base_row_loop out row 0#usize) = .div) :
    prover.append_opening_base_row (out := out) (row := row) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue070
