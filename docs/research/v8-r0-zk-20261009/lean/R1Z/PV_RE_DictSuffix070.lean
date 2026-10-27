import R1Z.PV_RE_DictSuffix069
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix070
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.append_opening_base_row`.
Recursive calls remain the original extracted calls. -/
def continueAfter (out : alloc.vec.Vec Std.U8) (row : Array aspis_core.field.wide_exact.WideExact 29#usize) (pvBoundValue : Payload (prover.append_opening_base_row_loop out row 0#usize)) : Result (alloc.vec.Vec Std.U8) := do
  let out1 := pvBoundValue
  let we ← Array.index_usize row 28#usize
  let bytes ← aspis_core.field.wide_exact.WideExact.to_le_bytes we
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) bytes
      { «end» := 16#usize }
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s


end R1Z.PV_RE_DictSuffix070
pv_dict_congr ProverRwFull.prover.append_opening_base_row
pv_dict_congr R1Z.PV_RE_DictSuffix070.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.prover.append_opening_base_row
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix070.continueAfter
