import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue014
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.claim_mask_value`.
Recursive calls remain the original extracted calls. -/
def continueAfter (claims : Array aspis_core.field.QM31 29#usize) (point : Array aspis_core.field.QM31 10#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result aspis_core.field.QM31 := do
  let q := out
  let semantic := Array.repeat 16#usize q
  let mask_only := Array.repeat 10#usize q
  let (s, to_slice_mut_back) ← Aeneas.Std.lift (Array.to_slice_mut semantic)
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31))
      claims { «end» := 16#usize }
  let s2 ←
    core.slice.Slice.copy_from_slice aspis_core.field.QM31.Insts.CoreMarkerCopy
      s s1
  let semantic1 := to_slice_mut_back s2
  let (s3, to_slice_mut_back1) ← Aeneas.Std.lift (Array.to_slice_mut mask_only)
  let s4 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31))
      claims { start := 16#usize, «end» := 26#usize }
  let s5 ←
    core.slice.Slice.copy_from_slice aspis_core.field.QM31.Insts.CoreMarkerCopy
      s3 s4
  let mask_only1 := to_slice_mut_back1 s5
  let q1 ← Array.index_usize claims 27#usize
  aspis_core.state_only_hiding.state_only_selected_mask_value semantic1
    mask_only1 q1 point

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (claims : Array aspis_core.field.QM31 29#usize) (point : Array aspis_core.field.QM31 10#usize) :
    host_semantic.claim_mask_value (claims := claims) (point := point) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (claims := claims) (point := point) out) := by
  rw [host_semantic.claim_mask_value]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (claims : Array aspis_core.field.QM31 29#usize) (point : Array aspis_core.field.QM31 10#usize) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    host_semantic.claim_mask_value (claims := claims) (point := point) = continueAfter (claims := claims) (point := point) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (claims : Array aspis_core.field.QM31 29#usize) (point : Array aspis_core.field.QM31 10#usize) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    host_semantic.claim_mask_value (claims := claims) (point := point) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (claims : Array aspis_core.field.QM31 29#usize) (point : Array aspis_core.field.QM31 10#usize)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    host_semantic.claim_mask_value (claims := claims) (point := point) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue014
