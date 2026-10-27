import R1Z.PV_RE_DictSuffix010
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix011
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.opening_lane_values`.
Recursive calls remain the original extracted calls. -/
def continueAfter (word : host_commitment.Word) (u : aspis_core.r0.domain.FibreIndex) (out : Payload (aspis_core.r0.domain.FibreIndex.get u)) : Result (Array aspis_core.field.wide_exact.WideExact 4#usize) := do
  let i := out
  let at1 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i)
  let we ← host_commitment.Word.value word at1
  let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 1#usize)
  let we1 ← host_commitment.Word.value word i1
  let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 2#usize)
  let we2 ← host_commitment.Word.value word i2
  let i3 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 3#usize)
  let we3 ← host_commitment.Word.value word i3
  ok (Array.make 4#usize [ we, we1, we2, we3 ])


end R1Z.PV_RE_DictSuffix011
pv_dict_congr ProverRwFull.host_commitment.opening_lane_values
pv_dict_congr R1Z.PV_RE_DictSuffix011.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_commitment.opening_lane_values
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix011.continueAfter
