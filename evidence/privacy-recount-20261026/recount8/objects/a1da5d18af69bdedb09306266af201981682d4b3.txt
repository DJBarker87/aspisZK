import R1Z.ProverRwSuccessByteEquality
import R1Z.ProverRwSuccessInverseInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessEquality
open Aeneas Aeneas.Std Result ProverRwFull
attribute [local instance] Classical.propDecidable
abbrev Point := aspis_core.circle.SecureCirclePoint
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
-- Derived Rust PartialEq control, with both field and byte comparisons proved.
def pointEq (a b : Point) : Result Bool := do
  let x ← ProverRwDictionaryDerived.qEq a.x b.x
  if x then ProverRwDictionaryDerived.qEq a.y b.y else .ok false

def contextEq (a b : Context) : Result Bool := do
  let digest ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a.statement_digest b.statement_digest
  if digest then
    let nonce ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a.mask_nonce b.mask_nonce
    if nonce then
      if a.mask_layout_fingerprint = b.mask_layout_fingerprint then
        .ok (decide (a.layout_factor_fingerprint = b.layout_factor_fingerprint))
      else .ok false
    else .ok false
  else .ok false

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessInverseInstall.selected ops with op37 := pointEq, op114 := contextEq}

theorem point_total (ops : ExternalFuns) (a b : Point) :
    (selected ops).op37 a b = .ok (decide (a=b)) := by
  change pointEq a b = _
  unfold pointEq
  rw [ProverRwDictionaryDerived.q_status]
  cases a with
  | mk x y => cases b with
    | mk u v =>
      by_cases hx : x=u <;> by_cases hy : y=v <;>
        simp [hx,hy,ProverRwDictionaryDerived.q_status]

theorem context_total (ops : ExternalFuns) (a b : Context) :
    (selected ops).op114 a b = .ok (decide (a=b)) := by
  change contextEq a b = _
  unfold contextEq
  simp only [ProverRwSuccessByteEquality.array_eq,bind_tc_ok]
  cases a with
  | mk d n m l => cases b with
    | mk d' n' m' l' =>
      by_cases hd : d=d' <;> by_cases hn : n=n' <;>
      by_cases hm : m=m' <;> by_cases hl : l=l' <;>
        simp [hd,hn,hm,hl]
#print axioms point_total
#print axioms context_total
end R1Z.ProverRwSuccessEquality
