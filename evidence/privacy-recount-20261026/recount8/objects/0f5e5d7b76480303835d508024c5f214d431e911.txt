import R1Z.PV_RDCD3_V260Folds
set_option autoImplicit false
namespace R1Z.PV_RDCD3_V260Owned
open Aeneas Aeneas.Std Result PV_B2_253c1
abbrev K := aspis_core.field.QM31
/-- Direct finite-tag comparison, without adding a library dictionary. -/
def isD : transport.Variant → Bool
  | .D => true
  | .S1 => false
  | .S2 => false



def inactive (w : host_weights.Weights) (j : Usize) : Result K := do
  let r ← host_weights.host_row w.variant j
  let row ← r / 16#usize
  let mask ← Array.index_usize aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS row
  let bit ← r % 16#usize
  if (U16.wrapping_shr mask (UScalar.cast .U32 bit) &&& 1#u16)=0#u16
  then ok aspis_core.field.QM31.ONE else ok aspis_core.field.QM31.ZERO

def extra (w : host_weights.Weights) (j : Usize) : Result K := do
  if j < 56#usize then
    let i ← j / 28#usize
    let q ← Array.index_usize w.extra i
    let n ← j % 28#usize
    aspis_core.field.QM31.pow q (UScalar.cast .U64 n)
  else ok aspis_core.field.QM31.ZERO

def tensor (w : host_weights.Weights) (kind j : Usize) : Result K := do
  let row ← if kind < 4#usize then ok (Usize.wrapping_sub kind 1#usize)
             else ok (Usize.wrapping_sub kind 2#usize)
  let factors ← Array.index_usize w.factors row
  PV_RDCD3_RangeLoop.source (PV_RDCD3_V260Folds.tensorStep factors j) ⟨0,5⟩ aspis_core.field.QM31.ONE

def point (w : host_weights.Weights) (kind j : Usize) : Result K := do
  let r ← host_weights.host_row w.variant j
  let points ← Array.index_usize w.points (Usize.wrapping_sub kind 1#usize)
  PV_RDCD3_RangeLoop.source (PV_RDCD3_V260Folds.pointStep points r) ⟨0,10⟩ aspis_core.field.QM31.ONE

/-- Owned source-shaped match. Rust agreement of imported Aeneas leaves is
reclassification within existing tool trust, never endpoint premise removal.
Structural frozen match, with the exact complete Result boundary of every
read and arithmetic helper. Ordered folds preserve all factors and errors. -/
def original (w : host_weights.Weights) (kind j : Usize) : Result K :=
  if kind=0#usize then inactive w j
  else if kind=4#usize then extra w j
  else if kind≥1#usize ∧ kind≤3#usize ∧ isD w.variant=true then point w kind j
  else tensor w kind j

theorem variant_eq (v : transport.Variant) :
    transport.Variant.Insts.CoreCmpPartialEqVariant.eq v .D = ok (isD v) := by
  cases v <;> simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    transport.Variant.read_discriminant,isD] <;> scalar_tac
#print axioms variant_eq

theorem source (w : host_weights.Weights) (kind j : Usize) :
    host_weights.raw_value w kind j = original w kind j := by
  by_cases h0 : kind=0#usize
  · simp only [host_weights.raw_value,original,h0,if_true,inactive,lift,bind_tc_ok]
  by_cases h4 : kind=4#usize
  · subst kind
    simp only [host_weights.raw_value,original,
      show ¬ (4#usize=0#usize) from by decide,if_false,if_true,extra,lift,bind_tc_ok]
  by_cases h1 : kind≥1#usize <;> by_cases h3 : kind≤3#usize <;>
    by_cases hv : isD w.variant=true <;>
    simp only [host_weights.raw_value,original,h0,h4,h1,h3,hv,if_true,if_false,
      variant_eq,lift,bind_tc_ok,tensor,point,
      and_true,and_false,true_and,false_and,Bool.false_eq_true,
      PV_RDCD3_V260Folds.tensor_loop,PV_RDCD3_V260Folds.point_loop] <;> rfl
#print axioms source
end R1Z.PV_RDCD3_V260Owned
