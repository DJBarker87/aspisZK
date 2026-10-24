import S9TwoDualFoldExpansionV1
import S3S9CurrentSourceModel
set_option autoImplicit false
noncomputable section
namespace AspisR1S9TwoDualSourceBaseV1
open AspisR1
open AspisR1S9TwoDualFoldExpansionV1
open scoped BigOperators
variable {K : Type} [Field K]

abbrev powers (a : K) (r : Fin 4) : K := a^r.val

def lowWeight (a0 a1 : K) (s : Fin 16) : K :=
  AspisR1.S3S9CurrentSourceModel.oldS9Low (powers a0) (powers a1) RoundPairing.quarter s

theorem source_perm_value (r : Fin 4) :
    (AspisR1.S2LibraFactoredIdentity.perm r).val=(4-r.val)%4 := by
  fin_cases r <;> rfl

theorem low_weight_formula (a0 a1 : K) (s : Fin 16) :
    lowWeight a0 a1 s=a0^((4-s.val%4)%4)*a1^((4-s.val/4)%4)*RoundPairing.quarter^2 := by
  unfold lowWeight AspisR1.S3S9CurrentSourceModel.oldS9Low powers
  rw [source_perm_value,source_perm_value]

/-- Boolean raw row, without any source table or1024-cell evaluation. -/
def booleanRow (flag : Fin 1024 → Bool) (i : Fin 1024) : K := if flag i then 1 else 0

theorem boolean_two_dual_at (a0 a1 : K) (flag : Fin 1024 → Bool) (d : Fin 64) :
    RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (booleanRow flag)) d=
      ∑s : Fin 16,if flag (blockIndex d s) then lowWeight a0 a1 s else 0 := by
  rw [two_dual_fold_1024_64]
  apply Finset.sum_congr rfl
  intro s _
  cases hflag : flag (blockIndex d s) with
  | false => simp only [booleanRow,hflag,Bool.false_eq_true,↓reduceIte,zero_mul]
  | true =>
    simp only [booleanRow,hflag,↓reduceIte,one_mul]
    rw [low_weight_formula]
    ring

theorem boolean_two_dual_dot (a0 a1 : K) (flag : Fin 1024 → Bool) (f : Fin 64 → K) :
    RoundPairing.dot f (RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (booleanRow flag)))=
      AspisR1.S3S9CurrentSourceModel.ungroupedPair f (lowWeight a0 a1)
        (fun d s=>flag (blockIndex d s)) := by
  unfold RoundPairing.dot AspisR1.S3S9CurrentSourceModel.ungroupedPair
  simp_rw [boolean_two_dual_at]
  simp only [Finset.mul_sum,mul_ite,mul_zero]

/-- The existing concrete inactive classification is only selected here;
its unchanged table/classification theorem is reused, never enumerated. -/
def inactiveFlag (i : Fin 1024) : Bool :=
  decide (AspisR1.S3S9CurrentSourceModel.sourceInactive
    (AspisR1.S3S9CurrentSourceModel.s2Row i.val)=1)

def inactiveRow (i : Fin 1024) : K := booleanRow inactiveFlag i

theorem inactive_flag_block (d : Fin 64) (s : Fin 16) :
    inactiveFlag (blockIndex d s)=AspisR1.S3S9CurrentSourceModel.inactiveAtSource d s := rfl

theorem inactive_two_dual_dot (a0 a1 : K) (f : Fin 64 → K) :
    RoundPairing.dot f (RoundPairing.dualFold a1 (RoundPairing.dualFold a0 inactiveRow))=
      AspisR1.S3S9CurrentSourceModel.ungroupedPair f (lowWeight a0 a1)
        AspisR1.S3S9CurrentSourceModel.inactiveAtSource := by
  change RoundPairing.dot f (RoundPairing.dualFold a1 (RoundPairing.dualFold a0 (booleanRow inactiveFlag)))=_
  have h:=boolean_two_dual_dot a0 a1 inactiveFlag f
  simpa only [inactive_flag_block] using h

#print axioms source_perm_value
#print axioms low_weight_formula
#print axioms boolean_two_dual_at
#print axioms boolean_two_dual_dot
#print axioms inactive_flag_block
#print axioms inactive_two_dual_dot
end AspisR1S9TwoDualSourceBaseV1
end
