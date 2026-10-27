import R1Z.PV_CB3_WeightsQuotient
import R1Z.PV_CB3_StagedComposition
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsExtraRead
open Aeneas Aeneas.Std Result ProverRwFull

theorem cast_value (x : Usize) (h : x.val < 32) : (UScalar.cast .U64 x).val = x.val := by
  change (BitVec.zeroExtend 64 x.bv).toNat = _
  rw [BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by change x.val < 18446744073709551616; omega)

def read (extra : Array aspis_core.field.QM31 2#usize) (j : Usize) :
    Result (aspis_core.field.QM31 × U64) := do
  let q ← UScalar.div j 28#usize
  let r ← UScalar.rem j 28#usize
  let point ← Array.index_usize extra q
  ok (point,UScalar.cast .U64 r)

theorem total (extra : Array aspis_core.field.QM31 2#usize) (j : Usize) (h : j.val < 56) :
    ∃ point e, read extra j = ok (point,e) ∧ e.val < 28 := by
  obtain ⟨q,hq,hqv⟩ := PV_CB3_WeightsQuotient.quotient j 28#usize (by change 28≠0; omega)
  obtain ⟨r,hr,hrv⟩ := PV_CB3_WeightsQuotient.remainder j 28#usize (by change 28≠0; omega)
  change q.val=j.val/28 at hqv
  change r.val=j.val%28 at hrv
  have hqb : q.val < 2 := by omega
  have hrb : r.val < 28 := by omega
  obtain ⟨point,hp⟩ := PV_CB3_StagedComposition.read_total extra q hqb
  refine ⟨point,UScalar.cast .U64 r,?_,?_⟩
  · simp only [read,hq,hr,hp,bind_tc_ok]
  · rw [cast_value r (by omega)]
    exact hrb
#print axioms cast_value
#print axioms total
end R1Z.PV_CB3_WeightsExtraRead
