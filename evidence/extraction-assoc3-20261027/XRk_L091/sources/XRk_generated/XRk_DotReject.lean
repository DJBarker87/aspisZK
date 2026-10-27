import XRk_DotCells
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRk_DotReject
theorem limit_frame (old : fast_pairing.EbyKDot)
    (e : aspis_core.field.wide_exact.WideExact) (q : aspis_core.field.QM31)
    (limit : old.count >= 4096#usize) :
    fast_pairing.EbyKDot.push old e q=ok (.Err (),old) := by
  have full : old.count >= fast_pairing.MAX_TERMS := by
    simpa only [fast_pairing.MAX_TERMS] using limit
  simp only [fast_pairing.EbyKDot.push,full,ite_true]

theorem invalid_scalar (q : aspis_core.field.QM31) (invalid : ¬XRk_CanonicalScalar.Canonical q) :
    fast_pairing.checked_q q=ok (.Err ()) := by
  unfold fast_pairing.checked_q fast_pairing.limbs_of
  simp only [bind_tc_ok]
  unfold fast_pairing.canonical.Q.from_limbs
  have h0 : (0#usize).val=0 := by scalar_tac
  have h1 : (1#usize).val=1 := by scalar_tac
  have h2 : (2#usize).val=2 := by scalar_tac
  have h3 : (3#usize).val=3 := by scalar_tac
  simp only [Array.index_usize,Array.make,Array.getElem?_Usize_eq,h0,h1,h2,h3,
    List.getElem?_cons_zero,List.getElem?_cons_succ,bind_tc_ok]
  split_ifs <;> simp_all [XRk_CanonicalScalar.Canonical,fast_pairing.canonical.P]
#print axioms limit_frame
#print axioms invalid_scalar
end XRk_DotReject
