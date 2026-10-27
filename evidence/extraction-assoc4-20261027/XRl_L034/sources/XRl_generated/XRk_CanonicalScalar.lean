import XRk_DotProjection
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRk_CanonicalScalar
def Canonical (q : aspis_core.field.QM31) : Prop :=
  q.c0.a < 2147483647#u32 ∧ q.c0.b < 2147483647#u32 ∧
  q.c1.a < 2147483647#u32 ∧ q.c1.b < 2147483647#u32

theorem checked (q : aspis_core.field.QM31) (raw : fast_pairing.canonical.Q)
    (run : fast_pairing.checked_q q=ok (.Ok raw)) : Canonical q := by
  unfold fast_pairing.checked_q fast_pairing.limbs_of at run
  simp only [bind_tc_ok] at run
  unfold fast_pairing.canonical.Q.from_limbs at run
  have h0 : (0#usize).val=0 := by scalar_tac
  have h1 : (1#usize).val=1 := by scalar_tac
  have h2 : (2#usize).val=2 := by scalar_tac
  have h3 : (3#usize).val=3 := by scalar_tac
  simp only [Array.index_usize,Array.make,Array.getElem?_Usize_eq,h0,h1,h2,h3,
    List.getElem?_cons_zero,List.getElem?_cons_succ,bind_tc_ok] at run
  split_ifs at run <;> simp_all [Canonical,fast_pairing.canonical.P]
#print axioms checked
end XRk_CanonicalScalar
