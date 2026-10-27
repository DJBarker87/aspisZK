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
  simp only [Array.index_usize,Array.make,bind_tc_ok] at run
  split_ifs at run <;> simp_all [Canonical,fast_pairing.canonical.P]
#print axioms checked
end XRk_CanonicalScalar
