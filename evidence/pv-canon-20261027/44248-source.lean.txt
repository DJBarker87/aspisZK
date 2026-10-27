import R1Z.PV_Canon_Carrier
import R1Z.ProverCommitArrayIndex25
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem update_read {α : Type} {n : Usize} (xs ys : Array α n)
    (i : Usize) (q z : α) (hi : i.val < n.val)
    (hu : Array.update xs i q = .ok ys) (hr : Array.index_usize ys i = .ok z) : z = q := by
  have hidx : i.val < xs.val.length := by rw [xs.property]; exact hi
  obtain ⟨out,hout,hset⟩ := WP.spec_imp_exists (Array.update_spec xs i q hidx)
  rw [hout] at hu
  cases hu
  rw [ProverCommitArrayIndex25.array_index_usize_ok ys i hi] at hr
  rw [hset] at hr
  change Result.ok ((xs.val.set i.val q)[i.val]'(by simpa only [List.length_set] using hidx)) = .ok z at hr
  simp only [List.getElem_set_self] at hr
  exact (Result.ok.inj hr).symm
 theorem update_read_canonical (xs ys : Array aspis_core.field.QM31 10#usize)
    (i : Usize) (q z : aspis_core.field.QM31) (hi : i.val < 10) (hq : Q q)
    (hu : Array.update xs i q = .ok ys) (hr : Array.index_usize ys i = .ok z) : Q z := by
  rw [update_read xs ys i q z hi hu hr]
  exact hq
#print axioms update_read
#print axioms update_read_canonical
end R1Z.PV_Canon
