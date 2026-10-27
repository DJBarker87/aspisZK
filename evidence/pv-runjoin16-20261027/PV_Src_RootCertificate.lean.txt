import R1Z.PV_Src_RootPrefix
import R1Z.PV_Src_RootSourceEquation

/-! Sound symbolic composition of the twenty-one exact parent hash cells.
The cells remain named hypotheses until independently proved. -/
set_option autoImplicit false
namespace R1Z.PV_Src_RootCertificate
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_Src_RootRecurrence PV_Src_RootPrefix

theorem steps_eq [ExternalLinear] (n : Nat) (level : Usize) (roots target : Roots)
    (count : level.val + n = 20)
    (hprefix : Prefix roots target (level.val+1))
    (parents : ∀ l : Fin 20,
      format.pool_v1_tree_parent target.val[l.val]! target.val[l.val]! =
        ok target.val[l.val+1]!) :
    PV_Src_RootRecurrence.steps level n roots = ok target := by
  induction n generalizing level roots with
  | zero =>
    have h : roots = target := BuilderRecordsArray.prefix_done roots target
      (by simpa [show level.val = 20 by omega] using hprefix)
    rw [PV_Src_RootRecurrence.steps,h]
  | succ n ih =>
    have bound : level.val < 20 := by omega
    rw [PV_Src_RootRecurrence.steps,PV_Src_RootPrefix.step target roots level bound hprefix
      (parents ⟨level.val,bound⟩)]
    simp only [bind_tc_ok]
    apply ih
    · rw [BuilderRecordsArray.next_val level (by omega)];omega
    · have h := PV_Src_RootPrefix.extend target roots level bound hprefix
      simpa [BuilderRecordsArray.next_val level (by omega)] using h

theorem source_eq [ExternalLinear] (target : Roots)
    (initial_eq : format.pool_v1_tree_parent
      (Array.repeat 8#usize aspis_core.field.M31.ZERO)
      (Array.repeat 8#usize aspis_core.field.M31.ZERO) = ok target.val[0]!)
    (parents : ∀ l : Fin 20,
      format.pool_v1_tree_parent target.val[l.val]! target.val[l.val]! =
        ok target.val[l.val+1]!) :
    pair_trace.pair_empty_roots = ok target := by
  rw [PV_Src_RootSourceEquation.source,PV_Src_RootSourceEquation.run,initial_eq]
  simp only [bind_tc_ok]
  rw [BuilderRecordsArray.update_gen _ 0#usize _ (by decide)]
  simp only [bind_tc_ok]
  apply steps_eq 20 0#usize _ target (by decide) _ parents
  exact BuilderRecordsArray.prefix_step _ target 0#usize (by decide) (by
    intro j hj; simp only [UScalar.ofNatCore_val_eq] at hj; omega)

#print axioms steps_eq
#print axioms source_eq
end R1Z.PV_Src_RootCertificate
