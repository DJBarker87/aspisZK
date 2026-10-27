import R1Z.PV_Src_PortInternalLoop
import R1Z.PV_Src_PortSboxStep

/-! Canonicality of each written internal-linear lane, retaining the exact
source words in the untouched prefix. No field-value equality is assumed. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalCanonical
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortInternalStep PV_Src_PortInternalLoop

theorem steps_canonical (n : Nat) (index : Usize) (state : State) (full : U64)
    (count : index.val+n=16) (prior : ∀ j, j < index.val → state.val[j]!.val < 2147483647) :
    PV_Src_PortSboxStep.Canonical (steps n index state full) := by
  induction n generalizing index state with
  | zero =>
    intro j
    exact prior j.val (by have := j.isLt;omega)
  | succ n ih =>
    have hi : index.val < 16 := by omega
    simp only [steps]
    apply ih
    · rw [BuilderRecordsArray.next_val index (by omega)];omega
    · intro j hj
      rw [BuilderRecordsArray.set_get state index _ j (by simpa using hi)]
      split
      · exact canonical state full index
      · next hne =>
        apply prior
        have hn := BuilderRecordsArray.next_val index (by omega)
        rw [hn] at hj
        omega

theorem full_canonical (state : State) (full : U64)
    (first : state.val[0]!.val < 2147483647) :
    ∃ out, poseidon2.internal_linear_lazy_loop {start := 1#usize, «end» := 16#usize}
      state full = ok out ∧ PV_Src_PortSboxStep.Canonical out := by
  refine ⟨steps 15 1#usize state full, full_loop state full, ?_⟩
  apply steps_canonical 15 1#usize state full (by decide)
  intro j hj
  have hj0 : j=0 := by simp only [UScalar.ofNatCore_val_eq] at hj;omega
  simpa only [hj0] using first

#print axioms steps_canonical
#print axioms full_canonical
end R1Z.PV_Src_PortInternalCanonical
