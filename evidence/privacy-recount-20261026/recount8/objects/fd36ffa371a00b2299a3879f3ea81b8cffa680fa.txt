import R1Z.PV_RunJoin_World

/-! Capacity lemmas for the source-derived entropy prototype. These do not
install native effects or an FS experiment. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EntropyTotal
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
variable [ErasureFns]

theorem scan_total (bytes : Array U8 32#usize) (combined : U8)
    (index : Usize) (fuel : Nat) (bound : index.val + fuel = 32) :
    ∃ out, entropy_nonzero32_loop bytes combined index = .ok out := by
  induction fuel generalizing index combined with
  | zero =>
    have stop : ¬ index < 32#usize := by change ¬ index.val < 32; omega
    refine ⟨combined,?_⟩
    unfold entropy_nonzero32_loop
    rw [loop]
    simp only [entropy_nonzero32_loop.body,stop,if_false,bind_tc_ok]
  | succ fuel ih =>
    have go : index < 32#usize := by change index.val < 32; omega
    have inside : index.val < bytes.length := by
      have length : bytes.length = 32 := by simp [Array.length]
      omega
    obtain ⟨value,read,_⟩ := WP.spec_imp_exists (Array.index_usize_spec bytes index inside)
    have safe : index.val + (1#usize).val ≤ Usize.max := by scalar_tac
    obtain ⟨next,add,increased⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) safe)
    have nextBound : next.val + fuel = 32 := by
      have one : (1#usize).val = 1 := by scalar_tac
      omega
    obtain ⟨out,tail⟩ := ih (combined ||| value) next nextBound
    refine ⟨out,?_⟩
    unfold entropy_nonzero32_loop
    rw [loop]
    simp only [entropy_nonzero32_loop.body,go,if_true,read,lift,bind_tc_ok,add]
    exact tail

theorem nonzero_total (bytes : Array U8 32#usize) :
    ∃ out, entropy_nonzero32 bytes = .ok out := by
  obtain ⟨combined,scan⟩ := scan_total bytes 0#u8 0#usize 32 (by rfl)
  exact ⟨combined != 0#u8,by simp only [entropy_nonzero32,scan,bind_tc_ok]⟩

#print axioms scan_total
#print axioms nonzero_total
end R1Z.PV_RunJoin_EntropyTotal
