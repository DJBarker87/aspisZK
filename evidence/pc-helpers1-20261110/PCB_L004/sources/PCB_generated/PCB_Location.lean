import PCB_Reference.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCB_Location

def model (n : Nat) : Nat × Nat := (n / 256, n % 256)

theorem result (n : U64) :
    ∃ out, PCB_Reference.location n = ok out ∧
      (out.page_number.val, out.slot.val) = model n.val := by
  obtain ⟨q,hq,vq⟩ := UScalar.div_spec (x := n) (y := 256#u64) (by decide)
  obtain ⟨r,hr,vr⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x := n) (y := 256#u64) (by decide))
  have rsmall : r.val < 256 := by simpa using (vr ▸ Nat.mod_lt n.val (by decide))
  refine ⟨{page_number := q, slot := UScalar.cast .U16 r}, ?_, ?_⟩
  · simp only [PCB_Reference.location, hq, hr, bind_tc_ok, lift, pure]
  · simp only [model, Prod.mk.injEq]
    constructor
    · simpa using vq
    · scalar_tac

#print axioms result
end PCB_Location
