import PCB_AppendRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCB_AppendScalarLaws

theorem geometry (filled : U16) (offset : Usize)
    (cap : filled.val + offset.val < 256) :
    ∃ out, PCB_AppendRef.geometry filled offset = ok out ∧
      out.val = 64 + 32 * (filled.val + offset.val) := by
  let i := core.convert.num.FromUsizeU16.from filled
  have vi : i.val = filled.val := core.convert.num.FromUsizeU16.from_val_eq filled
  obtain ⟨slot,hs,vs⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=i) (y:=offset) (by scalar_tac))
  obtain ⟨mul,hm,vm⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x:=slot) (y:=32#usize) (by scalar_tac))
  obtain ⟨out,ho,vo⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=64#usize) (y:=mul) (by scalar_tac))
  refine ⟨out,?_,?_⟩
  · simp only [PCB_AppendRef.geometry, lift, bind_tc_ok]
    change (do let s ← i + offset; let m ← s * 32#usize; 64#usize + m) = ok out
    rw [hs]; simp only [bind_tc_ok]; rw [hm]; simp only [bind_tc_ok]; exact ho
  · scalar_tac

theorem filled (n : U16) (count : Usize)
    (cap : n.val + count.val ≤ 256) :
    ∃ out, PCB_AppendRef.filled_bytes n count =
      ok (core.num.U16.to_le_bytes out) ∧ out.val = n.val + count.val := by
  let i := UScalar.cast .U16 count
  have vi : i.val = count.val := by dsimp [i]; scalar_tac
  obtain ⟨out,ho,vo⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=n) (y:=i) (by scalar_tac))
  refine ⟨out,?_,?_⟩
  · simp only [PCB_AppendRef.filled_bytes,lift,bind_tc_ok]
    change (do let f ← n + i; ok (core.num.U16.to_le_bytes f)) = _
    rw [ho]; rfl
  · scalar_tac

#print axioms geometry
#print axioms filled
end PCB_AppendScalarLaws
