import NNV_FinishCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FromFnBounded
open Aeneas Aeneas.Std Result

theorem loop {C T : Type} (f : core.ops.function.FnMut C Usize T) (c : C)
 (g : Usize → T) (indices : List Usize)
 (calls : ∀ i ∈ indices, f.call_mut c i = .ok (g i,c)) :
 OraclePortStdBuilder.fromFnLoop f indices c = .ok (indices.map g,c) := by
 induction indices with
 | nil => rfl
 | cons i is ih =>
  rw [OraclePortStdBuilder.fromFnLoop,calls i (by simp),bind_tc_ok]
  rw [ih (fun j hj => calls j (by simp [hj])),bind_tc_ok]
  rfl

theorem source {C T : Type} (n : Usize) (f : core.ops.function.FnMut C Usize T) (c : C)
 (g : Usize → T)
 (calls : ∀ i ∈ OraclePortStdBuilder.indices n, f.call_mut c i = .ok (g i,c)) :
 OraclePortStdBuilder.fromFn n f c = .ok (Array.make n
  ((OraclePortStdBuilder.indices n).map g) (by simp [OraclePortStdBuilder.indices])) := by
 unfold OraclePortStdBuilder.fromFn
 rw [loop f c g _ calls,bind_tc_ok]
 simp only [List.length_map,OraclePortStdBuilder.indices,List.length_ofFn,dif_pos]
 rfl
#print axioms loop
#print axioms source
end AspisR1.NNV_FromFnBounded
end
