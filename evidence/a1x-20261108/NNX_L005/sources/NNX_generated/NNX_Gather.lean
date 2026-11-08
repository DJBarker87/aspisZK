import NNV_FinishClaims
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_Gather
open Aeneas Aeneas.Std Result
/-- A finite read-only gather needs a law only at its reached indices and
SAME state, rather than a total callback law over unrelated states. -/
theorem loop {C T : Type} (f : core.ops.function.FnMut C Usize T)
 (c : C) (indices : List Usize) (g : Usize → T)
 (step : ∀ i ∈ indices, f.call_mut c i = .ok (g i,c)) :
 OraclePortStdBuilder.fromFnLoop f indices c = .ok (indices.map g,c) := by
 induction indices with
 | nil => rfl
 | cons i rest ih =>
  simp only [OraclePortStdBuilder.fromFnLoop,step i (by simp),bind_tc_ok,
   ih (fun j hj => step j (by simp [hj])),List.map_cons]

theorem array {C T : Type} [Inhabited T] (n : Usize) (f : core.ops.function.FnMut C Usize T)
 (c : C) (out : Array T n)
 (step : ∀ i ∈ OraclePortStdBuilder.indices n,
  f.call_mut c i = .ok (out.val[i.val]!,c)) :
 OraclePortStdBuilder.fromFn n f c = .ok out := by
 unfold OraclePortStdBuilder.fromFn
 have length := out.property
 have map : (OraclePortStdBuilder.indices n).map (fun i => out.val[i.val]!) = out.val := by
  apply List.ext_getElem
  · simp [OraclePortStdBuilder.indices,length]
  · intro j h1 h2
    simp [OraclePortStdBuilder.indices,List.getElem_ofFn,List.getElem_map,getElem!_pos,h2]
 rw [loop f c _ _ step,map]
 simp only [bind_tc_ok,length,dif_pos]
#print axioms loop
#print axioms array
end AspisR1.NNX_Gather
end
