import FIv_Arithmetic
import OraclePortStdBuilder
set_option autoImplicit false
namespace AspisR1.FIw_BuilderValue
open Aeneas Aeneas.Std Result

theorem loop {T C V : Type} (f : core.ops.function.FnMut C Usize T)
    (observe : T → V) (model : C → Usize → V)
    (step : ∀ c i x c',f.call_mut c i=ok (x,c') → observe x=model c i ∧ c'=c)
    (is : List Usize) (c : C) (xs : List T) (last : C)
    (run : OraclePortStdBuilder.fromFnLoop f is c=ok (xs,last)) :
    xs.map observe=is.map (model c) ∧ last=c := by
  induction is generalizing c xs last with
  | nil =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
    exact ⟨rfl,rfl⟩
  | cons i is ih =>
    unfold OraclePortStdBuilder.fromFnLoop at run
    obtain ⟨⟨x,c'⟩,call,r1⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨⟨ys,last'⟩,tail,r2⟩ := FIv_Map.bind_success _ _ _ r1
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj r2)
    obtain ⟨vx,rfl⟩ := step c i x c' call
    have rest := ih c ys last' tail
    exact ⟨by simp only [List.map_cons,vx,rest.1],rest.2⟩

theorem fromFn {T C V : Type} (n : Usize) (f : core.ops.function.FnMut C Usize T)
    (observe : T → V) (model : C → Usize → V)
    (step : ∀ c i x c',f.call_mut c i=ok (x,c') → observe x=model c i ∧ c'=c)
    (c : C) (out : Array T n) (run : OraclePortStdBuilder.fromFn n f c=ok out) :
    out.val.map observe=(OraclePortStdBuilder.indices n).map (model c) := by
  unfold OraclePortStdBuilder.fromFn at run
  obtain ⟨⟨xs,last⟩,called,r1⟩ := FIv_Map.bind_success _ _ _ run
  split at r1
  · have eq := congrArg Subtype.val (Result.ok.inj r1)
    rw [← eq]
    exact (loop f observe model step _ c xs last called).1
  · cases r1
#print axioms loop
#print axioms fromFn
end AspisR1.FIw_BuilderValue
