import R1Z.PV_RunJoin_CoefficientList50
import R1Z.PV_RunJoin_Vector44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientListResult50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_CoefficientActualCell50 (Column permuted)

theorem complete (columns : List Column) (out : alloc.vec.Vec Column)
    (room : out.length+columns.length≤Usize.max) :
    ∃ next, PV_RunJoin_CoefficientList50.run columns out=ok next ∧
      next.val=out.val ++ columns.map permuted := by
  induction columns generalizing out with
  | nil => exact ⟨out,rfl,by rw [List.map_nil,List.append_nil]⟩
  | cons q tail ih =>
    obtain ⟨mid,hm,hv⟩ := PV_RunJoin_Vector44.push out (permuted q) (by simp only [List.length_cons] at room;omega)
    have length : mid.length=out.length+1 := by
      change mid.val.length=out.val.length+1
      rw [hv,List.length_append,List.length_singleton]
    obtain ⟨next,hn,hnext⟩ := ih mid (by rw [length];simp only [List.length_cons] at room;omega)
    refine ⟨next,?_,?_⟩
    · simp only [PV_RunJoin_CoefficientList50.run,hm,bind_tc_ok,hn]
    · rw [hnext,hv,List.map_cons,List.append_assoc,List.singleton_append]
#print axioms complete
end R1Z.PV_RunJoin_CoefficientListResult50
