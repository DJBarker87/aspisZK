import R1Z.PV_RunJoin_FibreFillThread43
import R1Z.PV_RunJoin_QueryLaneTotal64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryMatrixTotal64
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FibreFillThread43 (Matrix W)

def put (values : Matrix) (row lane : Usize) (x : W) : Result Matrix := do
  let (a,back) ← Array.index_mut_usize values row
  let a' ← Array.update a lane x
  ok (back a')

theorem total (values : Matrix) (row lane : Usize) (x : W)
    (rowBound : row.val<4) (laneBound : lane.val<29) :
    ∃ next, put values row lane x=ok next := by
  obtain ⟨⟨a,back⟩,hr,hpost⟩ := WP.spec_imp_exists
    (Array.index_mut_usize_spec values row (by simpa only [Array.length,values.property] using rowBound))
  obtain ⟨a',ha,hvalue⟩ := WP.spec_imp_exists (Array.update_spec a lane x (by simpa only [Array.length,a.property] using laneBound))
  refine ⟨back a',?_⟩
  simp only [put,hr,ha,bind_tc_ok,Aeneas.Std.uncurry]

#print axioms put
#print axioms total
end R1Z.PV_RunJoin_QueryMatrixTotal64
