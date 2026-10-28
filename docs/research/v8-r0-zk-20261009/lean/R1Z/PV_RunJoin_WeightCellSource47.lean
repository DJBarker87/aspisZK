import R1Z.PV_RunJoin_WeightCellFold47
import R1Z.PV_RunJoin_WeightReadFold47
import R1Z.PV_RunJoin_WeightRowArray46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCellSource47
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_RunJoin_WeightWide46 (E toWide)
open PV_B2_F_ConstructorCarrier (amap)
open PV_RunJoin_WeightMap46 (mapResult)
abbrev Powers := PV_B2_C_MutationStep.Powers

def powerArray (k : Powers) : Array E 7#usize :=
  let (k0,k1,k2,k3,k4,k5,k6) := k
  Array.make 7#usize [k0,k1,k2,k3,k4,k5,k6]

theorem powers_elim (k0 k1 k2 k3 k4 k5 k6 : E)
    (f : E → E → E → E → E → E → E → Result E) :
    (let (a,b,c,d,e,f0,g) := (k0,k1,k2,k3,k4,k5,k6); f a b c d e f0 g)=
      f k0 k1 k2 k3 k4 k5 k6 := by rfl
#print axioms powers_elim

attribute [local irreducible] PV_B2_251c1.host_weights.mul_qm31
  PV_B2_251c1.aspis_core.field.wide_exact.WideExact.add

theorem complete (w : W) (hs : w.variant=.S2) (k : Powers) (j : Usize) (hj : j.val<1024) :
    ∃ row : Array Q 7#usize,
      PV_RunJoin_WeightRowArray46.run w j=ok row ∧
      AspisR1ProducerRelease47.weights53.row (state w) j=ok (amap toQ row) ∧
      PV_B2_251c1.host_weights.materialize_cell w k j=
        PV_RunJoin_WeightCell46.finite 7 (powerArray k) row 0#usize
          PV_B2_251c1.aspis_core.field.wide_exact.WideExact.ZERO ∧
      AspisR1ProducerRelease47.owned.cell (amap toWide (powerArray k)) (amap toQ row)
        0#usize 7#u8 AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO=
        mapResult toWide (PV_B2_251c1.host_weights.materialize_cell w k j) := by
  rcases k with ⟨k0,k1,k2,k3,k4,k5,k6⟩
  obtain ⟨q0,h0⟩ := PV_B2_D_RawTotal.source w 0#usize j (by decide) hj
  obtain ⟨q1,h1⟩ := PV_B2_D_RawTotal.source w 1#usize j (by decide) hj
  obtain ⟨q2,h2⟩ := PV_B2_D_RawTotal.source w 2#usize j (by decide) hj
  obtain ⟨q3,h3⟩ := PV_B2_D_RawTotal.source w 3#usize j (by decide) hj
  obtain ⟨q4,h4⟩ := PV_B2_D_RawTotal.source w 4#usize j (by decide) hj
  obtain ⟨q5,h5⟩ := PV_B2_D_RawTotal.source w 5#usize j (by decide) hj
  obtain ⟨q6,h6⟩ := PV_B2_D_RawTotal.source w 6#usize j (by decide) hj
  let row : Array Q 7#usize := Array.make 7#usize [q0,q1,q2,q3,q4,q5,q6]
  have hr : PV_RunJoin_WeightRowArray46.run w j=ok row := by
    dsimp only [row]
    simp only [PV_RunJoin_WeightRowArray46.run,h0,h1,h2,h3,h4,h5,h6,bind_tc_ok]
  have hm : AspisR1ProducerRelease47.weights53.row (state w) j=ok (amap toQ row) := by
    rw [PV_RunJoin_WeightRowArray46.complete w hs,hr]
    rfl
  have hc : PV_B2_251c1.host_weights.materialize_cell w (k0,k1,k2,k3,k4,k5,k6) j=
      PV_RunJoin_WeightCell46.finite 7 (powerArray (k0,k1,k2,k3,k4,k5,k6)) row 0#usize
        PV_B2_251c1.aspis_core.field.wide_exact.WideExact.ZERO := by
    rw [PV_B2_F_CellFold.source,PV_RunJoin_WeightCellFold47.source]
    dsimp only [PV_B2_F_CellFold.ordered,powerArray,row]
    rw [PV_RunJoin_WeightCellFold47.seven]
    apply PV_RunJoin_WeightReadFold47.map_read
      (fun i => PV_B2_251c1.host_weights.raw_value w i j)
      PV_B2_251c1.host_weights.mul_qm31
      PV_B2_251c1.aspis_core.field.wide_exact.WideExact.add
    exact .cons ⟨rfl,h0⟩ (.cons ⟨rfl,h1⟩ (.cons ⟨rfl,h2⟩
      (.cons ⟨rfl,h3⟩ (.cons ⟨rfl,h4⟩ (.cons ⟨rfl,h5⟩ (.cons ⟨rfl,h6⟩ .nil))))))
  refine ⟨row,hr,hm,hc,?_⟩
  rw [PV_RunJoin_WeightCellIndices46.zero]
  exact (PV_RunJoin_WeightCell46.complete 7 _ row 0#usize 7#u8 rfl _).trans
    (congrArg (mapResult toWide) hc.symm)
#print axioms complete
end R1Z.PV_RunJoin_WeightCellSource47
