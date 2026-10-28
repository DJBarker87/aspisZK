import R1Z.PV_RunJoin_WeightConstructorThread46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightConstructorShape46
open Aeneas Aeneas.Std Result
open PV_B2_C_ConstructorRows (Points Factors row0_total row1_total row2_total row3_total row4_total)
open PV_B2_C_WeightsNative
open PV_RunJoin_WeightConstructorThread46

def seed : Factors := Array.repeat 5#usize
  (Array.repeat 5#usize (Array.repeat 4#usize aspis_core.field.QM31.ZERO))

theorem rows_total (p : Points) (z : Array Point 2#usize) (f : Factors) :
    ∃ out, rows p z f=ok out := by
  obtain ⟨f0,h0⟩ := row0_total f p
  obtain ⟨f1,h1⟩ := row1_total f0 p
  obtain ⟨f2,h2⟩ := row2_total f1 p
  obtain ⟨f3,h3⟩ := row3_total f2 z
  obtain ⟨f4,h4⟩ := row4_total f3 z
  exact ⟨f4,by simp only [rows,h0,h1,h2,h3,h4,bind_tc_ok]⟩

theorem complete (v : V) (alpha : Array K 10#usize) (z : Array Point 2#usize) :
    ∃ p a8 a9 f,
      host_weights.state_only_statement_points alpha=ok p ∧
      Array.index_usize alpha 8#usize=ok a8 ∧
      Array.index_usize alpha 9#usize=ok a9 ∧
      rows p z seed=ok f ∧
      host_weights.Weights.new v alpha z=
        ok (.Ok ({variant:=v,factors:=f,points:=p,extra:=Array.make 2#usize [a8,a9]} : host_weights.Weights)) := by
  obtain ⟨p,hp⟩ := PV_B2_C_WeightsTotal.points alpha
  obtain ⟨a8,h8⟩ := PV_B2_C_ArrayTotal.read alpha 8#usize (by decide)
  obtain ⟨a9,h9⟩ := PV_B2_C_ArrayTotal.read alpha 9#usize (by decide)
  obtain ⟨f,hf⟩ := rows_total p z seed
  refine ⟨p,a8,a9,f,hp,h8,h9,hf,?_⟩
  rw [PV_RunJoin_WeightConstructorThread46.complete]
  change run v alpha z=_
  unfold seed at hf
  simp only [run,hp,h8,h9,hf,bind_tc_ok]

#print axioms rows_total
#print axioms complete
end R1Z.PV_RunJoin_WeightConstructorShape46
