import R1Z.PV_RunJoin_R24Decompose54
import R1Z.PV_RunJoin_R24Inputs54
import R1Z.PV_RunJoin_R24Residue0_54
import R1Z.PV_RunJoin_R24Residue1_54
import R1Z.PV_RunJoin_R24Residue2_54
import R1Z.PV_RunJoin_R24Residue3_54
import R1Z.PV_RunJoin_CircleNeutralR24Prefix53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Canonical54
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_R24Inputs54
abbrev Q := (U32 × U32) × (U32 × U32)
theorem complete (a b : Q) (ha : QC a) (hb : QC b) :
    ∃ y : Q, PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul a b=ok (some y) ∧ QC y ∧
      y.1.1.val=PV_RunJoin_R24Equation0_54.accumulator a b (u a b) (v a b)%2147483647 ∧
      y.1.2.val=PV_RunJoin_R24Equation1_54.accumulator a b (u a b) (v a b)%2147483647 ∧
      y.2.1.val=PV_RunJoin_R24Equation2_54.accumulator a b (u a b) (v a b)%2147483647 ∧
      y.2.2.val=PV_RunJoin_R24Equation3_54.accumulator a b (u a b) (v a b)%2147483647 := by
  have hbound := bounds a b ha hb
  obtain ⟨x0,h0,hc0,hv0⟩ := PV_RunJoin_R24Residue0_54.complete a b ha hb _ _ hbound.1 hbound.2
  obtain ⟨x1,h1,hc1,hv1⟩ := PV_RunJoin_R24Residue1_54.complete a b ha hb _ _ hbound.1 hbound.2
  obtain ⟨x2,h2,hc2,hv2⟩ := PV_RunJoin_R24Residue2_54.complete a b ha hb _ _ hbound.1 hbound.2
  obtain ⟨x3,h3,hc3,hv3⟩ := PV_RunJoin_R24Residue3_54.complete a b ha hb _ _ hbound.1 hbound.2
  refine ⟨((x0,x1),(x2,x3)),?_,⟨⟨hc0,hc1⟩,⟨hc2,hc3⟩⟩,hv0,hv1,hv2,hv3⟩
  rw [PV_RunJoin_CircleNeutralR24Prefix53.complete a b ha hb,PV_RunJoin_R24Decompose54.complete]
  change (do
    let c0 ← PV_RunJoin_R24Cell0_54.cell a b _ _
    let c1 ← PV_RunJoin_R24Cell1_54.cell a b _ _
    let c2 ← PV_RunJoin_R24Cell2_54.cell a b _ _
    let c3 ← PV_RunJoin_R24Cell3_54.cell a b _ _
    let lo ← PV_RunJoin_CircleR72Raw52.field.CM31.new c0 c1
    let hi ← PV_RunJoin_CircleR72Raw52.field.CM31.new c2 c3
    ok (some (lo,hi)))=ok _
  unfold u v at h0 h1 h2 h3
  rw [h0,bind_tc_ok,h1,bind_tc_ok,h2,bind_tc_ok,h3,bind_tc_ok]
  rfl
#print axioms complete
end R1Z.PV_RunJoin_R24Canonical54
