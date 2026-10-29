import R1Z.PV_RunJoin_CircleNeutralWide53
import R1Z.PV_RunJoin_NeutralCMulWord54
import R1Z.PV_RunJoin_NeutralMulValue54
import R1Z.PV_RunJoin_NeutralSubValue54
import R1Z.PV_RunJoin_NeutralReduceValue54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_NeutralCMulValue54
open PV_RunJoin_NeutralValue54 PV_RunJoin_NeutralTowerValue54 PV_RunJoin_CircleNeutralShape53

theorem complete (a b : C) (ha : CC a) (hb : CC b) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.CM31.mul a b=ok y ∧ CC y ∧ cv y=cm (cv a) (cv b) := by
  obtain ⟨m0,h0,hc0,hv0⟩ := PV_RunJoin_NeutralMulValue54.complete a.1 b.1 ha.1 hb.1
  obtain ⟨m1,h1,hc1,hv1⟩ := PV_RunJoin_NeutralMulValue54.complete a.2 b.2 ha.2 hb.2
  obtain ⟨m2,h2,hc2,hv2⟩ := PV_RunJoin_NeutralReduceValue54.complete (PV_RunJoin_NeutralCMulWord54.word a b)
  obtain ⟨y0,h3,hc3,hv3⟩ := PV_RunJoin_NeutralSubValue54.complete m0 m1 hc0 hc1
  obtain ⟨t,h4,hc4,hv4⟩ := PV_RunJoin_NeutralSubValue54.complete m2 m0 hc2 hc0
  obtain ⟨y1,h5,hc5,hv5⟩ := PV_RunJoin_NeutralSubValue54.complete t m1 hc4 hc1
  refine ⟨(y0,y1),?_,⟨hc3,hc5⟩,?_⟩
  · unfold PV_RunJoin_CircleRawTower52.field.CM31.mul
    simp only [h0,h1,lift,bind_tc_ok,PV_RunJoin_CircleNeutralWide53.from32,
      PV_RunJoin_CircleNeutralWrappers53.add64]
    change (do
      let z ← PV_RunJoin_CircleRawScalar52.field.M31.reduce_u64 (PV_RunJoin_NeutralCMulWord54.word a b)
      let r ← PV_RunJoin_CircleRawScalar52.field.M31.sub m0 m1
      let t ← PV_RunJoin_CircleRawScalar52.field.M31.sub z m0
      let q ← PV_RunJoin_CircleRawScalar52.field.M31.sub t m1
      ok (r,q))=ok (y0,y1)
    simp only [h2,h3,h4,h5,bind_tc_ok]
  · apply Prod.ext
    · exact hv3.trans (congrArg₂ (· - ·) hv0 hv1)
    · change scalar y1=scalar a.1*scalar b.2+scalar a.2*scalar b.1
      rw [hv5,hv4,hv2,PV_RunJoin_NeutralCMulWord54.value a b ha hb,hv0,hv1]
      simp only [Nat.cast_mul,Nat.cast_add]
      unfold scalar
      ring
#print axioms complete
end R1Z.PV_RunJoin_NeutralCMulValue54
