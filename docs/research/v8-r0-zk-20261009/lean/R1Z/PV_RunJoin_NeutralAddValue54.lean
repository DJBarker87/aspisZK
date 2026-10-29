import R1Z.PV_RunJoin_NeutralValue54
import R1Z.PV_RunJoin_CircleNeutralAddCanon53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_NeutralAddValue54
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_NeutralValue54 PV_RunJoin_CircleNeutralWord53

theorem complete (a b : U32) (ha : Canon a) (hb : Canon b) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.add a b=ok y ∧
      Canon y ∧ scalar y=scalar a+scalar b := by
  have sum : a.val+b.val<4294967294 := by unfold Canon at ha hb;omega
  have hv : (U32.wrapping_add a b).val=a.val+b.val := add32 _ _ (by omega)
  let y := PV_RunJoin_CircleNeutralSubtract53.output (U32.wrapping_add a b)
  have hy : PV_RunJoin_CircleRawScalar52.field.M31.add a b=ok y := by
    unfold PV_RunJoin_CircleRawScalar52.field.M31.add PV_RunJoin_CircleRawScalar52.field.ct.add
    simp only [lift,bind_tc_ok,PV_RunJoin_CircleNeutralWrappers53.add32,
      PV_RunJoin_CircleNeutralSubtract53.source,y]
  refine ⟨y,hy,PV_RunJoin_CircleNeutralSubtract53.canonical _ (by rw [hv];exact sum),?_⟩
  change scalar (PV_RunJoin_CircleNeutralSubtract53.output (U32.wrapping_add a b))=_
  rw [subtract _ (by rw [hv];exact sum)]
  unfold scalar
  rw [hv,Nat.cast_add]
#print axioms complete
end R1Z.PV_RunJoin_NeutralAddValue54
