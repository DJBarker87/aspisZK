import R1Z.PV_RunJoin_NeutralValue54
import R1Z.PV_RunJoin_CircleNeutralSub53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_NeutralSubValue54
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_NeutralValue54 PV_RunJoin_CircleNeutralWord53

theorem complete (a b : U32) (ha : Canon a) (hb : Canon b) :
    ∃ y, PV_RunJoin_CircleRawScalar52.field.M31.sub a b=ok y ∧
      Canon y ∧ scalar y=scalar a-scalar b := by
  have av : a.val<2147483647 := ha
  have bv : b.val<2147483647 := hb
  have hsum : (U32.wrapping_add a 2147483647#u32).val=a.val+2147483647 :=
    add32 _ _ (by change a.val+2147483647<4294967296;omega)
  have hle : b.val≤(U32.wrapping_add a 2147483647#u32).val := by rw [hsum];omega
  have hv : (U32.wrapping_sub (U32.wrapping_add a 2147483647#u32) b).val=a.val+2147483647-b.val := by
    rw [sub32 _ _ hle,hsum]
  have hsmall : (U32.wrapping_sub (U32.wrapping_add a 2147483647#u32) b).val<4294967294 := by rw [hv];omega
  let y := PV_RunJoin_CircleNeutralSubtract53.output (U32.wrapping_sub (U32.wrapping_add a 2147483647#u32) b)
  have hy : PV_RunJoin_CircleRawScalar52.field.M31.sub a b=ok y := by
    unfold PV_RunJoin_CircleRawScalar52.field.M31.sub PV_RunJoin_CircleRawScalar52.field.ct.sub PV_RunJoin_CircleRawScalar52.field.P
    simp only [lift,bind_tc_ok,PV_RunJoin_CircleNeutralWrappers53.add32,
      PV_RunJoin_CircleNeutralWrappers53.sub32,PV_RunJoin_CircleNeutralSubtract53.source,y]
  refine ⟨y,hy,PV_RunJoin_CircleNeutralSubtract53.canonical _ hsmall,?_⟩
  change scalar (PV_RunJoin_CircleNeutralSubtract53.output _)=_
  rw [subtract _ hsmall]
  unfold scalar
  rw [hv,Nat.cast_sub (by omega),Nat.cast_add,prime_zero,add_zero]
#print axioms complete
end R1Z.PV_RunJoin_NeutralSubValue54
