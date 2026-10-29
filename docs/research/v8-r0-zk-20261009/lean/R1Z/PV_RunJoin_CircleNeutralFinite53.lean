import R1Z.PV_RunJoin_CircleNeutralMul53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralFinite53
open PV_RunJoin_CircleNeutralShape53

def finite : Nat → U32 → Result U32
  | 0,a => ok a
  | n+1,a => do
      let b ← PV_RunJoin_CircleRawScalar52.field.M31.mul a a
      finite n b

def model : Nat → U32 → Result U32
  | 0,a => ok a
  | n+1,a => do
      let b ← PV_RunJoin_CircleR72Raw52.field.M31.mul a a
      model n b

theorem total (n : Nat) (a : U32) (ha : Canon a) :
    ∃ y, finite n a = ok y ∧ model n a = ok y ∧ Canon y := by
  induction n generalizing a with
  | zero => exact ⟨a,rfl,rfl,ha⟩
  | succ n ih =>
    obtain ⟨b,hb,hb',hc⟩ := PV_RunJoin_CircleNeutralMul53.complete a a ha ha
    obtain ⟨y,hy,hy',hc'⟩ := ih b hc
    exact ⟨y,by simp only [finite,hb,bind_tc_ok,hy],
      by simp only [model,hb',bind_tc_ok,hy'],hc'⟩

#print axioms finite
#print axioms model
#print axioms total
end R1Z.PV_RunJoin_CircleNeutralFinite53
