import R1Z.PV_RunJoin_CircleNeutralRange53
import R1Z.PV_RunJoin_CircleNeutralFinite53
import R1Z.ProverRw19LoopBind
import R1Z.PV_RunJoin_CircleNeutralSquareEquation53
import R1Z.PV_RunJoin_CircleNeutralSquareCell53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralSquareLoop53
open PV_RunJoin_CircleNeutralFinite53 PV_RunJoin_CircleNeutralRange53

theorem owned (n : Nat) (r : core.ops.range.Range Usize) (a : U32)
    (hr : r.end.val=r.start.val+n) :
    PV_RunJoin_CircleRawScalar52.field.square_n_loop r a = finite n a := by
  induction n generalizing r a with
  | zero =>
    have hn := next_none r (by omega)
    rw [PV_RunJoin_CircleNeutralSquareEquation53.owned]
    simp only [PV_RunJoin_CircleRawScalar52.field.square_n_loop.body,hn,bind_tc_ok,finite]
    rfl
  | succ n ih =>
    obtain ⟨after,hn,hs,he⟩ := next_some r (by omega)
    have hafter : after.end.val=after.start.val+n := by rw [he];omega
    rw [PV_RunJoin_CircleNeutralSquareEquation53.owned]
    rw [PV_RunJoin_CircleNeutralSquareCell53.owned r after a hn]
    simp only [bind_assoc_eq,bind_tc_ok]
    change (do let v ← PV_RunJoin_CircleRawScalar52.field.M31.mul a a
               PV_RunJoin_CircleRawScalar52.field.square_n_loop after v) = finite (n+1) a
    rw [finite]
    apply congrArg (Aeneas.Std.bind (PV_RunJoin_CircleRawScalar52.field.M31.mul a a))
    funext v
    exact ih after v hafter

theorem model (n : Nat) (r : core.ops.range.Range Usize) (a : U32)
    (hr : r.end.val=r.start.val+n) :
    PV_RunJoin_CircleR72Raw52.field.square_n_loop r a = PV_RunJoin_CircleNeutralFinite53.model n a := by
  induction n generalizing r a with
  | zero =>
    have hn := next_none r (by omega)
    rw [PV_RunJoin_CircleNeutralSquareEquation53.model]
    simp only [PV_RunJoin_CircleR72Raw52.field.square_n_loop.body,hn,bind_tc_ok,PV_RunJoin_CircleNeutralFinite53.model]
    rfl
  | succ n ih =>
    obtain ⟨after,hn,hs,he⟩ := next_some r (by omega)
    have hafter : after.end.val=after.start.val+n := by rw [he];omega
    rw [PV_RunJoin_CircleNeutralSquareEquation53.model]
    rw [PV_RunJoin_CircleNeutralSquareCell53.model r after a hn]
    simp only [bind_assoc_eq,bind_tc_ok]
    change (do let v ← PV_RunJoin_CircleR72Raw52.field.M31.mul a a
               PV_RunJoin_CircleR72Raw52.field.square_n_loop after v) = PV_RunJoin_CircleNeutralFinite53.model (n+1) a
    rw [PV_RunJoin_CircleNeutralFinite53.model]
    apply congrArg (Aeneas.Std.bind (PV_RunJoin_CircleR72Raw52.field.M31.mul a a))
    funext v
    exact ih after v hafter

#print axioms owned
#print axioms model
end R1Z.PV_RunJoin_CircleNeutralSquareLoop53
