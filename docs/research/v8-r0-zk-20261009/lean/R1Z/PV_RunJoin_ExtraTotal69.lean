import R1Z.PV_RunJoin_NativeQuarticTotal69
import R1Z.PV_RunJoin_SamplerCounters54
import R1Z.ProverRwP6ArrayRead
import R1Z.ProverRw19LoopBind
import R1Z.PV_RunJoin_CompactStep39
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ExtraTotal69
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31

/-- Reusable totality requirements; the native instance is derived below. -/
structure Arithmetic : Prop where
  add : ∀ a b : Q, ∃ c, aspis_core.field.QM31.add a b=ok c
  mul : ∀ a b : Q, ∃ c, aspis_core.field.QM31.mul a b=ok c
  zero : ∃ c, aspis_core.field.QM31.ZERO=ok c

theorem offset (side j : Usize) (hs : side.val<2) (hj : j.val<28) :
    (Usize.wrapping_add (Usize.wrapping_mul 28#usize side) j).val<1024 := by
  have size : 1024<UScalar.size .Usize := by scalar_tac
  have hm : (Usize.wrapping_mul 28#usize side).val=28*side.val := by
    rw [Usize.wrapping_mul_val_eq]
    change (28*side.val)%UScalar.size .Usize=28*side.val
    exact Nat.mod_eq_of_lt (by omega)
  rw [Usize.wrapping_add_val_eq,hm]
  change (28*side.val+j.val)%UScalar.size .Usize<1024
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem inner (law : Arithmetic) (coefficients : Array Q 1024#usize)
    (side : Usize) (hs : side.val<2) (x value : Q)
    (n : Nat) (j : Usize) (hj : j.val=n) (bound : n≤28) :
    ∃ out, host_semantic.extra_loop0_loop0 coefficients side value x j=ok out := by
  induction n generalizing value j with
  | zero =>
    have stop : ¬j>0#usize := by change ¬j.val>0;omega
    unfold host_semantic.extra_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.extra_loop0_loop0.body,stop,if_false,bind_tc_ok]
    exact ⟨value,rfl⟩
  | succ n ih =>
    have more : j>0#usize := by change j.val>0;omega
    have dec : (Usize.wrapping_sub j 1#usize).val=n := by
      rw [PV_RunJoin_SamplerCounters54.sub_one j (by omega)];omega
    obtain ⟨q,hq⟩ := law.mul value x
    obtain ⟨v,hv⟩ := ProverRwP6ArrayRead.read coefficients
      (Usize.wrapping_add (Usize.wrapping_mul 28#usize side) (Usize.wrapping_sub j 1#usize))
      (by apply offset side _ hs;rw [dec];omega)
    obtain ⟨next,hn⟩ := law.add q v
    obtain ⟨out,ho⟩ := ih next (Usize.wrapping_sub j 1#usize) dec (by omega)
    refine ⟨out,?_⟩
    unfold host_semantic.extra_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.extra_loop0_loop0.body,more,if_true,lift,hq,hv,hn,bind_tc_ok]
    exact ho

theorem outer (law : Arithmetic) (coefficients : Array Q 1024#usize)
    (a b zero sum : Q) (n : Nat) (side : Usize) (rank : side.val+n=2) :
    ∃ out, host_semantic.extra_loop0 zero coefficients a b sum side=ok out := by
  induction n generalizing sum side with
  | zero =>
    have stop : ¬side<2#usize := by change ¬side.val<2;omega
    unfold host_semantic.extra_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.extra_loop0.body,stop,if_false,bind_tc_ok]
    exact ⟨sum,rfl⟩
  | succ n ih =>
    have more : side<2#usize := by change side.val<2;omega
    let x := if side=0#usize then a else b
    have hx : (if side=0#usize then ok a else ok b)=ok x := by
      dsimp only [x];split <;> rfl
    obtain ⟨value,hv⟩ := inner law coefficients side more x zero 28 28#usize rfl (by omega)
    obtain ⟨next,hn⟩ := law.add sum value
    have inc := PV_RunJoin_SamplerCounters54.increment side (by change side.val<32;omega)
    obtain ⟨out,ho⟩ := ih next (Usize.wrapping_add side 1#usize) (by rw [inc];omega)
    refine ⟨out,?_⟩
    unfold host_semantic.extra_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.extra_loop0.body,more,if_true,hx,hv,hn,lift,bind_tc_ok]
    exact ho

theorem complete (law : Arithmetic) (coefficients : Array Q 1024#usize) (a b : Q) :
    ∃ out,host_semantic.extra coefficients a b=ok out := by
  obtain ⟨zero,hz⟩ := law.zero
  obtain ⟨out,ho⟩ := outer law coefficients a b zero zero 2 0#usize rfl
  exact ⟨out,by simp only [host_semantic.extra,hz,bind_tc_ok,ho]⟩

#print axioms Arithmetic
#print axioms offset
#print axioms inner
#print axioms outer
#print axioms complete
end R1Z.PV_RunJoin_ExtraTotal69
