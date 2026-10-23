import Port4C_Reverse
import Port4C_OwnedInverse

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_InverseLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
open Port3_PushFrame (bind_success)
variable {CoreError : Type}

/-- CURRENT native backward iterator and Vec writes preserve the complete
owned inverse result. The sole primitive multiply port is session A-owned. -/
theorem from_owned (ops : Ops CoreError)
    (multiply : ops.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (flat prefixes inverse out : alloc.vec.Vec U32) (suffix : U32) (index : Usize)
    (bound : index.val≤110)
    (h : Port4C_OwnedInverse.inverse_owned flat prefixes inverse suffix index=ok out) :
    verifier.QueryGeometry.for_range_loop0_loop0 ops (Port4C_Reverse.reverse index)
      flat prefixes suffix inverse=ok out := by
  generalize hn : index.val=n at *
  induction n generalizing index inverse suffix with
  | zero =>
    have same : index=0#usize := UScalar.eq_of_val_eq hn
    subst index
    rw [Port4C_OwnedInverse.inverse_owned] at h
    simp only [if_pos rfl] at h
    have same := Result.ok.inj h
    subst out
    have bodyRun : verifier.QueryGeometry.for_range_loop0_loop0.body ops flat prefixes
        (Port4C_Reverse.reverse 0#usize) suffix inverse=ok (done inverse) := by
      unfold verifier.QueryGeometry.for_range_loop0_loop0.body
      rw [Port4C_Reverse.zero]
      rfl
    unfold verifier.QueryGeometry.for_range_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,bodyRun]
  | succ n ih =>
    have nonzero : index≠0#usize := by intro hz; subst index; change 0=n+1 at hn; omega
    obtain ⟨i,hsub,hvalue,hnext⟩ := Port4C_Reverse.positive index (by omega)
    have hiv : i.val=n := by omega
    rw [Port4C_OwnedInverse.inverse_owned,if_neg nonzero,hsub,bind_tc_ok] at h
    obtain ⟨pref,hpref,h⟩ := bind_success _ _ _ h
    obtain ⟨newValue,hnew,h⟩ := bind_success _ _ _ h
    obtain ⟨⟨old,back⟩,hmut,h⟩ := bind_success _ _ _ h
    obtain ⟨x,hx,h⟩ := bind_success _ _ _ h
    obtain ⟨suffix1,hsuffix,h⟩ := bind_success _ _ _ h
    have tail := ih (back newValue) suffix1 i (by omega) h hiv
    have bodyRun : verifier.QueryGeometry.for_range_loop0_loop0.body ops flat prefixes
        (Port4C_Reverse.reverse index) suffix inverse=
        ok (cont (Port4C_Reverse.reverse i,suffix1,back newValue)) := by
      unfold verifier.QueryGeometry.for_range_loop0_loop0.body
      rw [hnext,bind_tc_ok]
      simp only [multiply,hpref,hnew,hmut,hx,hsuffix,bind_tc_ok]
    unfold verifier.QueryGeometry.for_range_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,bodyRun]
    exact tail

#print axioms from_owned
end AspisR1.Port4C_InverseLoop
end
