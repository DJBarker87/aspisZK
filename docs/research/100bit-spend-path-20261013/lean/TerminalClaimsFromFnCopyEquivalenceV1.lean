import TerminalClaimsFromFnCallbackV5
import TerminalArrayFromFnCopyEquivalenceV8

/-! Concrete bridge for the current terminal_qm31 claims selector.  This
reuses its exact generated `claims[i / 28][i % 28]` callback body and applies
the green generic stable-callback equivalence.  The model remains a model of
the Rust standard operation; this does not prove the Rust core-library body. -/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

def terminalClaimsCallOnce {T : Type} :
    core.ops.function.FnOnce (TerminalClaimsClosure T) Usize T := {
  call_once := fun c flat => do
    let (q, _) ← terminalClaimsCallMut c flat
    .ok q
}

def terminalClaimsFnMut {T : Type} :
    core.ops.function.FnMut (TerminalClaimsClosure T) Usize T := {
  FnOnceInst := terminalClaimsCallOnce
  call_mut := terminalClaimsCallMut
}

/-- Total row-major selector used to instantiate the generated callback on
its reachable range.  Modulo makes it total without adding an initializer. -/
def terminalClaimsValue {T : Type} (c : TerminalClaimsClosure T) (i : Nat) : T :=
  let k := i % 84
  let row := k / 28
  let col := k % 28
  (c.val[row]'(by
    have hk : k < 84 := Nat.mod_lt _ (by omega)
    have hr : k / 28 < 3 := by omega
    simpa [c.property] using hr)).val[col]'(by
    have hk : k < 84 := Nat.mod_lt _ (by omega)
    have hc : k % 28 < 28 := Nat.mod_lt _ (by omega)
    have h29 : (29#usize : Usize).val = 29 := by scalar_tac
    have hr : k / 28 < 3 := by omega
    have hrow : k / 28 < c.val.length := by simpa [c.property] using hr
    have hrowlen : (c.val[k / 28]'hrow).val.length = 29 := by
      simpa [((c.val[k / 28]'hrow).property), h29]
    rw [hrowlen]
    omega)

theorem terminalClaimsFnMut_stable {T : Type}
    (c : TerminalClaimsClosure T) (flat : Usize) (hflat : flat.val < 84) :
    ∃ q, terminalClaimsFnMut.call_mut c flat = .ok (q, c) ∧
      q = terminalClaimsValue c flat.val := by
  obtain ⟨q, hcall, hq⟩ := terminalClaimsCallMut_stable c flat hflat
  refine ⟨q, ?_, ?_⟩
  · simpa [terminalClaimsFnMut] using hcall
  · simpa [terminalClaimsValue, Nat.mod_eq_of_lt hflat] using hq

theorem terminalClaims_from_fn_copy_stable {T : Type}
    (copyInst : core.marker.Copy T) (init : T)
    (claims : TerminalClaimsClosure T) :
    ∃ out : Array T 84#usize,
      AspisR1SelectedMaskProbe.core.array.from_fn 84#usize terminalClaimsFnMut claims =
        .ok out ∧
      array_from_fn_copy 84#usize copyInst terminalClaimsFnMut init claims =
        .ok out ∧
      ∀ i : Nat, ∀ hi : i < (84#usize : Usize).val,
        out.val[i]'(by simpa [out.property] using hi) = terminalClaimsValue claims i := by
  have hstable : ∀ i : Usize, i.val < (84#usize : Usize).val →
      terminalClaimsFnMut.call_mut claims i =
        .ok (terminalClaimsValue claims i.val, claims) := by
    intro i hi
    have h84 : (84#usize : Usize).val = 84 := by scalar_tac
    have hi' : i.val < 84 := by simpa [h84] using hi
    obtain ⟨q, hcall, hq⟩ := terminalClaimsFnMut_stable claims i hi'
    rw [hq] at hcall
    exact hcall
  obtain ⟨out, hmodel, hcopy, hvalues⟩ :=
    core_array_from_fn_eq_copy_of_stable
      (N := 84#usize) copyInst terminalClaimsFnMut init claims
      (terminalClaimsValue claims) hstable
  refine ⟨out, hmodel, hcopy, ?_⟩
  intro i hi
  have h84 : (84#usize : Usize).val = 84 := by scalar_tac
  exact hvalues i (by simpa [h84] using hi)

#print axioms terminalClaimsFnMut_stable
#print axioms terminalClaims_from_fn_copy_stable

end AspisR1SelectedMaskProbe
