import ArrayFromFnCopySlice
import ExtractedMaskReducerOps

/-! Stable-capture execution contract for the exact generated array helper.
The callback equation is an explicit premise; each real callback must be
proved successful and state-preserving before this theorem applies. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result ControlFlow

private theorem loop_stable_aux
    {T T2 : Type} {N : Std.Usize}
    (inst : core.ops.function.FnMut T2 Std.Usize T) (f : T2)
    (value : Nat → T) (hstable : ∀ i : Std.Usize, i.val < N.val →
      inst.call_mut f i = .ok (value i.val, f))
    (fuel : Nat) (i : Std.Usize) (out : Array T N)
    (hgap : N.val - i.val = fuel) (hi : i.val ≤ N.val)
    (hprefix : ∀ j, ∀ hj : j < i.val, ∀ hjN : j < N.val,
      out.val[j]'(by simpa [out.property] using hjN) = value j) :
    ∃ final : Array T N,
      array_from_fn_copy_loop inst f out i = .ok final ∧
      ∀ j, ∀ hjN : j < N.val,
        final.val[j]'(by simpa [final.property] using hjN) = value j := by
  induction fuel using Nat.strong_induction_on generalizing i out with
  | h fuel ih =>
      by_cases hlt : i.val < N.val
      · have hcall := hstable i hlt
        have hupdateBound : i.val < out.length := by simpa using hlt
        obtain ⟨updated, hupdate, hset⟩ :=
          Aeneas.Std.WP.spec_imp_exists (Array.update_spec out i (value i.val) hupdateBound)
        have hNbound : N.val ≤ Usize.max := by
          have hNsize : N.val < 2 ^ Usize.numBits := by
            simpa [Usize.numBits, UScalarTy.Usize_numBits_eq] using N.hBounds
          have hmax : Usize.max + 1 = 2 ^ Usize.numBits := by
            rw [Usize.numBits]
            exact Usize.max_succ_eq_pow
          omega
        have hmax : i.val + 1 ≤ Usize.max := by
          omega
        have haddSpec : (i + 1#usize : Result Usize) ⦃ j => j.val = i.val + 1 ⦄ := by
          apply UScalar.add_spec
          have hone : (1#usize).val = 1 := by scalar_tac
          simpa only [hone, UScalar.max_USize_eq] using hmax
        obtain ⟨i1, hadd, hi1val⟩ := Aeneas.Std.WP.spec_imp_exists haddSpec
        have hprefix1 : ∀ j, ∀ hj : j < i1.val, ∀ hjN : j < N.val,
            updated.val[j]'(by simpa [updated.property] using hjN) = value j := by
          intro j hj hjN
          have hjOldBound : j < out.val.length := by simpa [out.property] using hjN
          by_cases heq : j = i.val
          · subst j
            have hcell : (out.val.set i.val (value i.val))[i.val]'(by
                simpa using hlt) = value i.val := by
              exact List.getElem_set_self (l := out.val) (i := i.val)
                (a := value i.val) (by simpa using hlt)
            simpa [hset, Array.set_val_eq] using hcell
          · have hjOld : j < i.val := by rw [hi1val] at hj; omega
            have hne : i.val ≠ j := Ne.symm heq
            have hjSetBound : j < (out.val.set i.val (value i.val)).length := by
              simpa using hjOldBound
            have hcell : (out.val.set i.val (value i.val))[j]'hjSetBound =
                out.val[j]'hjOldBound := by
              simpa using (List.getElem_set_ne (l := out.val) (i := i.val)
                (j := j) hne hjSetBound)
            cases hset
            change (out.val.set i.val (value i.val))[j]'hjSetBound = value j
            rw [hcell]
            exact hprefix j hjOld hjN
        have hgap1 : N.val - i1.val < fuel := by
          rw [hi1val, ← hgap]
          omega
        have hi1le : i1.val ≤ N.val := by rw [hi1val]; omega
        obtain ⟨final, hrec, hfinal⟩ := ih (N.val - i1.val) hgap1 i1 updated rfl hi1le hprefix1
        refine ⟨final, ?_, hfinal⟩
        rw [array_from_fn_copy_loop.eq_def]
        simp only [UScalar.lt_equiv, hlt, if_pos, hcall, bind_tc_ok, hupdate,
          hadd, bind_tc_ok, hrec]
      · have heq : i.val = N.val := by omega
        refine ⟨out, ?_, ?_⟩
        · rw [array_from_fn_copy_loop.eq_def]
          simp [UScalar.lt_equiv, hlt]
        · intro j hjN
          have hj : j < i.val := by omega
          exact hprefix j hj hjN

theorem array_from_fn_copy_stable
    {T T2 : Type} (N : Std.Usize) (copyInst : core.marker.Copy T)
    (inst : core.ops.function.FnMut T2 Std.Usize T) (init : T) (f : T2)
    (value : Nat → T)
    (hstable : ∀ i : Std.Usize, i.val < N.val →
      inst.call_mut f i = .ok (value i.val, f)) :
    ∃ out : Array T N,
      array_from_fn_copy N copyInst inst init f = .ok out ∧
      ∀ j, ∀ hj : j < N.val,
        out.val[j]'(by simpa [out.property] using hj) = value j := by
  have hprefix : ∀ j, ∀ hj : j < (0#usize).val, ∀ hjN : j < N.val,
      (Array.repeat N init).val[j]'(by simpa [Array.repeat_val] using hjN) = value j := by
    intro j hj hjN
    have hfalse : False := by simpa using hj
    exact hfalse.elim
  have hN : (0#usize : Std.Usize).val ≤ N.val := by simp
  obtain ⟨out, hrun, hout⟩ := loop_stable_aux inst f value hstable
    (N.val - (0#usize).val) 0#usize (Array.repeat N init) rfl hN hprefix
  refine ⟨out, ?_, hout⟩
  simp only [array_from_fn_copy, bind_tc_ok]
  exact hrun

#print axioms array_from_fn_copy_stable

end AspisR1SelectedMaskProbe
