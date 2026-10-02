import AspisV8R19.R329PrefixInitializationExecution
import AspisV8R19.R326PrefixProductSelectors
import AspisV8R19.R317SliceLastExecution

/-! Selectors for the selected first-prefix fragment. These statements use the
exact fragment output equation and explicit nonempty/canonical-read premises;
they do not close the surrounding batch guards or inverse path. -/
set_option autoImplicit false
namespace AspisV8R19.R332PrefixInitializationSelectors

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R321BatchPrefixLoopExecution
open AspisV8R19.R326PrefixProductSelectors
open AspisV8R19.R329PrefixInitializationExecution
open AspisV8R19.R317SliceLastExecution
open AspisR328PrefixInitializationRaw

noncomputable section

/-- Prefix product at source index j, including the initialized first item. -/
def sourcePrefixValue (f : Nat → M31Exact) (j : Nat) : M31Exact :=
  prefixAccum (fun k => f (k + 1)) 0 j (f 0)

theorem selected_prefix_output_length (xs : Slice U32) (f : Nat → M31Exact)
    (hnonempty : 0 < xs.val.length) (out : alloc.vec.Vec U32)
    (hout : out.val = [encodeBase (f 0)] ++
      prefixValues (fun k => f (k + 1)) 0 (xs.val.length - 1) (f 0)) :
    out.val.length = xs.val.length := by
  rw [hout]
  simp only [List.length_append, List.length_singleton,
    prefixValues_length]
  omega

theorem selected_prefix_output_reads (xs : Slice U32) (f : Nat → M31Exact)
    (hnonempty : 0 < xs.val.length) (out : alloc.vec.Vec U32)
    (hout : out.val = [encodeBase (f 0)] ++
      prefixValues (fun k => f (k + 1)) 0 (xs.val.length - 1) (f 0)) :
    ∀ j, j < xs.val.length →
      out.val[j]? = some (encodeBase (sourcePrefixValue f j)) := by
  intro j hj
  cases j with
  | zero =>
      rw [hout]
      simp [sourcePrefixValue, prefixAccum]
  | succ j =>
      have hjtail : j < xs.val.length - 1 := by omega
      rw [hout]
      rw [List.getElem?_append_right (by simp)]
      simpa [sourcePrefixValue, Nat.add_sub_cancel_left] using
        (prefixValues_getElem? (fun k => f (k + 1)) 0
          (xs.val.length - 1) (f 0) j hjtail)

theorem selected_prefix_output_last (xs : Slice U32) (f : Nat → M31Exact)
    (hnonempty : 0 < xs.val.length) (out : alloc.vec.Vec U32)
    (hout : out.val = [encodeBase (f 0)] ++
      prefixValues (fun k => f (k + 1)) 0 (xs.val.length - 1) (f 0)) :
    out.val.getLast? =
      some (encodeBase (sourcePrefixValue f (xs.val.length - 1))) := by
  rw [List.getLast?_eq_getElem?]
  rw [selected_prefix_output_length xs f hnonempty out hout]
  exact selected_prefix_output_reads xs f hnonempty out hout
    (xs.val.length - 1) (by omega)

theorem selected_prefix_initialization_bundle (xs : Slice U32)
    (f : Nat → M31Exact) (hnonempty : 0 < xs.val.length)
    (hxs : ∀ j, j < xs.val.length →
      xs.val[j]? = some (encodeBase (f j))) :
    ∃ out : alloc.vec.Vec U32,
      out.val.length = xs.val.length ∧
      (∀ j, j < xs.val.length →
        out.val[j]? = some (encodeBase (sourcePrefixValue f j))) ∧
      out.val.getLast? =
        some (encodeBase (sourcePrefixValue f (xs.val.length - 1))) ∧
      AspisR328PrefixInitializationRaw.selectedPrefix0 xs = .ok out := by
  obtain ⟨out, hout, hselected⟩ := selectedPrefix0_products xs f hnonempty hxs
  exact ⟨out,
    selected_prefix_output_length xs f hnonempty out hout,
    selected_prefix_output_reads xs f hnonempty out hout,
    selected_prefix_output_last xs f hnonempty out hout,
    hselected⟩

theorem selected_prefix_actual_last (xs : Slice U32)
    (f : Nat → M31Exact) (hnonempty : 0 < xs.val.length)
    (hxs : ∀ j, j < xs.val.length →
      xs.val[j]? = some (encodeBase (f j))) :
    ∃ out : alloc.vec.Vec U32,
      AspisR328PrefixInitializationRaw.selectedPrefix0 xs = .ok out ∧
      AspisR316SliceLastRaw.core.slice.Slice.last (alloc.vec.Vec.deref out) =
        .ok (some (encodeBase (sourcePrefixValue f (xs.val.length - 1)))) := by
  obtain ⟨out, _hlen, _hreads, hlast, hselected⟩ :=
    selected_prefix_initialization_bundle xs f hnonempty hxs
  refine ⟨out, hselected, ?_⟩
  rw [last_complete]
  change .ok out.val.getLast? =
    .ok (some (encodeBase (sourcePrefixValue f (xs.val.length - 1))))
  rw [hlast]

#print axioms selected_prefix_output_length
#print axioms selected_prefix_output_reads
#print axioms selected_prefix_output_last
#print axioms selected_prefix_initialization_bundle
#print axioms selected_prefix_actual_last

end
end AspisV8R19.R332PrefixInitializationSelectors
