import AspisV8R19.R332PrefixInitializationSelectors
import AspisV8R19.R336PrefixPairInverseExecution
import AspisV8R19.R311BatchReverseLoopExecution

/-! Exact composition of the initialized-prefix selector with the actual
reverse-loop execution. Length, canonical reads, iterator bounds, and output
capacity remain explicit premises; no enclosing caller guard is asserted. -/
set_option autoImplicit false
namespace AspisV8R19.R337InitializedReverseExecution

open Aeneas Aeneas.Std Result ControlFlow
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R332PrefixInitializationSelectors
open AspisV8R19.R336PrefixPairInverseExecution
open AspisV8R19.R311BatchReverseLoopExecution
open AspisR328PrefixInitializationRaw
open AspisR335PrefixPairInverseRaw
open AspisR305BatchReverseRaw.circle_norm.joined_inverse.line_norm.r110_norm

noncomputable section

/-- First initialized-prefix result followed by the actual reverse loop 2.
The caller supplies the relationship between the natural length and source
slice, the loop bounds, and sufficient initialized output length. -/
theorem first_prefix_initialized_reverse
    (xs : Slice U32) (f : Nat → M31Exact) (L : Nat)
    (hxslen : xs.val.length = L) (hnonempty : 0 < L)
    (hcanon : ∀ j, j < L →
      xs.val[j]? = some (encodeBase (f j)))
    (iter : ReverseRange) (hstart : iter.iter.start.val = 1)
    (hend : iter.iter.end.val = L)
    (ox : VecU32) (hoxlen : ox.length = L) (x : M31Exact) :
    ∃ px : VecU32,
      selectedPrefix0 xs = .ok px ∧
      batch_loop2 iter xs px (encodeBase x) ox =
        .ok (encodeBase
              (reverseModel f (sourcePrefixValue f) (L - 1) x ox).1,
             (reverseModel f (sourcePrefixValue f) (L - 1) x ox).2) := by
  have hxsnonempty : 0 < xs.val.length := by omega
  have hxs : ∀ j, j < xs.val.length →
      xs.val[j]? = some (encodeBase (f j)) := by
    intro j hj
    apply hcanon
    omega
  obtain ⟨px, hpxlen, hpxreads, _hpxlast, hselected⟩ :=
    selected_prefix_initialization_bundle xs f hxsnonempty hxs
  have hstart' : iter.iter.start.val = 1 := hstart
  have hend' : iter.iter.end.val = (L - 1) + 1 := by omega
  have hxsreads : ∀ j, 1 ≤ j → j ≤ L - 1 →
      xs.val[j]? = some (encodeBase (f j)) := by
    intro j hj1 hjn
    apply hcanon
    omega
  have hpxreads' : ∀ j, j < L - 1 →
      px.val[j]? = some (encodeBase (sourcePrefixValue f j)) := by
    intro j hj
    exact hpxreads j (by omega)
  have hcapacity : L - 1 < ox.length := by omega
  have hrun := batch_loop2_reverseModel f (sourcePrefixValue f)
    (L - 1) xs px ox iter x hstart' hend' hxsreads hpxreads' hcapacity
  exact ⟨px, hselected, by simpa using hrun⟩

/-- Second initialized-prefix result followed by the actual reverse loop 3.
Its equality with loop 2 uses R311's body-identical loop theorem. -/
theorem second_prefix_initialized_reverse
    (ys : Slice U32) (g : Nat → M31Exact) (L : Nat)
    (hyslen : ys.val.length = L) (hnonempty : 0 < L)
    (hcanon : ∀ j, j < L →
      ys.val[j]? = some (encodeBase (g j)))
    (iter : ReverseRange) (hstart : iter.iter.start.val = 1)
    (hend : iter.iter.end.val = L)
    (oy : VecU32) (hoylen : oy.length = L) (x : M31Exact) :
    ∃ py : VecU32,
      selectedPrefix1 ys = .ok py ∧
      batch_loop3 iter ys py (encodeBase x) oy =
        .ok (encodeBase
              (reverseModel g (sourcePrefixValue g) (L - 1) x oy).1,
             (reverseModel g (sourcePrefixValue g) (L - 1) x oy).2) := by
  have hysnonempty : 0 < ys.val.length := by omega
  have hys : ∀ j, j < ys.val.length →
      ys.val[j]? = some (encodeBase (g j)) := by
    intro j hj
    apply hcanon
    omega
  obtain ⟨py, hpylen, hpyreads, _hpylast, hselected⟩ :=
    second_prefix_bundle ys g hysnonempty hys
  have hstart' : iter.iter.start.val = 1 := hstart
  have hend' : iter.iter.end.val = (L - 1) + 1 := by omega
  have hysreads : ∀ j, 1 ≤ j → j ≤ L - 1 →
      ys.val[j]? = some (encodeBase (g j)) := by
    intro j hj1 hjn
    apply hcanon
    omega
  have hpyreads' : ∀ j, j < L - 1 →
      py.val[j]? = some (encodeBase (sourcePrefixValue g j)) := by
    intro j hj
    exact hpyreads j (by omega)
  have hcapacity : L - 1 < oy.length := by omega
  have hrun := batch_loop2_reverseModel g (sourcePrefixValue g)
    (L - 1) ys py oy iter x hstart' hend' hysreads hpyreads' hcapacity
  have hrun3 := batch_loop3_eq_batch_loop2 iter ys py (encodeBase x) oy
  rw [hrun3]
  exact ⟨py, hselected, by simpa using hrun⟩

#print axioms first_prefix_initialized_reverse
#print axioms second_prefix_initialized_reverse

end
end AspisV8R19.R337InitializedReverseExecution
