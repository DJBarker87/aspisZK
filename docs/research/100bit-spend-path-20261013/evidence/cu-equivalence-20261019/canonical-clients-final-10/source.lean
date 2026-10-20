import CuSavingsCanonicalDotClientFactors
import CuSavingsCanonicalDotPartials
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotClients
open Aeneas Aeneas.Std Result ControlFlow AspisR1CanonicalDots
open CuSavingsCanonicalDotClientFactors CuSavingsCanonicalFieldStreamLoop
open CuSavingsCanonicalDotsPush
variable [Shared]

theorem old_shared_high_run (partials : Array E 4#usize) (scalars : Array K 4#usize) (iter : Range) (dot : old_pairing.EbyKDot) :
    old_clients.shared_high_loop iter partials scalars dot=oldRun (highNext partials scalars) iter dot := by
  unfold old_clients.shared_high_loop oldRun
  congr 1
  funext state
  exact old_shared_high_factor partials scalars state.1 state.2

theorem new_shared_high_run (partials : Array E 4#usize) (scalars : Array K 4#usize) (iter : Range) (dot : new_pairing.EbyKDot) :
    new_clients.shared_high_loop iter partials scalars dot=newRun (highNext partials scalars) iter dot := by
  unfold new_clients.shared_high_loop newRun
  congr 1
  funext state
  exact new_shared_high_factor partials scalars state.1 state.2

theorem shared_high_loop_eq (partials : Array E 4#usize) (scalars : Array K 4#usize) (hc : CanonicalArray partials) (iter : Range)
    (dot : old_pairing.EbyKDot) (hi : RelatedCounts dot) :
    new_clients.shared_high_loop iter partials scalars (project dot)=
      old_clients.shared_high_loop iter partials scalars dot := by
  rw [new_shared_high_run,old_shared_high_run]
  exact run_equivalence (highNext partials scalars) (highNext_canonical partials scalars hc) iter dot hi
#print axioms shared_high_loop_eq

theorem old_shared_row_run (f : Slice U8) (common : Array K 16#usize) (s : Usize) (iter : Range) (dot : old_pairing.EbyKDot) :
    old_clients.shared_row_loop iter f common s dot=oldRun (rowNext f common s) iter dot := by
  unfold old_clients.shared_row_loop oldRun
  congr 1
  funext state
  exact old_shared_row_factor f common s state.1 state.2

theorem new_shared_row_run (f : Slice U8) (common : Array K 16#usize) (s : Usize) (iter : Range) (dot : new_pairing.EbyKDot) :
    new_clients.shared_row_loop iter f common s dot=newRun (rowNext f common s) iter dot := by
  unfold new_clients.shared_row_loop newRun
  congr 1
  funext state
  exact new_shared_row_factor f common s state.1 state.2

theorem shared_row_loop_eq (f : Slice U8) (common : Array K 16#usize) (s : Usize) (iter : Range)
    (dot : old_pairing.EbyKDot) (hi : RelatedCounts dot) :
    new_clients.shared_row_loop iter f common s (project dot)=
      old_clients.shared_row_loop iter f common s dot := by
  rw [new_shared_row_run,old_shared_row_run]
  exact run_equivalence (rowNext f common s) (rowNext_canonical f common s) iter dot hi
#print axioms shared_row_loop_eq

theorem old_final_stream_run (f : Slice U8) (iter : Enum) (dot : old_pairing.EbyKDot) :
    old_clients.final_stream_loop iter f dot=oldRun (finalNext f) iter dot := by
  unfold old_clients.final_stream_loop oldRun
  congr 1
  funext state
  exact old_final_stream_factor f state.1 state.2

theorem new_final_stream_run (f : Slice U8) (iter : Enum) (dot : new_pairing.EbyKDot) :
    new_clients.final_stream_loop iter f dot=newRun (finalNext f) iter dot := by
  unfold new_clients.final_stream_loop newRun
  congr 1
  funext state
  exact new_final_stream_factor f state.1 state.2

theorem final_stream_loop_eq (f : Slice U8) (iter : Enum)
    (dot : old_pairing.EbyKDot) (hi : RelatedCounts dot) :
    new_clients.final_stream_loop iter f (project dot)=
      old_clients.final_stream_loop iter f dot := by
  rw [new_final_stream_run,old_final_stream_run]
  exact run_equivalence (finalNext f) (finalNext_canonical f) iter dot hi
#print axioms final_stream_loop_eq

theorem row_equivalence (f : Slice U8) (common : Array K 16#usize) (s : Usize) :
    new_clients.shared_row f common s=old_clients.shared_row f common s := by
  simp only [new_clients.shared_row,old_clients.shared_row,
    CuSavingsCanonicalDotsInvariant.old_new,CuSavingsCanonicalDotsInvariant.new_new,bind_tc_ok]
  exact shared_row_loop_eq f common s _ _ CuSavingsCanonicalDotsInvariant.initial_counts

theorem partials_equivalence (f : Slice U8) (common : Array K 16#usize) :
    new_clients.shared_partials f common=old_clients.shared_partials f common :=
  CuSavingsCanonicalDotPartials.outer_eq f common (row_equivalence f common)

theorem high_equivalence (partials : Array E 4#usize) (scalars : Array K 4#usize)
    (hc : CanonicalArray partials) :
    new_clients.shared_high partials scalars=old_clients.shared_high partials scalars := by
  simp only [new_clients.shared_high,old_clients.shared_high,
    CuSavingsCanonicalDotsInvariant.old_new,CuSavingsCanonicalDotsInvariant.new_new,bind_tc_ok]
  exact shared_high_loop_eq partials scalars hc _ _ CuSavingsCanonicalDotsInvariant.initial_counts

theorem final_equivalence (f : Slice U8) (weights : Slice K) :
    new_clients.final_stream f weights=old_clients.final_stream f weights := by
  simp only [new_clients.final_stream,old_clients.final_stream,
    CuSavingsCanonicalDotsInvariant.old_new,CuSavingsCanonicalDotsInvariant.new_new,bind_tc_ok]
  apply (bind_eq_iff (core.slice.Slice.iter weights) _ _).mpr
  intro sliceIter _
  apply (bind_eq_iff (core.iter.traits.iterator.Iterator.enumerate.trait_default
    (core.iter.traits.iterator.IteratorSliceIter K) sliceIter) _ _).mpr
  intro iter _
  exact final_stream_loop_eq f iter _ CuSavingsCanonicalDotsInvariant.initial_counts
#print axioms row_equivalence
#print axioms partials_equivalence
#print axioms high_equivalence
#print axioms final_equivalence
end AspisR1.CuSavingsCanonicalDotClients
