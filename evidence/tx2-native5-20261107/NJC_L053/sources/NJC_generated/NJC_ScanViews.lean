import NJC_ClosedCalls
import NIL_WindowLayout
set_option autoImplicit false
noncomputable section
namespace NJC_ScanViews
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical

/-- CLOSED opening law at the SAME input/index, with literal U8 contents.
No pointer or digest equality is used as a payload equality. -/
theorem query (proof : Slice U8) (length : proof.val.length=57607)
 (i : Usize) (inside : i.val<22) :
 ∃ q, NEO_TailRef.opening proof i=ok q ∧ q.val.length=832 ∧
 q.val=(proof.val.drop (10055+i.val*832)).take 832 := by
 obtain ⟨q,run,width,contents⟩ := Port4B_Opening.opening_exact proof length i inside
 refine ⟨q,?_,width,?_⟩
 · rw [NJC_ClosedCalls.opening_clause]
   exact run
 · apply MultiproofConeByteEquality.bytes_injective
   simpa only [OraclePortCompactDraft.slice,bytesOf,List.map_take,List.map_drop] using contents

/-- Every nested scalar/K/E call selects its exact source bytes within the
SAME opening. Out-of-window bytes are never inferred from a descriptor. -/
theorem subwindow (proof q : List U8) (i off n : Nat)
 (same : q=(proof.drop (10055+i*832)).take 832) (fit : off+n≤832) :
 (q.drop off).take n=(proof.drop (10055+i*832+off)).take n := by
 rw [same,List.drop_take,List.take_take,List.drop_drop]
 rw [Nat.min_eq_left (by omega)]

/-- The actual scan tail covers both the7 round1 and64 final fields, on the
same proof. This reuses the retained contiguous-window lemma. -/
theorem final (proof : List U8) (i : Nat) (inside : i<64) :
 (((proof.drop 7783).take 2272).drop (32*(7+i))).take 32=
 (proof.drop (8007+32*i)).take 32 := NIL_WindowLayout.scan_final proof i inside

#print axioms query
#print axioms subwindow
#print axioms final
end NJC_ScanViews
