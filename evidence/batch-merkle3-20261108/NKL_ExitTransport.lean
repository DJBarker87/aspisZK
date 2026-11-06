import NKB_ParseCut
set_option autoImplicit false
namespace NKL_ExitTransport
open Aeneas Aeneas.Std Result
abbrev Indices := NKB_ParseCut.Indices
abbrev Values := NKB_ParseCut.Values
abbrev Reply := NKB_ParseCut.RustResult

/-- Native exit blocks. Branch entry is a preceding-segment obligation. -/
inductive Exit where | parse | merkle | success

def reply : Exit → Reply
 | .parse => .Err .Parse | .merkle => .Err .Merkle | .success => .Ok ()

/-- Typed cut for a single entered return block: no oracle event or write
is hidden here. Parse reuses K019/K020; the other two blocks are NKL K001-K004. -/
structure Cut (exit : Exit) (idx : Indices) (val : Values) (out : Reply)
 (afterIdx : Indices) (afterVal : Values) : Prop where
 result : out = reply exit
 indices : afterIdx = idx
 values : afterVal = val

/-- Error observation at the cohort interface; retains the complete successful
value. This is a local observation map, NOT the unproved whole-cohort equation. -/
def observe (r : Reply) (idx : Indices) (val : Values) : Result (Unit × Indices × Values) :=
 match r with | .Ok u => ok (u,idx,val) | .Err _ => fail .panic

theorem parse_cut (idx : Indices) (val : Values) (out : Reply)
 (afterIdx : Indices) (afterVal : Values)
 (cut : NKB_ParseCut.Cut idx val out afterIdx afterVal) :
 Cut .parse idx val out afterIdx afterVal :=
 ⟨cut.error,cut.indexFrame,cut.valueFrame⟩

theorem result (exit : Exit) (idx : Indices) (val : Values) (out : Reply)
 (afterIdx : Indices) (afterVal : Values)
 (cut : Cut exit idx val out afterIdx afterVal) :
 (out,afterIdx,afterVal) = (reply exit,idx,val) := by
 rw [cut.result,cut.indices,cut.values]

theorem observed (exit : Exit) (idx : Indices) (val : Values) (out : Reply)
 (afterIdx : Indices) (afterVal : Values)
 (cut : Cut exit idx val out afterIdx afterVal) :
 observe out afterIdx afterVal =
  match exit with | .success => ok ((),idx,val) | _ => fail .panic := by
 cases exit <;> simpa only [cut.result,cut.indices,cut.values,reply,observe]

/-- The exit appends no event. Both an ordered effect log and an oracle-query
log can instantiate Event; their complete prefixes are retained unchanged. -/
def atExit {Event : Type} (events : List Event) (out : Reply)
 (idx : Indices) (val : Values) := (events,observe out idx val)

theorem no_suffix {Event : Type} (events : List Event) (exit : Exit)
 (idx : Indices) (val : Values) (out : Reply) (afterIdx : Indices) (afterVal : Values)
 (cut : Cut exit idx val out afterIdx afterVal) :
 atExit events out afterIdx afterVal =
 (events,match exit with | .success => ok ((),idx,val) | _ => fail .panic) := by
 unfold atExit
 rw [observed exit idx val out afterIdx afterVal cut]

#print result
#print axioms parse_cut
#print axioms result
#print axioms observed
#print axioms no_suffix
end NKL_ExitTransport
