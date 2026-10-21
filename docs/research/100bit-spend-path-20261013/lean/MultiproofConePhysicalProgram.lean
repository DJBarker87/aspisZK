import MultiproofConePhysicalDigest
import MultiproofConeOrderedLevel

set_option autoImplicit false
namespace AspisR1.MultiproofConePhysicalProgram
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalDigest
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Digest := Array U8 32#usize
abbrev Address := Slice (Slice U8)
abbrev Run (α : Type) := Program Address Digest (Result α)

def checked {α β : Type} (r : Result α) (f : α → Run β) : Run β :=
  match r with
  | .ok x => f x
  | .fail e => .done (.fail e)
  | .div => .done .div

/-- The exact post-hash checked mutations of the extracted writer. -/
def finish (s : reference.Scratch) (digest : Digest) (ni cursor : Usize)
    (index : U32) (w : Usize) : Result reference.Row := do
  let parent ← index/2#u32
  let idx ← Array.update s.idx w parent
  let val ← Array.update s.val w digest
  let nw ← w+1#usize
  ok (.Next {s with idx:=idx,val:=val,«at»:=cursor} ni nw)

def writer (s : reference.Scratch) (left right : Digest) (ni cursor : Usize)
    (index : U32) (w : Usize) : Run reference.Row :=
  .ask (parts left right) fun digest => .done (finish s digest ni cursor index w)

/-- The instrumented physical node, retaining all array/range/scalar Results.
The oracle answer is written into scratch in the ask continuation. -/
def node (s : reference.Scratch) (physical : Slice U8) (i w : Usize) : Run reference.Row :=
  checked (Array.index_usize s.idx i) fun index =>
  checked (Array.index_usize s.val i) fun value =>
  checked (i+1#usize) fun ni =>
  let supplied : Run reference.Row :=
    checked (Slice.len physical-s.«at») fun remaining =>
    if remaining<32#usize then .done (.ok (.Stop s)) else
    checked (s.«at»+32#usize) fun cursor =>
    checked (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      physical {start:=s.«at»,«end»:=cursor}) fun chunk =>
    checked (reference.read32 chunk) fun sibling =>
    if index &&& 1#u32=0#u32 then writer s value sibling ni cursor index w
    else writer s sibling value ni cursor index w
  if ni<s.n then
    checked (Array.index_usize s.idx ni) fun nextIndex =>
    if nextIndex=index^^^1#u32 then
      checked (Array.index_usize s.val ni) fun right =>
      checked (i+2#usize) fun next => writer s value right next s.«at» index w
    else supplied
  else supplied

theorem checked_result {α β : Type} (H : Address → Digest) (r : Result α) (f : α → Run β) :
    (eval H (checked r f)).2 = (do let x ← r; (eval H (f x)).2) := by
  cases r <;> rfl

theorem conditional_result {α : Type} (H : Address → Digest) (test : Prop) [Decidable test]
    (yes no : Run α) :
    (eval H (if test then yes else no)).2 =
      if test then (eval H yes).2 else (eval H no).2 := by
  split <;> rfl

/-- All-input writer return correspondence. Logs remain present in the
instrumented program; this theorem projects only the returned Result. -/
theorem writer_result {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Address → Digest) (law : ∀ input, D.digest hash input=ok (H input))
    (s : reference.Scratch) (left right : Digest) (ni cursor : Usize) (index : U32) (w : Usize) :
    (eval H (writer s left right ni cursor index w)).2=
      reference.write_parent D hash s left right ni cursor index w := by
  change finish s (H (parts left right)) ni cursor index w = _
  unfold reference.write_parent
  change _ = (do let digest ← D.digest hash (parts left right); finish s digest ni cursor index w)
  rw [law];rfl

/-- Exact returned Result for arbitrary physical scratch and slice, including
panic/divergence and short rejection, with no initial domain assumption. -/
theorem node_result {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Address → Digest) (law : ∀ input, D.digest hash input=ok (H input))
    (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    (eval H (node s physical i w)).2=reference.binary_step D hash s physical i w := by
  simp only [node,checked_result,conditional_result,writer_result D hash H law,eval]
  unfold reference.binary_step
  rfl

#print axioms checked_result
#print axioms conditional_result
#print axioms writer_result
#print axioms node_result
end AspisR1.MultiproofConePhysicalProgram
