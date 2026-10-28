import R1Z.ProverRwQueryScan
import R1Z.ProverRwQueryTransition

/-! Checked factoring of the actual source body: selected byte word then
one Q22 transition. No hash/materialization law is introduced. -/
set_option autoImplicit false
namespace R1Z.ProverRwQueryWord
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwQueryTransition Query31ExplicitScanBody

def readWord (blocks : Blocks) (k draws : Usize) : Result U32 := do
  let i ← draws % 8#usize
  let at1 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i)
  let a ← Array.index_usize blocks k
  let i1 ← Array.index_usize a at1
  let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 1#usize)
  let i3 ← Array.index_usize a i2
  let i4 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 2#usize)
  let i5 ← Array.index_usize a i4
  let i6 ← Aeneas.Std.lift (Std.Usize.wrapping_add at1 3#usize)
  let i7 ← Array.index_usize a i6
  let i8 ←
    Aeneas.Std.lift (core.num.U32.from_le_bytes
      (Array.make 4#usize [ i1, i3, i5, i7 ]))
  let candidate ← Aeneas.Std.lift (i8 &&& 262143#u32)
  ok candidate

def factored (recur : Queries → Usize → Usize → Result Output)
    (blocks advances : Blocks) (accepted : Queries) (n draws : Usize) : Result Output := do
  if draws = 64#usize then
    if n = 22#usize then
      let a ← Array.index_usize advances 7#usize
      ok (.Ok (accepted,a))
    else ok (.Err verifier.Error.Transcript)
  else
    let k ← draws / 8#usize
    if n = 22#usize then
      let a ← Array.index_usize advances k
      ok (.Ok (accepted,a))
    else
      let candidate ← readWord blocks k draws
      let next ← advance ⟨accepted,n,draws⟩ candidate
      recur next.accepted next.accepted_len next.draws

theorem dispatch_factored (recur : Queries → Usize → Usize → Result Output)
    (blocks advances : Blocks) (accepted : Queries) (n draws : Usize) :
    dispatch recur blocks advances accepted n draws =
      factored recur blocks advances accepted n draws := by
  simp only [dispatch,factored,readWord,advance,bind_assoc_eq,lift,bind_tc_ok]
  split
  · rfl
  · apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro k hk
    split
    · rfl
    · repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
      split <;> simp only [bind_assoc_eq,bind_tc_ok]

theorem source_factored (blocks advances : Blocks) (accepted : Queries) (n draws : Usize) :
    host_transcript.scan_query_words blocks advances accepted n draws =
      factored (host_transcript.scan_query_words blocks advances) blocks advances accepted n draws := by
  rw [source_unfold,dispatch_factored]

#print axioms dispatch_factored
#print axioms source_factored
end R1Z.ProverRwQueryWord
