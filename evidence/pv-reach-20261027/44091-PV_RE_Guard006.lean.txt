import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Guard006
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

def onTrue (blocks : Array (Array Std.U8 32#usize) 8#usize) (advances : Array (Array Std.U8 32#usize) 8#usize) (accepted : Array Std.U32 22#usize) (n : Std.Usize) (draws : Std.Usize) : Result (core.result.Result ((Array Std.U32 22#usize) × (Array Std.U8
    32#usize)) verifier.Error) := do
    if n = 22#usize
    then
      let a ← Array.index_usize advances 7#usize
      ok (core.result.Result.Ok (accepted, a))
    else ok (core.result.Result.Err verifier.Error.Transcript)

def onFalse (blocks : Array (Array Std.U8 32#usize) 8#usize) (advances : Array (Array Std.U8 32#usize) 8#usize) (accepted : Array Std.U32 22#usize) (n : Std.Usize) (draws : Std.Usize) : Result (core.result.Result ((Array Std.U32 22#usize) × (Array Std.U8
    32#usize)) verifier.Error) := do
    let k ← draws / 8#usize
    if n = 22#usize
    then
      let a ← Array.index_usize advances k
      ok (core.result.Result.Ok (accepted, a))
    else
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
      let b ← host_transcript.query_contains accepted n candidate
      if b
      then
        let i9 ← Aeneas.Std.lift (Std.Usize.wrapping_add draws 1#usize)
        host_transcript.scan_query_words blocks advances accepted n i9
      else
        let accepted1 ← Array.update accepted n candidate
        let i9 ← Aeneas.Std.lift (Std.Usize.wrapping_add n 1#usize)
        let i10 ← Aeneas.Std.lift (Std.Usize.wrapping_add draws 1#usize)
        host_transcript.scan_query_words blocks advances accepted1 i9 i10

/-- Exact first guard of `host_transcript.scan_query_words`.
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (blocks : Array (Array Std.U8 32#usize) 8#usize) (advances : Array (Array Std.U8 32#usize) 8#usize) (accepted : Array Std.U32 22#usize) (n : Std.Usize) (draws : Std.Usize) :
  host_transcript.scan_query_words (blocks := blocks) (advances := advances) (accepted := accepted) (n := n) (draws := draws) =
    (if draws = 64#usize then onTrue (blocks := blocks) (advances := advances) (accepted := accepted) (n := n) (draws := draws) else onFalse (blocks := blocks) (advances := advances) (accepted := accepted) (n := n) (draws := draws)) := by
  rw [host_transcript.scan_query_words]
  rfl

#print axioms onTrue
#print axioms onFalse
#print axioms first
end R1Z.PV_RE_Guard006
