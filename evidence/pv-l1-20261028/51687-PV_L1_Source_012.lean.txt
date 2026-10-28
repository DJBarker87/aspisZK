import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_012
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (blocks : Array (Array Std.U8 32#usize) 8#usize)
  (advances : Array (Array Std.U8 32#usize) 8#usize)
  (accepted : Array Std.U32 22#usize) (n : Std.Usize) (draws : Std.Usize) :
  Logged (core.result.Result ((Array Std.U32 22#usize) × (Array Std.U8
    32#usize)) verifier.Error)
  := do
  let _ ← observe .queryScan 0 (ok ())
  if draws = 64#usize
  then
    if n = 22#usize
    then
      let a ← PV_L1_Logged.lift (Array.index_usize advances 7#usize)
      Pure.pure (core.result.Result.Ok (accepted, a))
    else Pure.pure (core.result.Result.Err verifier.Error.Transcript)
  else
    let k ← PV_L1_Logged.lift (draws / 8#usize)
    if n = 22#usize
    then
      let a ← PV_L1_Logged.lift (Array.index_usize advances k)
      Pure.pure (core.result.Result.Ok (accepted, a))
    else
      let i ← PV_L1_Logged.lift (draws % 8#usize)
      let at1 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_mul 4#usize i))
      let a ← PV_L1_Logged.lift (Array.index_usize blocks k)
      let i1 ← PV_L1_Logged.lift (Array.index_usize a at1)
      let i2 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add at1 1#usize))
      let i3 ← PV_L1_Logged.lift (Array.index_usize a i2)
      let i4 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add at1 2#usize))
      let i5 ← PV_L1_Logged.lift (Array.index_usize a i4)
      let i6 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add at1 3#usize))
      let i7 ← PV_L1_Logged.lift (Array.index_usize a i6)
      let i8 ← PV_L1_Logged.lift (Aeneas.Std.lift (core.num.U32.from_le_bytes
          (Array.make 4#usize [ i1, i3, i5, i7 ])))
      let candidate ← PV_L1_Logged.lift (Aeneas.Std.lift (i8 &&& 262143#u32))
      let b ← PV_L1_Logged.lift (host_transcript.query_contains accepted n candidate)
      if b
      then
        let i9 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add draws 1#usize))
        host_transcript.scan_query_words blocks advances accepted n i9
      else
        let accepted1 ← PV_L1_Logged.lift (Array.update accepted n candidate)
        let i9 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add n 1#usize))
        let i10 ← PV_L1_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add draws 1#usize))
        host_transcript.scan_query_words blocks advances accepted1 i9 i10

theorem complete_result
  (blocks : Array (Array Std.U8 32#usize) 8#usize)
  (advances : Array (Array Std.U8 32#usize) 8#usize)
  (accepted : Array Std.U32 22#usize) (n : Std.Usize) (draws : Std.Usize) :
  erase (produce blocks advances accepted n draws) = host_transcript.scan_query_words blocks advances accepted n draws := by
  unfold produce
  conv_rhs => unfold host_transcript.scan_query_words
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_012
