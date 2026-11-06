import NJU_ResumeObserved
set_option autoImplicit false
noncomputable section
namespace NKU
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev Pair := verifier.Prepared × verifier.Accumulator
/-- One immutable invocation frame. Reservation is the actual allocator item,
not a newly chosen outcome at the allocation site. -/
structure Frame where
 checkpoint : Slice U8
 proof : Slice U8
 publicBytes : Slice U8
 reservation : NP6_StdModel.Reservation
/-- All entered NKK occurrences use the existing typed event constructors;
terminal/cleanup observations retain the full returned value. -/
inductive Event where
 | call (event : NJU_ResumeObserved.Event)
 | terminal (reply : Result (core.result.Result Pair verifier.Error))
 | cleanup (weights : alloc.vec.Vec K)
inductive Phase where
 | header | proofDigest | publicDigest | checkpointDigest | roots | fields
 | queries | validator | semantic | zClaim | filled | weights | tail | terminal
structure Decoded where
 next : Option U8 := none
 endAt : Option Usize := none
 roots : List (Array U8 32#usize) := []
 gammaAlpha : List E := []
 rho : Option K := none
 queries : List U32 := []
 semantic : Option (Array K 10#usize) := none
 z : List K := []
 claim : Option E := none
 rhs : Option E := none
 power : Option K := none
/-- Single parent carrier: immutable inputs, decoded slots, Reader/backing,
iterator, owned allocation and complete terminal status. No callee reply is
assumed successful. -/
structure State where
 frame : Frame
 phase : Phase := .header
 decoded : Decoded := {}
 reader : verifier.Reader
 iterator : Option (core.slice.iter.Iter U8) := none
 owned : Option (alloc.vec.Vec K) := none
 returned : Option (Result (core.result.Result Pair verifier.Error)) := none
 history : List Event := []
def initial (frame : Frame) : State :=
 { frame, reader := { bytes := frame.checkpoint, «at» := 0#usize } }
def headerPost (s : State) (next : U8) («end» : Usize) : State :=
 { s with phase := .proofDigest, decoded := {s.decoded with next := some next, endAt := some «end»} }
theorem header_frame (s : State) (next : U8) («end» : Usize) :
 (headerPost s next «end»).frame=s.frame ∧
 (headerPost s next «end»).reader=s.reader ∧
 (headerPost s next «end»).owned=s.owned := ⟨rfl,rfl,rfl⟩
#print axioms header_frame
end NKU
