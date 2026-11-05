import NID_ReadListTransport
set_option autoImplicit false
noncomputable section
namespace NID_WeightReadsTransport
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port5Q2_ReaderWeights

theorem reads (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (bytes : Slice U8) (n : Nat) (start : Usize)
 (bound : start.val+16*n≤bytes.val.length) :
 Port5Q2_ReaderWeights.reads (T2Nat_ScalarJoin.readK unwrap) bytes n start=
 Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK bytes n start := by
 induction n generalizing start with
 | zero => rfl
 | succ n ih =>
   obtain ⟨b,out,_,cursor,_,run⟩ := CheckpointBytes3Reader.read_k_c5 ⟨bytes,start⟩ (by simp only;omega)
   have head := NID_BoundedReaders.k unwrap unwrap_ok (⟨bytes,start⟩ : verifier.Reader) (by simp only;omega)
   simp only [Port5Q2_ReaderWeights.reads,head,run,bind_tc_ok]
   cases value : CheckpointBytes3Reader.optionK
     ((ExactLeafFieldCodec.decodeQM31 (MultiproofConeCanonical.bytesOf b.val)).map CheckpointBytes3KDecode.rawK) with
   | Err err => rfl
   | Ok x =>
     change (do let tail ← Port5Q2_ReaderWeights.reads (T2Nat_ScalarJoin.readK unwrap) bytes n out.at
                match tail with
                | .Err e => ok (core.result.Result.Err e)
                | .Ok (xs,last) => ok (core.result.Result.Ok (x::xs,last))) =
            (do let tail ← Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK bytes n out.at
                match tail with
                | .Err e => ok (core.result.Result.Err e)
                | .Ok (xs,last) => ok (core.result.Result.Ok (x::xs,last)))
     rw [ih out.at (by simp only at cursor;rw [cursor];omega)]

/-- Exact full current helper Result, including first decoder rejection and
all deferred Vec backwrites, on the caller-established bounded section. -/
theorem weights (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (bytes : Slice U8) (start : Usize)
 (v : alloc.vec.Vec aspis_core.field.QM31)
 (bound : start.val+16*v.val.length≤bytes.val.length) :
 Port5Q2_ReaderWeights.weights (T2Nat_ScalarJoin.readK unwrap) bytes start v=
 CheckpointBytes4Ops.readWeights bytes start v := by
 rw [←T2Nat_WeightSequence.weights,Port5Q2_ReaderWeights.exact,Port5Q2_ReaderWeights.exact,
  reads unwrap unwrap_ok bytes v.val.length start bound]

/-- SAME64 weights allocated by the S2 resume caller, cursor712. No weights'
values, canonicality, allocation success or successful helper result assumed. -/
theorem checkpoint (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (bytes : Slice U8) (start : Usize)
 (v : alloc.vec.Vec aspis_core.field.QM31)
 (size : bytes.val.length=1768) (cursor : start.val=712) (width : v.val.length=64) :
 Port5Q2_ReaderWeights.weights (T2Nat_ScalarJoin.readK unwrap) bytes start v=
 CheckpointBytes4Ops.readWeights bytes start v :=
 weights unwrap unwrap_ok bytes start v (by rw [size,cursor,width];decide)
#print axioms reads
#print axioms weights
#print axioms checkpoint
end NID_WeightReadsTransport
