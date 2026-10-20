import AspisR1RhoResumeCaller.Types
import CuSavingsRhoEntryTransport
import AspisR1RhoReader.Funs
import AspisR1RhoResumeInlined.Funs
namespace AspisR1RhoResumeCaller
open Aeneas Aeneas.Std Result
abbrev verifier.Error.Checkpoint := AspisR1RhoQuery.verifier.Error.Checkpoint
/- Exact common source fragments retained parametrically. Neither receives the
stored rho/power, so they cannot change those locals. No proposition fields. -/
class ResumeCommon where
  beginSource : {H : Type} → aspis_core.Digest32 H → Slice U8 → Slice U8 → Slice U8 → transport.Variant → H → Result (core.result.Result ResumeBegin verifier.Error)
  middleSource : ResumeReader → Result (core.result.Result ResumeMiddle verifier.Error)
  allocationBackend : AspisR1.CuSavingsRhoEmptyReserveModel.Backend
abbrev source_resume_begin {H : Type} [ResumeCommon] := ResumeCommon.beginSource (H:=H)
abbrev source_resume_middle [ResumeCommon] := ResumeCommon.middleSource

def source_read_k (reader : ResumeReader) :
    Result (core.result.Result (aspis_core.field.QM31 × ResumeReader) verifier.Error) := do
  let (r,after) ← AspisR1CuRho.verifier.Reader.k reader
  .ok (match r with | .Err e => .Err (AspisR1RhoStage.initError e) | .Ok k => .Ok (k,after))
def source_resume_weights (weights : alloc.vec.Vec aspis_core.field.QM31) (reader : ResumeReader) :
    Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31 × ResumeReader) verifier.Error) := do
  let r ← AspisR1RhoResumeInlined.verifier.resume_weights weights reader
  .ok (match r with | .Err e => .Err (AspisR1RhoStage.initError e) | .Ok pair => .Ok pair)
-- Exact source-derived Copy/zero transported by coordinates. The allocator
-- is instantiated on the same current field carrier as the resumed loop.
def sourceCopy : core.marker.Copy aspis_core.field.QM31 :=
  {cloneInst:={clone:=fun x => .ok x}}
def sourceZero : aspis_core.field.QM31 :=
  {c0:={a:=0#u32,b:=0#u32},c1:={a:=0#u32,b:=0#u32}}
def source_resume_allocate [ResumeCommon] (v : transport.Variant) :
    Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) verifier.Error) :=
  letI : AspisR1CuRho.HeapReserve :=
    AspisR1.CuSavingsRhoEmptyReserveModel.heapReserve ResumeCommon.allocationBackend
  do
  let n ← AspisR1RhoPowerTail.transport.Variant.final_len v
  let r ← AspisR1CuRho.r0.heap.source_filled sourceCopy n sourceZero
  .ok (match r with | .Err _ => .Err .Allocation | .Ok weights => .Ok weights)
end AspisR1RhoResumeCaller
