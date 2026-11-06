import NKB_Rejection

set_option autoImplicit false
namespace NKB_ParseCut
open Aeneas Aeneas.Std Result
abbrev Indices := Array U32 16#usize
abbrev Values := Array (Array U8 32#usize) 16#usize
abbrev RustResult := core.result.Result Unit NJS_Extract.verifier.Error

/-- K019/K020: the exact frozen entered `return Err(Error::Parse);` block.
Assertions: `matches!(out,Err(Error::Parse))`, `idx[j]==before_i[j]`,
`val[j][k]==before_v[j][k]`, for arbitrary j<16,k<32. This local transcription
contains no branch/parent success, syscall outcome or whole-model endpoint.
Source NKB_harness.rs SHA256 cb04e11ecda06c80ed32b012364eedc626ab361a5c83227b5722f98ad5d2a2ce.
Fragment NKB_fragments.rs SHA256 8556a388557677730e0057f11ccc1007aa723a2df96a1fcb6679c952aef0d916.
Exact assertion: `assert!(matches!(out,Err(Error::Parse)));`.
Entering the branch must be derived from the preceding guard; no full-parent
certificate is claimed. Hashes and exact snapshots: NKB_CERTIFICATES.md. -/
structure Cut (idx : Indices) (val : Values) (out : RustResult)
    (afterIdx : Indices) (afterVal : Values) : Prop where
 error : out=.Err .Parse
 indexFrame : afterIdx=idx
 valueFrame : afterVal=val

/-- A normally returned native Parse error is not the reused pending-none
wrapper's fail/panic result, on these SAME complete arrays. -/
theorem mismatch (idx : Indices) (val : Values) (out : RustResult)
    (afterIdx : Indices) (afterVal : Values) (cut : Cut idx val out afterIdx afterVal) :
 NKB_Rejection.boundary idx val none ≠ ok (out,afterIdx,afterVal) := by
 rw [cut.error,cut.indexFrame,cut.valueFrame]
 exact NKB_Rejection.lost_error idx val .Parse

set_option pp.proofs false
#print mismatch
#print axioms mismatch
end NKB_ParseCut
