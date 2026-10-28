import NCP_Extracted2.Funs
import NBP_DecodeWord
set_option autoImplicit false
noncomputable section
namespace NCP_DecodeReference
open Aeneas Aeneas.Std Result
def error : NCP_Extracted2.atomic_statement.NCP_AtomicStatementError →
    AspisR1TerminalDecoder.atomic_statement.AtomicStatementError
  | .NonCanonicalDigest => .NonCanonicalDigest
  | .NonCanonicalAssetId => .NonCanonicalAssetId
  | .FeeOutOfRange => .FeeOutOfRange
  | .PathDepthMismatch => .PathDepthMismatch
  | .InsertionIndexOutOfRange => .InsertionIndexOutOfRange
  | .CurrentAnchorMismatch => .CurrentAnchorMismatch
  | .OutputAnchorMismatch => .OutputAnchorMismatch

def transport (r : core.result.Result (Array U32 8#usize)
    NCP_Extracted2.atomic_statement.NCP_AtomicStatementError) :
    core.result.Result (Array U32 8#usize)
      AspisR1TerminalDecoder.atomic_statement.AtomicStatementError :=
  match r with
  | .Ok d => .Ok d
  | .Err e => .Err (error e)

def reference : NBN_AfterDecodeTypes.Decode := fun b => do
  let r ← NCP_Extracted2.NCP_digest.NCP_ref_decode b
  ok (transport r)

end NCP_DecodeReference
