import NCP_Extracted2.Funs
import NCP_ModelDischarge
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

theorem reference_model (b : Array U8 32#usize) :
    reference b = ok (NBP_DigestDecode.decoded b) := by
  simp [reference,NCP_Extracted2.NCP_digest.NCP_ref_decode,
    Array.index_usize,Array.length,b.property,NBP_DigestDecode.decoded,
    NBP_DecodeWord.word,NBG_WideBytes.word,NBG_WideBytes.limbs,
    NBP_DecodeWord.P,transport,error,lift,bind_tc_ok]

theorem reference_source : NBN_AfterDecodeTypes.NBN_Dep_DigestDecode reference := by
  intro b
  rw [reference_model]
  exact (NBP_DigestDecode.result b).symm

#print axioms reference_model
#print axioms reference_source
end NCP_DecodeReference
