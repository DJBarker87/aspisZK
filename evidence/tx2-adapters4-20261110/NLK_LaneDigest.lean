import NFY_Part005
import NLK_LaneInput
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NLK_LaneDigest
open Aeneas Aeneas.Std Result
abbrev Node := NKP_LaneCuts.Node
abbrev FE := AspisR1TerminalDecoder.atomic_statement.AtomicStatementError

def node (words : Array U32 8#usize) : Node := fun i =>
 words.val[i.val]'(by simpa [words.property] using i.isLt)

def mapReply : core.result.Result (Array U32 8#usize) FE → core.result.Result Node Unit
 | .Ok words => .Ok (node words)
 | .Err _ => .Err ()

def decode (bytes : Array U8 32#usize) : core.result.Result Node Unit :=
 mapReply (NFY_NBP_DigestDecode.decoded bytes)

/-- The CLOSED digest row is instantiated at THIS32-byte array. No successful
child Result is supplied by the caller and every raw error is retained. -/
def source (bytes : Array U8 32#usize) : Result (core.result.Result Node Unit) := do
 let reply ← AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes
 ok (mapReply reply)

theorem child (bytes : Array U8 32#usize) : source bytes=ok (decode bytes) := by
 have h := congrArg Prod.fst (NFY_NEQ_DecodeScalar.digest_result_state_effects bytes ())
 change AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes =
   ok (NFY_NBP_DigestDecode.decoded bytes) at h
 unfold source
 rw [h]
 rfl

theorem root_at_same_bytes (p : NLK_LaneInput.Sized) :
 source (NLK_LaneInput.root p)=ok (decode (NLK_LaneInput.root p)) := child _

theorem frontier_at_same_bytes (p : NLK_LaneInput.Sized) (level : Fin 20) :
 source (NLK_LaneInput.frontier p level)=ok (decode (NLK_LaneInput.frontier p level)) := child _

#print child
#print axioms child
#print axioms root_at_same_bytes
#print axioms frontier_at_same_bytes
end NLK_LaneDigest
