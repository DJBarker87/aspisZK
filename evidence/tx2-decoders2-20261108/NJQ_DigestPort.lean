import NJQ_Read
import NFY_Part005
set_option autoImplicit false
noncomputable section
namespace NJQ_DigestPort
open Aeneas Aeneas.Std Result
abbrev SourceError := AspisR1TerminalDecoder.atomic_statement.AtomicStatementError
abbrev TargetError := NJI_Extracted.aspis_statement.atomic_statement.AtomicStatementError
abbrev Digest := Array U32 8#usize

def error : SourceError → TargetError
 | .NonCanonicalDigest => .NonCanonicalDigest
 | .NonCanonicalAssetId => .NonCanonicalAssetId
 | .FeeOutOfRange => .FeeOutOfRange
 | .PathDepthMismatch => .PathDepthMismatch
 | .InsertionIndexOutOfRange => .InsertionIndexOutOfRange
 | .CurrentAnchorMismatch => .CurrentAnchorMismatch
 | .OutputAnchorMismatch => .OutputAnchorMismatch

def port (r : core.result.Result Digest SourceError) : core.result.Result Digest TargetError :=
 match r with | .Ok d => .Ok d | .Err e => .Err (error e)

def canonical (b : Array U8 32#usize) : Result (core.result.Result Digest TargetError) := do
 let reply ← AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical b
 ok (port reply)

def decoded (b : Array U8 32#usize) : core.result.Result Digest TargetError :=
 port (NFY_NBP_DigestDecode.decoded b)

/-- CLOSED TX2:146 applied on the SAME exact typed byte array, every Result. -/
theorem source (b : Array U8 32#usize) : canonical b=ok (decoded b) := by
 unfold canonical
 rw [NFY_NBP_DigestDecode.result]
 rfl

/-- This is the original checkpoint's 80..112 window, not an independently
chosen digest argument or a decoder-success assumption. -/
theorem argument (b : Slice U8) (len : b.val.length=192) :
 ∃ a : Array U8 32#usize, NJQ_Read.read b 80#usize 32#usize=ok a ∧
 a.val=(b.val.drop 80).take 32 := by
 let a := NHY_NaturalReads.array b 80 32#usize (by change 80+32≤b.val.length;omega)
 exact ⟨a,NJQ_Read.value b 80#usize 32#usize (by change 80+32≤b.val.length;omega),rfl⟩

#print axioms source
#print axioms argument
end NJQ_DigestPort
