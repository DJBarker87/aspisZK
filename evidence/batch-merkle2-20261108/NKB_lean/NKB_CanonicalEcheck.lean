import NJZ_CodecSemantics
import NKB_ScanWindows
set_option autoImplicit false
namespace NKB_CanonicalEcheck
open Aeneas Aeneas.Std Result AspisR1 NFU_Retarget

def pass (bs : Slice U8) (k : Bool) (i : Nat) : Bool :=
 LPl.Echeck.chunk ((bs.val.drop (32*i)).take 32) k

/-- Every complete child window comes from the SAME bytes and has the exact
32-byte domain; no canonicality or child success is assumed. -/
theorem window (bs : Slice U8) (i : Nat) (active : i<bs.val.length/32) :
 ∃ b : Array U8 32#usize,b.val=(bs.val.drop (32*i)).take 32 := by
 have room : 32*i+32≤bs.val.length := by omega
 refine ⟨⟨(bs.val.drop (32*i)).take 32,?_⟩,rfl⟩
 change ((bs.val.drop (32*i)).take 32).length=32
 simp only [List.length_take,List.length_drop]
 omega

/-- Closed echeck candidate instantiated without an oracle/trace/success
premise. This covers canonical_scan's 32/224/2272/128-byte children, both
results, and the ignored short suffix on the child's full public domain.
NJZ credit remains pending the next authoritative ledger gate. -/
theorem source (bs : Slice U8) (k : Bool) :
 NFU_Retarget.verifier.echeck bs k=
 ok (if (List.range (bs.val.length/32)).all (pass bs k) then .Ok () else .Err .Parse) := by
 apply NJZ_CodecSemantics.root
 intro i active
 obtain ⟨b,same⟩:=window bs i active
 refine ⟨b,same,?_⟩
 have h:=NJZ_CodecSemantics.source b k
 rw [same] at h
 change pass bs k i=NJZ_CodecSemantics.replyStep (NJZ_CodecSemantics.decoded b) k
 unfold pass
 rw [←h]
 unfold NJZ_CodecSemantics.parsedStep NJZ_CodecSemantics.replyStep NJZ_CodecSemantics.decoded
 cases NJC_EReaderResults.naturalE b <;> rfl

#print axioms window
#print axioms source
end NKB_CanonicalEcheck
