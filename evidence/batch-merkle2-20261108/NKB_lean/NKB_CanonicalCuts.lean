import NKB_CanonicalEcheck
import NKB_CanonicalOpening
set_option autoImplicit false
namespace NKB_CanonicalCuts
open Aeneas Aeneas.Std Result AspisR1 NKB_CanonicalRange NKB_CanonicalOpening

def isOk : ScanResult→Bool | .Ok _=>true | .Err _=>false

/-- Reviewed transcription of K029/K030, K025/K026, K027/K028:
`assert_eq!(out.is_ok(),expected); if !expected { assert!(matches!(out,Err(Error::Parse))) }`.
Only these asserted output clauses appear here. Complete input hashes and
native domains are in NKB_CANONICAL_NATIVE_PAIRS.json. No whole-parent credit. -/
def ReadCut (expected : Bool) (out : ScanResult) : Prop :=
 isOk out=expected ∧ (expected=false→ out=.Err .Parse)

theorem read_result (expected : Bool) (out : ScanResult) (cut : ReadCut expected out) :
 out=reply expected := by
 cases expected with
 | false=>simpa only [reply,Bool.false_eq_true,if_false] using cut.2 rfl
 | true=>
   cases out with
   | Ok value=>cases value;rfl
   | Err error=>have impossible:=cut.1;cases impossible

/-- Unit-valued echeck has only the two constructors established by the
CLOSED child's concrete source theorem. This is a result-shape fact, without
assuming either branch; NJZ's ledger credit is still pending. -/
theorem child_shape (bs : Slice U8) (k : Bool) :
 NFU_Retarget.verifier.echeck bs k=ok (.Ok ()) ∨
 NFU_Retarget.verifier.echeck bs k=ok (.Err .Parse) := by
 rw [NKB_CanonicalEcheck.source]
 cases h:(List.range (bs.val.length/32)).all (NKB_CanonicalEcheck.pass bs k) <;> simp

theorem child_ok (bs : Slice U8) (k : Bool)
 (chosen : (List.range (bs.val.length/32)).all (NKB_CanonicalEcheck.pass bs k)=true) :
 NFU_Retarget.verifier.echeck bs k=ok (.Ok ()) := by
 rw [NKB_CanonicalEcheck.source,chosen];rfl

theorem child_parse (bs : Slice U8) (k : Bool)
 (chosen : (List.range (bs.val.length/32)).all (NKB_CanonicalEcheck.pass bs k)=false) :
 NFU_Retarget.verifier.echeck bs k=ok (.Err .Parse) := by
 rw [NKB_CanonicalEcheck.source,chosen];rfl

/-- K033/K034 cover the Ok child constructor; K049/K036 the Parse
constructor on identical final source inputs. Together they preserve Result
at the actual one-call site; no arbitrary non-Parse child error is admitted. -/
def CallCut (childOk : Bool) (out : ScanResult) : Prop :=
 if childOk then isOk out=true else out=.Err .Parse

theorem call_result (childOk : Bool) (out : ScanResult) (cut : CallCut childOk out) :
 out=reply childOk := by
 apply read_result
 cases childOk with
 | false=>exact ⟨by rw [show out=.Err .Parse from cut];rfl,fun _=>cut⟩
 | true=>exact ⟨cut,by intro h;cases h⟩

#print axioms read_result
#print axioms child_shape
#print axioms child_ok
#print axioms child_parse
#print axioms call_result
end NKB_CanonicalCuts
