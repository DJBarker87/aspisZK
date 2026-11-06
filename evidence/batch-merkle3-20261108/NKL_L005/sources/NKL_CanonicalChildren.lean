import NKB_CanonicalEcheck
import NKB_CanonicalPrefix
import NFU_LPl_Check
set_option autoImplicit false
namespace NKL_CanonicalChildren
open Aeneas Aeneas.Std Result AspisR1

def compactGood (bytes : Slice U8) : Bool :=
 (List.range (bytes.val.length/16)).all (NFU_Retarget.LPl.Check.predicate bytes.val)

def echeckGood (bytes : Slice U8) : Bool :=
 (List.range (bytes.val.length/32)).all (NKB_CanonicalEcheck.pass bytes false)

/-- Total CLOSED compact child installed at the SAME bytes, with both Result
arms. No first-error trace, successful-child, or endpoint equality is assumed. -/
theorem compact_result (bytes : Slice U8) :
 NFU_Retarget.compact.check_values bytes =
 ok (if compactGood bytes then .Ok () else .Err .NonCanonical) := by
 rw [NFU_Retarget.LPl_A.Check.shipped_leaf_model]
 have same : NFU_Retarget.LPl_A.Check.loop bytes.val=compactGood bytes := by
  rw [NFU_Retarget.LPl_A.Check.loop,NFU_Retarget.LPl_A.stages_all]
  unfold compactGood
  apply congrArg (List.all (List.range (bytes.val.length/16)))
  funext i
  exact (NFU_Retarget.LPl.Check.stage bytes.val i).symm
 rw [same]

theorem echeck_result (bytes : Slice U8) :
 NFU_Retarget.verifier.echeck bytes false =
 ok (if echeckGood bytes then .Ok () else .Err .Parse) :=
 NKB_CanonicalEcheck.source bytes false

/-- Result conversion at the actual compact-to-verifier boundary: every
NonCanonical error becomes Parse, and the Ok value stays Unit. -/
def convert {Error : Type} (r : core.result.Result Unit Error) :
 NKB_CanonicalRange.ScanResult :=
 match r with | .Ok u => .Ok u | .Err _ => .Err .Parse

theorem compact_call (bytes : Slice U8) :
 (do let r ← NFU_Retarget.compact.check_values bytes
     ok (convert r)) = ok (NKB_CanonicalOpening.reply (compactGood bytes)) := by
 rw [compact_result]
 cases h:compactGood bytes <;> rfl

theorem echeck_call (bytes : Slice U8) :
 (do let r ← NFU_Retarget.verifier.echeck bytes false
     ok (match r with | .Ok u => (.Ok u : NKB_CanonicalRange.ScanResult) | .Err _ => .Err .Parse)) =
 ok (NKB_CanonicalOpening.reply (echeckGood bytes)) := by
 rw [echeck_result]
 cases h:echeckGood bytes <;> rfl

set_option pp.proofs false
#print compact_call
#print echeck_call
#print axioms compact_result
#print axioms echeck_result
#print axioms compact_call
#print axioms echeck_call
end NKL_CanonicalChildren
