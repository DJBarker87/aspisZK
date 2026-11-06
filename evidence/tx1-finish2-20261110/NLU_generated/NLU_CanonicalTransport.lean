import NLU_TerminalTransport
import NKQ_CanonicalBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Terminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation FIq_Carriers
/-- Identity of the four scalar carriers at the actual FIq terminal boundary;
no arithmetic, selected successful value or changed domain is introduced. -/
theorem canonical_to_native (q : aspis_core.field.QM31) (h : JFv_RoundArithmetic.Canonical q) :
 FIv_NativeValue.Canon (toQ q) := by
 exact h
theorem nkq_to_native (q : aspis_core.field.QM31) (h : NKQ_MaskCuts.Canon q) :
 FIv_NativeValue.Canon (toQ q) :=
 canonical_to_native q ((NKQ_CanonicalBridge.canonical q).mpr h)
theorem array_to_native {N : Usize} (a : Array aspis_core.field.QM31 N)
 (h : ∀ q∈a.val,NKQ_MaskCuts.Canon q) : FIw_ArrayValue.canonical (mapArray toQ a) := by
 intro q member
 change q∈a.val.map toQ at member
 obtain ⟨original,inside,same⟩:=List.mem_map.mp member
 subst q
 exact nkq_to_native original (h original inside)
theorem claims_to_native (claims : NLC_Finish.Claims) (h : NKQ_MaskCuts.CanonClaims claims) :
 ∀ row∈(mapArray (mapArray toQ) claims).val,FIw_ArrayValue.canonical row := by
 intro row member
 change row∈claims.val.map (mapArray toQ) at member
 obtain ⟨original,inside,same⟩:=List.mem_map.mp member
 subst row
 exact array_to_native original (h original inside)
#print axioms canonical_to_native
#print axioms nkq_to_native
#print axioms array_to_native
#print axioms claims_to_native
end AspisR1.NLU_Terminal
end
