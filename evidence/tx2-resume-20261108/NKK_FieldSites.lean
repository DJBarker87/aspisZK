import NKK_FieldDomain
import NKK_FieldAssociation
set_option autoImplicit false
noncomputable section
namespace NKK_FieldSites
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKK_FieldFold

def gammaKinds : List Kind := [.e,.e,.e,.e,.k]
def zKinds : List Kind := [.k,.k,.k,.k,.e,.e,.k]

/-- Native gamma_stage is instantiated at the actual source176 offset after
three raw32 calls, with the entire immutable backing retained. -/
theorem gamma (bytes : Slice U8) (r : Reader)
 (backing : r.bytes=bytes) (size : bytes.val.length=1768) (cursor : r.at.val=176) :
 NKK_LogClauses.Holds (NKK_FieldDomain.Inside bytes) (program gammaKinds r) := by
 apply NKK_FieldDomain.inside gammaKinds r bytes backing
 change r.at.val+144≤bytes.val.length
 rw [cursor,size]
 omega

/-- The source semantic child supplies568; the7 native z/claim/rhs/power
calls remain bounded even at the final power read. -/
theorem z (bytes : Slice U8) (r : Reader)
 (backing : r.bytes=bytes) (size : bytes.val.length=1768) (cursor : r.at.val=568) :
 NKK_LogClauses.Holds (NKK_FieldDomain.Inside bytes) (program zKinds r) := by
 apply NKK_FieldDomain.inside zKinds r bytes backing
 change r.at.val+144≤bytes.val.length
 rw [cursor,size]
 omega

/-- Both native mixed stages use the actual log in their fold, not a free
reply stream or an independently chosen successful parent. -/
theorem gamma_fold (r : Reader) (before : List Value) :
 Matches before (fold (program gammaKinds r).events ⟨before,r,.ok (.Ok ())⟩)
 (program gammaKinds r).result := association gammaKinds r before

theorem z_fold (r : Reader) (before : List Value) :
 Matches before (fold (program zKinds r).events ⟨before,r,.ok (.Ok ())⟩)
 (program zKinds r).result := association zKinds r before

#print axioms gamma
#print axioms z
#print axioms gamma_fold
#print axioms z_fold
end NKK_FieldSites
