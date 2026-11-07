import LIB_VPublicDomain
set_option autoImplicit false
noncomputable section
namespace LIB_VTerminalCarriers
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1
open LIB_VScalarCarriers (array toRaw)
abbrev NQ := FIv_NativeArithmetic.NQ
def scalar (q : QM31) : NQ := FIq_Carriers.toQ (toRaw q)
def nativeArray {n : Usize} (a : Array QM31 n) : Array NQ n :=
 FIq_Carriers.mapArray FIq_Carriers.toQ (array toRaw a)
def nativeClaims (c : Claims) :=
 FIq_Carriers.mapArray (FIq_Carriers.mapArray FIq_Carriers.toQ) (claimsRaw c)
def nativeChallenges (c : OrigChallenges) := FIq_Carriers.toChallenges (challengesRaw c)
theorem scalar_canonical (q : QM31) : FIv_NativeValue.Canon (scalar q) := q.property
theorem array_canonical {n : Usize} (a : Array QM31 n) : FIw_ArrayValue.canonical (nativeArray a) := by
 intro q mem
 change q ∈ (a.val.map toRaw).map FIq_Carriers.toQ at mem
 obtain ⟨raw,mem,rfl⟩ := List.mem_map.mp mem
 obtain ⟨can,_,rfl⟩ := List.mem_map.mp mem
 exact scalar_canonical can
theorem claims_canonical (c : Claims) : ∀ row∈(nativeClaims c).val,FIw_ArrayValue.canonical row := by
 intro row mem
 change row ∈ (c.val.map k29Raw).map (FIq_Carriers.mapArray FIq_Carriers.toQ) at mem
 obtain ⟨raw,mem,rfl⟩ := List.mem_map.mp mem
 obtain ⟨can,_,rfl⟩ := List.mem_map.mp mem
 exact array_canonical can
def ofNative (q : NQ) (h : FIv_NativeValue.Canon q) : QM31 :=
 ⟨⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩,h⟩
theorem scalar_ofNative (q : NQ) (h : FIv_NativeValue.Canon q) : scalar (ofNative q h)=q := by cases q;rfl
#print axioms scalar_canonical
#print axioms array_canonical
#print axioms claims_canonical
#print axioms scalar_ofNative
end LIB_VTerminalCarriers
