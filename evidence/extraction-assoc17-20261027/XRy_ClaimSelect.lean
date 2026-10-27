import XRy_ClaimSum
import CurrentClaimScalarNormalForm
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRy_ClaimSelect

theorem usize_value (n : Nat) (hn : n<32) : (XRn_Join_usize n).val=n := by
 change n%(UScalar.cMax .Usize+1)=n
 apply Nat.mod_eq_of_lt
 have hmin : 32 ≤ UScalar.cMax .Usize := by scalar_tac
 omega

/-- Verbatim scalar-selection branch of the existing raw preparedPart. -/
def read {H : Type} (sem : E.Sem H) (y1 : Slice U8) (point lane : Nat) : Result E.Q := do
 if point<3 then do
   let row ← Array.index_usize sem.claims (XRn_Join_usize point)
   Array.index_usize row (XRn_Join_usize lane)
 else if point=3 then Array.index_usize sem.extra (XRn_Join_usize lane)
 else if point=4 then Array.index_usize sem.before_z1 (XRn_Join_usize lane)
 else do
   let bytes ← XRn_Join_sliceRange y1 (32*lane) (32*lane+32)
   let e ← aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
   match e with
   | some e => ok (XRn_Join_FieldExternal.newQ e.c0)
   | none => fail .panic

#print axioms usize_value
end XRy_ClaimSelect
