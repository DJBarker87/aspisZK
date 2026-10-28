import R1Z.PV_RunJoin_PolyCompact40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PolyHigh40
open Aeneas Aeneas.Std ProverRwFull PV_RunJoin_PolyCell38
variable [ExternalTypes]

/-- Every byte read by the compactor in the high half is zero. -/
theorem high (q : Q) (j : Nat) (lo : 16≤j) (hi : j<32) :
    (cell q)[j]?=some 0#u8 := by
  have hg := congrArg (fun xs : List U8 => xs[j-16]?)
    (PV_RunJoin_PolyCompact40.high_half q)
  simpa only [List.getElem?_drop,Nat.add_sub_of_le lo,
    List.getElem?_replicate,show j-16<16 from (by omega),↓reduceIte] using hg
#print axioms high
end R1Z.PV_RunJoin_PolyHigh40
