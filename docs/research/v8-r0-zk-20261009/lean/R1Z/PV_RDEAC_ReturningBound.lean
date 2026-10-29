import R1Z.PV_RDEAC_FullCaps
import R1Z.PV_RDEAC_JoinHandlers
import R1Z.PV_RDEAC_JoinString
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEAC_ReturningBound
open PV_RDB1_V183_ReserveWorld PV_CBL_StringBytesAdapter PV_RDEAC_JoinValue

theorem relative_value (base path : List U8) :
    PV_RDEA_PushValues.value base path false (needsSeparator base)=joined base path := by
  cases h : needsSeparator base <;> simp only [PV_RDEA_PushValues.value,joined,h,
    Bool.false_eq_true,if_false,if_true,List.append_nil]

theorem one_more (base path : List U8) :
    base.length+1+path.length≤(joined base path).length+1 := by
  unfold joined
  split <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> omega

/-- This is a bound derived from native *success*, not an assumption that a
public allocation succeeds or a restriction deleting native error cases.
The ABI hypothesis selects the deployed 64-bit interpretation of Usize. -/
theorem derived {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat)
    (base path : List U8) (w : World S F)
    (abi : 9223372036854775808≤Usize.max)
    (success : (PV_RDEAC_FullJoin.join step shape address false (needsSeparator base) base path w).returned=.ok ()) :
    base.length+1+path.length≤Usize.max := by
  let e := PV_RDEAC_FullJoin.join step shape address false (needsSeparator base) base path w
  have cap := PV_RDEAC_FullCaps.join step shape width address false (needsSeparator base) base path w success
  change e.buffer.capacity≤9223372036854775807 at cap
  have fits := e.buffer.fits
  have values := PV_RDEAC_JoinHandlers.success_value step shape address false (needsSeparator base) base path w success
  change e.buffer.values=PV_RDEA_PushValues.value base path false (needsSeparator base) at values
  rw [values,relative_value] at fits
  have bound := one_more base path
  omega

#print axioms relative_value
#print axioms one_more
#print axioms derived
end R1Z.PV_RDEAC_ReturningBound
