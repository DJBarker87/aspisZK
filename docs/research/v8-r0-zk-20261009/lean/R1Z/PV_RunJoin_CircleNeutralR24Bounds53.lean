import R1Z.PV_RunJoin_CircleNeutralShape53
import R1Z.PV_RunJoin_CircleNeutralFold53
import AspisV8R19.PartialDot
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralR24Bounds53
open PV_RunJoin_CircleNeutralShape53

theorem product (a b : U32) (ha : Canon a) (hb : Canon b) :
    a.val*b.val < 4611686014132420609 := Nat.mul_lt_mul_of_lt_of_lt ha hb

theorem intermediate (cg dh ch dg : Nat)
    (hcg : cg<4611686014132420609) (hdh : dh<4611686014132420609)
    (hch : ch<4611686014132420609) (hdg : dg<4611686014132420609) :
    dh ≤ cg+4611686014132420609 ∧ cg+4611686014132420609 < 18446744073709551616 ∧
      cg+4611686014132420609-dh < 9223372028264841218 ∧ ch+dg < 9223372028264841218 := by
  omega

theorem folded (x : U64) (hx : x.val<9223372028264841218) :
    (PV_RunJoin_CircleNeutralFold53.fold x).val < 6442450941 := by
  rw [PV_RunJoin_CircleNeutralFold53.fold_val]
  omega

theorem first (ae bf af be u v : Nat)
    (hae : ae<4611686014132420609) (hbf : bf<4611686014132420609)
    (haf : af<4611686014132420609) (hbe : be<4611686014132420609)
    (hu : u<6442450941) (hv : v<6442450941) :
    bf ≤ ae+4611686014132420609 ∧ ae+4611686014132420609 < 18446744073709551616 ∧
      v ≤ ae+4611686014132420609-bf+2*u+6442450941 ∧
      ae+4611686014132420609-bf+2*u+6442450941 < 18446744073709551616 ∧
      af+be+u+2*v < 18446744073709551616 := by omega

theorem third (ag ce bh df : Nat)
    (hag : ag<4611686014132420609) (hce : ce<4611686014132420609)
    (hbh : bh<4611686014132420609) (hdf : df<4611686014132420609) :
    ag+ce+9223372028264841218 < 18446744073709551616 ∧
      bh ≤ ag+ce+9223372028264841218 ∧ df ≤ ag+ce+9223372028264841218-bh := by omega

theorem fourth (ah bg cf de : Nat)
    (hah : ah<4611686014132420609) (hbg : bg<4611686014132420609)
    (hcf : cf<4611686014132420609) (hde : de<4611686014132420609) :
    ah+bg+cf+de < 18446744073709551616 := by omega

#print axioms product
#print axioms intermediate
#print axioms folded
#print axioms first
#print axioms third
#print axioms fourth
end R1Z.PV_RunJoin_CircleNeutralR24Bounds53
