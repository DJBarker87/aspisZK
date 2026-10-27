import LPs_CheckDomain
import LPn_ExpandTrace
set_option autoImplicit false
namespace AspisR1.LPs_ExpandDomain
open Aeneas Aeneas.Std Result LPs_CheckDomain

def Expanded (compact y1 : List U8) : Prop := ∀ row, row<29 → ∀ lane, lane<32 →
  byte y1 (32*row+lane)=if lane<16 then byte compact (16*row+lane) else 0

theorem expanded (compact before y1 : Slice U8)
    (len : compact.val.length=464) (size : before.val.length=928)
    (trace : LPn.Expand.NativeTrace compact.val before.val 29 y1.val) :
    y1.val.length=928 ∧ Expanded compact.val y1.val ∧
    _root_.compact.expand_values compact before=ok (.Ok (),y1) := by
  have inherited := LPn.Expand.to_inherited _ _ _ _ trace
  have length := LPl.Expand.length _ _ _ _ inherited
  refine ⟨length.trans size,?_,?_⟩
  · intro row hr lane hl
    have observed := LPl.Expand.invariant _ _ _ _ inherited (32*row+lane) (by omega)
    rw [if_pos (by omega)] at observed
    have div : (32*row+lane)/32=row := by omega
    have mod : (32*row+lane)%32=lane := by omega
    simp only [LPl_A.Expand.byte,div,mod] at observed
    unfold byte
    rw [observed]
    split <;> (try simp only [Nat.mul_comm]) <;> rfl
  · apply LPn.Expand.native_result compact before y1 (by omega) (by omega) (by omega)
    simpa only [len] using trace

#print axioms expanded
end AspisR1.LPs_ExpandDomain
