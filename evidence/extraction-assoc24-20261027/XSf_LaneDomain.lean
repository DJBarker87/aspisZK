import XSf_ByteDomain
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRk_ResultTools
set_option autoImplicit false
namespace XSf_LaneDomain
open AspisR1

theorem selected (s : Slice U8) (i : Usize) (hi : i.val<29) :
 LPq_SelectedDomain.selected s i=XRn_Join_sliceRange s (32*i.val) (32*i.val+32) := by
 have space : 928<UScalar.size .Usize := by
   have hmax : 928 ≤ Usize.max := by scalar_tac
   simp only [UScalar.size,UScalarTy.numBits,Usize.max,Usize.numBits] at hmax ⊢
   scalar_tac
 have h1 : (1#usize).val=1 := by scalar_tac
 have h32 : (32#usize).val=32 := by scalar_tac
 have fits : i.val+(1#usize).val<UScalar.size .Usize := by rw [h1]; omega
 have nv : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
   rw [Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt fits]
   rfl
 have fl : i.val*(32#usize).val<UScalar.size .Usize := by rw [h32]; omega
 have fr : (Usize.wrapping_add i 1#usize).val*(32#usize).val<UScalar.size .Usize := by rw [nv,h32]; omega
 unfold LPq_SelectedDomain.selected
 rw [XSa_ParserRange.range,Usize.wrapping_mul_val_eq,Nat.mod_eq_of_lt fl,
   Usize.wrapping_mul_val_eq,Nat.mod_eq_of_lt fr,nv]
 congr 1 <;> scalar_tac

theorem from_lanes (s : Slice U8)
 (lanes : ∀ n : Nat, n<29 → ∃ x : C.E, XSa_ParserLane.field s n=ok x) :
 LPq_SelectedDomain.ByteDomain s := by
 apply XSf_ByteDomain.from_decoders
 intro i hi
 obtain ⟨x,hx⟩ := lanes i.val hi
 unfold XSa_ParserLane.field at hx
 obtain ⟨b,hb,hx⟩ := bind_success _ _ _ hx
 obtain ⟨opt,hparse,hx⟩ := bind_success _ _ _ hx
 cases opt with
 | none => cases hx
 | some value => exact ⟨b,value,(selected s i hi).trans hb,hparse⟩

#print axioms selected
#print axioms from_lanes
end XSf_LaneDomain
