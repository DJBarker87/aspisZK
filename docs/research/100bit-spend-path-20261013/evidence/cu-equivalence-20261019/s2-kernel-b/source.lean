import CuSavingsS2SourceCoefficientLoop
import CuSavingsS2SourceTail
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceKernel
open Aeneas Aeneas.Std Result AspisR1S2Groups
open CuSavingsS2SourceArrays
variable [Shared]

theorem initial_catalog : Catalog 0 (Array.repeat 64#usize 0#u16) 0#usize := by
  constructor
  · exact CuSavingsS2SourceTables.seen_zero.symm
  · intro i hi
    have hzero : (0#usize).val=0 := by scalar_tac
    omega

theorem repeat_lookup (n : Usize) (i : Nat) : lookup (Array.repeat n zero) zero i=zero := by
  simp [lookup,Array.repeat,List.getD_eq_getElem?_getD]

theorem initial_coeff : CoeffEq (Array.repeat 64#usize zero) (Array.repeat 12#usize zero) := by
  intro i hi
  rw [repeat_lookup,repeat_lookup]

theorem quotient (f : Slice U8) (hlen : Slice.len f=2048#usize) :
    (Slice.len f / 32#usize : Result Usize)=.ok 64#usize := by
  rw [hlen]
  obtain ⟨x,hx,hv⟩ := UScalar.div_spec (x:=2048#usize) (y:=32#usize) (by scalar_tac)
  have he : x=64#usize := UScalar.eq_of_val_eq (by scalar_tac)
  simpa only [he] using hx

theorem source_kernel (w : Weights) (f : Slice U8) (low : Array E 16#usize)
    (hw : w.variant=transport.Variant.S2) (hlen : Slice.len f=2048#usize) :
    new.s2_grouped_inactive_pair f low = old.grouped_inactive_pair w f low := by
  unfold new.s2_grouped_inactive_pair old.grouped_inactive_pair
  dsimp only
  rw [quotient f hlen]
  simp only [bind_tc_ok]
  apply CuSavingsS2SourceCoefficientLoop.source_transport 64 w f
    {start:=0#usize,«end»:=64#usize} (Array.repeat 64#usize 0#u16)
    (Array.repeat 64#usize zero) (Array.repeat 12#usize zero) 0#usize hw
    (by scalar_tac) (by scalar_tac) (by scalar_tac) initial_catalog initial_coeff
  intro masks oldCoeffs newCoeffs groups hc hv
  have hn : groups=12#usize := UScalar.eq_of_val_eq (hc.1.trans CuSavingsS2SourceTables.seen_end)
  subst groups
  exact CuSavingsS2SourceTail.source_loop 12 low masks oldCoeffs newCoeffs 12#usize hc hv
    {start:=0#usize,«end»:=12#usize} (by scalar_tac) (by scalar_tac) (by scalar_tac) zero

#print axioms initial_catalog
#print axioms initial_coeff
#print axioms quotient
#print axioms source_kernel
end AspisR1.CuSavingsS2SourceKernel
