import NEO_QuadraticTotal
import NBG_WideBytes
set_option autoImplicit false
namespace NEO_WideWord
open Aeneas Aeneas.Std Result
attribute [local irreducible] core.num.U32.from_le_bytes

theorem small (k : Nat) (h : k<32) : k%Usize.size=k := by
 have cap : 32<Usize.size := by simp only [Usize.size_def,Usize.numBits_def]; scalar_tac
 exact Nat.mod_eq_of_lt (by omega)

theorem fixed (bytes : Array U8 32#usize) (i : Usize) (k : Nat)
 (same : i.val=4*k) (bound : k<8) :
 NEO_WindowV2.word bytes.to_slice i=ok (NBG_WideBytes.word bytes k) := by
 have a : 4*k<32 := by omega
 have b : 4*k+1<32 := by omega
 have c : 4*k+2<32 := by omega
 have d : 4*k+3<32 := by omega
 simp [NEO_WindowV2.word,Slice.index_usize,Array.to_slice,bytes.property,
  Usize.wrapping_add_val_eq,same,NBG_WideBytes.word,lift,bind_tc_ok,
  small _ a,small _ b,small _ c,small _ d,a,b,c,d]

#print axioms small
#print axioms fixed
end NEO_WideWord
