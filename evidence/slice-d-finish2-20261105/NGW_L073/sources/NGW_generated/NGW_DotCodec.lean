import NGW_DotRef.Funs
import NGM_DotABI
import NGM_GuardExact
set_option autoImplicit false
namespace NGW_DotCodec
open Aeneas Aeneas.Std Result AspisR1
abbrev Dot := NGM_DotABI.Dot

def toRef (d : Dot) : NGW_DotRef.Dot := ⟨d.c0.sums,d.c1.sums,d.count⟩
def fromRef (r : NGW_DotRef.Dot) : Dot := NGM_DotABI.make ⟨r.left,r.right,r.count⟩

theorem from_to (d : Dot) : fromRef (toRef d)=d := NGM_DotABI.make_read d

theorem to_from (r : NGW_DotRef.Dot) : toRef (fromRef r)=r := by cases r;rfl

theorem count_roundtrip (c : Usize) (bound : c.val ≤ 64) :
 UScalar.cast .Usize (UScalar.cast .U64 c)=c := by
 have size : 4096 ≤ UScalar.size .Usize := by
  rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h|h <;> simp [h]
 have wide : c.val < UScalar.size .U64 := by
  change c.val < 18446744073709551616
  omega
 apply UScalar.eq_of_val_eq
 rw [UScalar.cast_val_eq,UScalar.cast_val_eq,Nat.mod_eq_of_lt wide,Nat.mod_eq_of_lt (by omega)]

theorem unpack_pack (d : Dot) (bound : d.count.val ≤ 64) :
 (do let w ← NGW_DotRef.pack (toRef d)
     let r ← NGW_DotRef.unpack w
     ok (fromRef r))=ok d := by
 rcases d with ⟨⟨left⟩,⟨right⟩,count⟩
 obtain ⟨a,b,c,d,hl⟩ := NGM_ArrayFour.shape left
 obtain ⟨e,f,g,h,hr⟩ := NGM_ArrayFour.shape right
 subst left
 subst right
 have counts := count_roundtrip count bound
 simp [NGW_DotRef.pack,NGW_DotRef.unpack,toRef,fromRef,NGM_DotABI.make,Array.make,Array.index_usize,counts]

#print axioms from_to
#print axioms to_from
#print axioms count_roundtrip
#print axioms unpack_pack
end NGW_DotCodec
