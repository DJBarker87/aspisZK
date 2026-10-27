import XSe_ByteWindows
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_OldBytes
open XSe_ByteWindows
def words (s : Slice U8) : Array U32 8#usize :=
 Array.make 8#usize [XRn_Join_word [byte s 0,byte s 1,byte s 2,byte s 3],XRn_Join_word [byte s 4,byte s 5,byte s 6,byte s 7],XRn_Join_word [byte s 8,byte s 9,byte s 10,byte s 11],XRn_Join_word [byte s 12,byte s 13,byte s 14,byte s 15],XRn_Join_word [byte s 16,byte s 17,byte s 18,byte s 19],XRn_Join_word [byte s 20,byte s 21,byte s 22,byte s 23],XRn_Join_word [byte s 24,byte s 25,byte s 26,byte s 27],XRn_Join_word [byte s 28,byte s 29,byte s 30,byte s 31]]
/-- Complete old byte-decoder transport into the checked raw-limb carrier. -/
theorem source (s : Slice U8) (size : s.val.length=32) :
 XSc_RecordByteLength.mapped s=
 _root_.aspis_core.field.wide_exact.WideExact.from_limbs (words s) := by
 unfold XSc_RecordByteLength.mapped
 unfold AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes
 have len : Slice.len s=AspisR1PrefixAggregateParser.field.wide_exact.WideExact.BYTE_LEN := by
  apply UScalar.eq_of_val_eq
  unfold AspisR1PrefixAggregateParser.field.wide_exact.WideExact.BYTE_LEN
  scalar_tac
 rw [if_neg (by simpa only [bne_iff_ne] using not_not_intro len)]
 simp only [index s 0#usize (by change 0<s.val.length; omega),bind_tc_ok]
 simp only [index s 1#usize (by change 1<s.val.length; omega),bind_tc_ok]
 simp only [index s 2#usize (by change 2<s.val.length; omega),bind_tc_ok]
 simp only [index s 3#usize (by change 3<s.val.length; omega),bind_tc_ok]
 simp only [index s 4#usize (by change 4<s.val.length; omega),bind_tc_ok]
 simp only [index s 5#usize (by change 5<s.val.length; omega),bind_tc_ok]
 simp only [index s 6#usize (by change 6<s.val.length; omega),bind_tc_ok]
 simp only [index s 7#usize (by change 7<s.val.length; omega),bind_tc_ok]
 simp only [index s 8#usize (by change 8<s.val.length; omega),bind_tc_ok]
 simp only [index s 9#usize (by change 9<s.val.length; omega),bind_tc_ok]
 simp only [index s 10#usize (by change 10<s.val.length; omega),bind_tc_ok]
 simp only [index s 11#usize (by change 11<s.val.length; omega),bind_tc_ok]
 simp only [index s 12#usize (by change 12<s.val.length; omega),bind_tc_ok]
 simp only [index s 13#usize (by change 13<s.val.length; omega),bind_tc_ok]
 simp only [index s 14#usize (by change 14<s.val.length; omega),bind_tc_ok]
 simp only [index s 15#usize (by change 15<s.val.length; omega),bind_tc_ok]
 simp only [index s 16#usize (by change 16<s.val.length; omega),bind_tc_ok]
 simp only [index s 17#usize (by change 17<s.val.length; omega),bind_tc_ok]
 simp only [index s 18#usize (by change 18<s.val.length; omega),bind_tc_ok]
 simp only [index s 19#usize (by change 19<s.val.length; omega),bind_tc_ok]
 simp only [index s 20#usize (by change 20<s.val.length; omega),bind_tc_ok]
 simp only [index s 21#usize (by change 21<s.val.length; omega),bind_tc_ok]
 simp only [index s 22#usize (by change 22<s.val.length; omega),bind_tc_ok]
 simp only [index s 23#usize (by change 23<s.val.length; omega),bind_tc_ok]
 simp only [index s 24#usize (by change 24<s.val.length; omega),bind_tc_ok]
 simp only [index s 25#usize (by change 25<s.val.length; omega),bind_tc_ok]
 simp only [index s 26#usize (by change 26<s.val.length; omega),bind_tc_ok]
 simp only [index s 27#usize (by change 27<s.val.length; omega),bind_tc_ok]
 simp only [index s 28#usize (by change 28<s.val.length; omega),bind_tc_ok]
 simp only [index s 29#usize (by change 29<s.val.length; omega),bind_tc_ok]
 simp only [index s 30#usize (by change 30<s.val.length; omega),bind_tc_ok]
 simp only [index s 31#usize (by change 31<s.val.length; omega),bind_tc_ok]
 simp only [lift,XSc_WordTransport.source,bind_tc_ok]
 exact XSc_RecordFieldGeneral.source (words s)
#print axioms source
end XSe_OldBytes
