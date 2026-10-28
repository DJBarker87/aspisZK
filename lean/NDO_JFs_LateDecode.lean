import NDO_JFs_LateWords
import NDO_JFs_LateTail
import NDO_JFs_AfterstateSize
set_option autoImplicit false
namespace AspisR1.JFs_LateDecode
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

theorem factored : AspisS6NativeLateDecoderSplit.decode JFu_PublicRange.late=
    ok (.Ok JFs_LateChildren.value) := by
  have tail:=JFs_LateTail.source
  unfold JFu_PublicRange.late at tail
  have b8:=JFs_LateBytes.b8
  have b9:=JFs_LateBytes.b9
  unfold JFu_PublicRange.late at b8 b9
  have one : (1#u8 !=1#u8)=false := by decide
  have two : (2#u8 !=2#u8)=false := by decide
  have lengthCheck : (1520#usize !=1520#usize)=false := by decide
  unfold AspisS6NativeLateDecoderSplit.decode
  simp only [JFs_LateConstants.length,JFs_LateConstants.size,bind_tc_ok,lengthCheck,
    Bool.false_eq_true,↓reduceIte]
  simp only [JFu_PublicRange.late,
    JFt_LocalWindow.firstn 144 1520 8#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,JFs_LateBytes.magic_selected,
    JFs_LateConstants.magic_array,JFs_LateConstants.magic_compare,bind_tc_ok,
    Bool.false_eq_true,↓reduceIte,b8,b9,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION,POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT,
    one,two]
  simp only [JFt_Range.read 144 1520 (by decide) 10#usize 12#usize (by decide) (by decide),
    JFt_Range.read 144 1520 (by decide) 12#usize 16#usize (by decide) (by decide),
    JFt_Range.read 144 1520 (by decide) 16#usize 20#usize (by decide) (by decide),
    JFt_Range.read 144 1520 (by decide) 20#usize 24#usize (by decide) (by decide),
    show (10#usize).val=10 from rfl,show (12#usize).val=12 from rfl,
    show (16#usize).val=16 from rfl,show (20#usize).val=20 from rfl,show (24#usize).val=24 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    JFs_LateWords.read10,JFs_LateWords.read12,JFs_LateWords.read16,JFs_LateWords.read20,
    JFs_LateWords.word10,JFs_LateWords.word12,JFs_LateWords.word16,JFs_LateWords.word20,
    JFs_LateWords.cast10,JFs_LateWords.cast12,JFs_LateWords.cast16,JFs_LateWords.cast20,
    lift,bind_tc_ok,POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES,POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,
    JFs_AfterstateSize.bytes,show (32#usize !=32#usize)=false from by decide,
    show (800#usize !=800#usize)=false from by decide,
    show (688#usize !=688#usize)=false from by decide,lengthCheck,
    Bool.false_eq_true,↓reduceIte,tail]

theorem source : decode_pool_v1_pair_late_public_statement_boxed_v1 JFu_PublicRange.late=
    ok (.Ok JFs_LateChildren.value) :=
  (AspisS6NativeLateDecoderSplit.decode_source _).symm.trans factored

#print axioms factored
#print axioms source
end AspisR1.JFs_LateDecode
