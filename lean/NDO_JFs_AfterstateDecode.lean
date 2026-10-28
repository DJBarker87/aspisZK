import NDO_JFs_AfterstateHeader
import NDO_JFs_AfterstateSize
set_option autoImplicit false
namespace AspisR1.JFs_AfterstateDecode
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

theorem factored : AspisS6NativeAfterstateDecoderFactored.decode JFu_PublicRange.afterstate=
    ok (.Ok JFt_AfterstateValue.value) := by
  have oneCheck : (1#u8 !=1#u8)=false := by decide
  have lengthCheck : (688#usize !=688#usize)=false := by decide
  have tail:=JFt_Afterstate00.source
  unfold JFu_PublicRange.afterstate at tail
  unfold AspisS6NativeAfterstateDecoderFactored.decode
  simp only [JFs_AfterstateSize.length,JFs_AfterstateSize.bytes,bind_tc_ok,lengthCheck,
    Bool.false_eq_true,↓reduceIte]
  simp only [JFu_PublicRange.afterstate,
    JFt_LocalWindow.firstn 976 688 4#usize (by decide) (by decide),
    show (4#usize).val=4 from rfl,JFs_AfterstateHeader.magic_selected,
    JFs_AfterstateHeader.magic_array,bind_tc_ok,JFs_AfterstateHeader.magic_compare,
    Bool.false_eq_true,↓reduceIte]
  have b4:=JFs_AfterstateHeader.b4
  have b5:=JFs_AfterstateHeader.b5
  have b6:=JFs_AfterstateHeader.b6
  have b7:=JFs_AfterstateHeader.b7
  unfold JFu_PublicRange.afterstate at b4 b5 b6 b7
  simp only [b4,b5,b6,b7,bind_tc_ok,
    POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION,
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    oneCheck,Bool.false_eq_true,↓reduceIte]
  simp only [JFt_Range.read 976 688 (by decide) 16#usize 48#usize (by decide) (by decide),
    show (16#usize).val=16 from rfl,show (48#usize).val=48 from rfl,
    Nat.reduceAdd,Nat.reduceSub,JFt_AfterstateDigest.exact22,JFt_AfterstateDigest.decode22,
    bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,tail]

theorem source : decode_pool_v1_pair_verified_afterstate_v1 JFu_PublicRange.afterstate=
    ok (.Ok JFt_AfterstateValue.value) :=
  (AspisS6NativeAfterstateDecoderFactored.decode_source _).symm.trans factored

#print axioms factored
#print axioms source
end AspisR1.JFs_AfterstateDecode
