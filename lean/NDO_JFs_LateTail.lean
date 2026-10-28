import NDO_JFs_LateChildren
import NDO_JFs_LateConstants
import NDO_JFs_RangeFrom
set_option autoImplicit false
namespace AspisR1.JFs_LateTail
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem source : AspisS6NativeLateDecoderSplit.decode_tail JFu_PublicRange.late=
    ok (.Ok JFs_LateChildren.value) := by
  have b24:=JFs_LateBytes.b24
  have b25:=JFs_LateBytes.b25
  have b26:=JFs_LateBytes.b26
  have b27:=JFs_LateBytes.b27
  have b28:=JFs_LateBytes.b28
  have b29:=JFs_LateBytes.b29
  have b30:=JFs_LateBytes.b30
  have b31:=JFs_LateBytes.b31
  unfold JFu_PublicRange.late at b24 b25 b26 b27 b28 b29 b30 b31
  have zero : (0#u8 !=0#u8)=false := by decide
  obtain ⟨sum,add,value⟩:=WP.spec_imp_exists
    (Usize.add_spec (x:=32#usize) (y:=800#usize) (by scalar_tac))
  have same : sum=832#usize := by scalar_tac
  rw [same] at add
  have snapshot:=JFs_LateChildren.snapshot
  have afterstate:=JFs_LateChildren.afterstate
  unfold JFu_PublicRange.snapshot at snapshot
  unfold JFu_PublicRange.afterstate at afterstate
  unfold AspisS6NativeLateDecoderSplit.decode_tail
  simp only [JFu_PublicRange.late,b24,b25,b26,b27,b28,b29,b30,b31,bind_tc_ok,zero,
    Bool.false_eq_true,↓reduceIte,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,add]
  simp only [JFt_Range.read 144 1520 (by decide) 32#usize 832#usize (by decide) (by decide),
    JFs_RangeFrom.read 144 1520 (by decide) 832#usize (by decide),
    show (32#usize).val=32 from rfl,show (832#usize).val=832 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    snapshot,afterstate,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    JFs_LateChildren.next,lift,JFs_LateChildren.next_compare,
    Bool.false_eq_true,↓reduceIte]
  rfl

#print axioms source
end AspisR1.JFs_LateTail
