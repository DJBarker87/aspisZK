import RPu_FJf_RawDecode
import RPu_FJf_DotBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_DotMeaning
open Aeneas Aeneas.Std Result
open FJf_RawResidue (F)
open FJf_DotLane (Dot)

theorem pack_add (a b c d e f g h : F) :
    FJf_RawTower.pack (a+e) (b+f) (c+g) (d+h)=
      FJf_RawTower.pack a b c d+FJf_RawTower.pack e f g h := rfl

theorem folded (x : U64) : ((FIo_ReduceBounds.fold x).val : F)=(x.val : F) := by
  rw [JFv_TX2_FoldValue.source,FJf_RawResidue.fold]

theorem push (dot out : Dot) (a b : FIo_Native.fast_pairing.canonical.Q)
    (ha : JFs_TX2_DotFinish.Canon a) (hb : JFs_TX2_DotFinish.Canon b)
    (n : Nat) (hn : n < 4096) (bound : FJf_DotBound.Bound dot n)
    (run : FIo_Native.fast_pairing.canonical.Dot.push dot a b=ok out) :
    FJf_DotBound.Bound out (n+1) ∧
      FJf_RawDecode.dot out=FJf_RawDecode.dot dot+FJf_RawDecode.q a*FJf_RawDecode.q b := by
  obtain ⟨raw,hr,hb',hv⟩ := FJf_DotBound.push dot out a b n hn bound run
  have vv : ∀ j,j < 4 → ((FJf_U64Array.cell out.sums j).val : F)=
      ((FJf_U64Array.cell dot.sums j).val : F)+((FJf_U64Array.cell raw j).val : F) := by
    intro j hj
    rw [hv j hj,Nat.cast_add,folded]
  refine ⟨hb',?_⟩
  rw [←FJf_RawDecode.source a b raw ha hb hr]
  unfold FJf_RawDecode.dot FJf_RawDecode.raw
  change FJf_RawTower.pack
    ((FJf_U64Array.cell out.sums 0).val : F) ((FJf_U64Array.cell out.sums 1).val : F)
    ((FJf_U64Array.cell out.sums 2).val : F) ((FJf_U64Array.cell out.sums 3).val : F)=
    FJf_RawTower.pack
      (((FJf_U64Array.cell dot.sums 0).val : F)+((FJf_U64Array.cell raw 0).val : F))
      (((FJf_U64Array.cell dot.sums 1).val : F)+((FJf_U64Array.cell raw 1).val : F))
      (((FJf_U64Array.cell dot.sums 2).val : F)+((FJf_U64Array.cell raw 2).val : F))
      (((FJf_U64Array.cell dot.sums 3).val : F)+((FJf_U64Array.cell raw 3).val : F))
  congr 1
  · exact vv 0 (by decide)
  · exact vv 1 (by decide)
  · exact vv 2 (by decide)
  · exact vv 3 (by decide)

theorem finish (dot : Dot) (out : FIo_Native.fast_pairing.canonical.Q)
    (run : FIo_Native.fast_pairing.canonical.Dot.finish dot=ok out) :
    JFs_TX2_DotFinish.Canon out ∧ FJf_RawDecode.q out=FJf_RawDecode.dot dot := by
  obtain ⟨hc,hv⟩ := FJf_DotFinishValue.value dot out run
  refine ⟨hc,?_⟩
  unfold FJf_RawDecode.q FJf_RawDecode.dot FJf_RawDecode.raw
  congr 1
  · rw [hv 0];exact ZMod.natCast_mod _ _
  · rw [hv 1];exact ZMod.natCast_mod _ _
  · rw [hv 2];exact ZMod.natCast_mod _ _
  · rw [hv 3];exact ZMod.natCast_mod _ _
#print axioms pack_add
#print axioms folded
#print axioms push
#print axioms finish
end AspisR1.FJf_DotMeaning
end
