import RPt_FJf_RawTower
import RPt_FJf_RawField
import RPt_FJf_DotFinishValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_RawDecode
open Aeneas Aeneas.Std Result
open FJf_RawResidue (F)

def q (a : FIo_Native.fast_pairing.canonical.Q) : OraclePortCheckpointAbiC5.K :=
  FJf_RawTower.pack ((JFv_TX2_DotFinishMeaning.cell a 0).val : F)
    ((JFv_TX2_DotFinishMeaning.cell a 1).val : F)
    ((JFv_TX2_DotFinishMeaning.cell a 2).val : F)
    ((JFv_TX2_DotFinishMeaning.cell a 3).val : F)

def raw (a : Array U64 4#usize) : OraclePortCheckpointAbiC5.K :=
  FJf_RawTower.pack ((FJf_U64Array.cell a 0).val : F) ((FJf_U64Array.cell a 1).val : F)
    ((FJf_U64Array.cell a 2).val : F) ((FJf_U64Array.cell a 3).val : F)

def dot (a : FIo_Native.fast_pairing.canonical.Dot) : OraclePortCheckpointAbiC5.K := raw a.sums

theorem source (a b : FIo_Native.fast_pairing.canonical.Q) (out : Array U64 4#usize)
    (ha : JFs_TX2_DotFinish.Canon a) (hb : JFs_TX2_DotFinish.Canon b)
    (run : FIo_Native.fast_pairing.canonical.Q.raw a b=ok out) : raw out=q a*q b := by
  obtain ⟨a,b',c,d,rfl⟩ := JFs_TX2_RawMap.shape a
  obtain ⟨e,f,g,h,rfl⟩ := JFs_TX2_RawMap.shape b
  have ha0 := ha a (by simp [JFs_TX2_RawMap.pack,Array.make])
  have ha1 := ha b' (by simp [JFs_TX2_RawMap.pack,Array.make])
  have ha2 := ha c (by simp [JFs_TX2_RawMap.pack,Array.make])
  have ha3 := ha d (by simp [JFs_TX2_RawMap.pack,Array.make])
  have hb0 := hb e (by simp [JFs_TX2_RawMap.pack,Array.make])
  have hb1 := hb f (by simp [JFs_TX2_RawMap.pack,Array.make])
  have hb2 := hb g (by simp [JFs_TX2_RawMap.pack,Array.make])
  have hb3 := hb h (by simp [JFs_TX2_RawMap.pack,Array.make])
  have expected := FJf_RawReference.source a b' c d e f g h
  have same := Result.ok.inj (expected.symm.trans run)
  subst out
  change FJf_RawTower.pack
    ((FJf_RawReference.raw0 a b' c d e f g h).val : F)
    ((FJf_RawReference.raw1 a b' c d e f g h).val : F)
    ((FJf_RawReference.raw2 a b' c d e f g h).val : F)
    ((FJf_RawReference.raw3 a b' c d e f g h).val : F)=
    FJf_RawTower.pack (a.val:F) b'.val c.val d.val*FJf_RawTower.pack (e.val:F) f.val g.val h.val
  rw [FJf_RawField.lane0 a b' c d e f g h ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3,
    FJf_RawField.lane1 a b' c d e f g h ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3,
    FJf_RawField.lane2 a b' c d e f g h ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3,
    FJf_RawField.lane3 a b' c d e f g h ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  exact FJf_RawTower.multiply _ _ _ _ _ _ _ _

#print axioms source
end AspisR1.FJf_RawDecode
end
