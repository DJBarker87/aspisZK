import NDO_JGv_DotSum
import JGv_DotCanonical
import SAG_DotWeights
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_DotMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open scoped BigOperators
attribute [local irreducible] JFw_Frames.window JFx_NativeBytes.proof

theorem field (i : Usize) (hi : i.val<64) :
    FIn_Primitives.field (JFw_Frames.window 8007 2048) i=ok (JGv_DotData.field ⟨i.val,hi⟩) := by
  interval_cases h : i.val
  · have same : i=0#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message00.field00
  · have same : i=1#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message00.field01
  · have same : i=2#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message00.field02
  · have same : i=3#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message00.field03
  · have same : i=4#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message00.field04
  · have same : i=5#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message00.field05
  · have same : i=6#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message00.field06
  · have same : i=7#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message00.field07
  · have same : i=8#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message08.field08
  · have same : i=9#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message08.field09
  · have same : i=10#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message08.field10
  · have same : i=11#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message08.field11
  · have same : i=12#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message08.field12
  · have same : i=13#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message08.field13
  · have same : i=14#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message08.field14
  · have same : i=15#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message08.field15
  · have same : i=16#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message16.field16
  · have same : i=17#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message16.field17
  · have same : i=18#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message16.field18
  · have same : i=19#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message16.field19
  · have same : i=20#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message16.field20
  · have same : i=21#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message16.field21
  · have same : i=22#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message16.field22
  · have same : i=23#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message16.field23
  · have same : i=24#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message24.field24
  · have same : i=25#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message24.field25
  · have same : i=26#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message24.field26
  · have same : i=27#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message24.field27
  · have same : i=28#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message24.field28
  · have same : i=29#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message24.field29
  · have same : i=30#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message24.field30
  · have same : i=31#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message24.field31
  · have same : i=32#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message32.field32
  · have same : i=33#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message32.field33
  · have same : i=34#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message32.field34
  · have same : i=35#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message32.field35
  · have same : i=36#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message32.field36
  · have same : i=37#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message32.field37
  · have same : i=38#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message32.field38
  · have same : i=39#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message32.field39
  · have same : i=40#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message40.field40
  · have same : i=41#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message40.field41
  · have same : i=42#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message40.field42
  · have same : i=43#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message40.field43
  · have same : i=44#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message40.field44
  · have same : i=45#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message40.field45
  · have same : i=46#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message40.field46
  · have same : i=47#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message40.field47
  · have same : i=48#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message48.field48
  · have same : i=49#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message48.field49
  · have same : i=50#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message48.field50
  · have same : i=51#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message48.field51
  · have same : i=52#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message48.field52
  · have same : i=53#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message48.field53
  · have same : i=54#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message48.field54
  · have same : i=55#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message48.field55
  · have same : i=56#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message56.field56
  · have same : i=57#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message56.field57
  · have same : i=58#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message56.field58
  · have same : i=59#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message56.field59
  · have same : i=60#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message56.field60
  · have same : i=61#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message56.field61
  · have same : i=62#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message56.field62
  · have same : i=63#usize := UScalar.eq_of_val_eq h
    subst i
    exact JGo_TX2_Message56.field63
#print axioms field

theorem reader (i : Usize) (x : FinishE) (hi : i.val<64)
    (run : finishField (JFw_Frames.window 8007 2048) i=ok x) :
    decodeFinish x=CheckpointBytes5Output.ofE (JGv_DotData.field ⟨i.val,hi⟩) := by
  have expected := FIn_Primitives.field_value _ _ _ (field i hi)
  have actual := SAG_FieldRead.from_finish _ _ _ run
  exact Option.some.inj (actual.symm.trans expected)
#print axioms reader

theorem source (out : AspisR1Stage2.Stage2Finish.E)
    (run : SAG_DotClosed.source (JFw_Frames.window 8007 2048) JGv_WeightsData.value=ok (.Ok out)) :
    CheckpointBytes5Output.ofE out=CheckpointBytes5Output.ofE JGv_QueryScalars11.rhs := by
  have weight : ∀ (i : Usize) (q : AspisR1Stage2.Stage2Finish.K) (hi : i.val<64),
      Slice.index_usize JGv_WeightsData.value i=ok q →
      AspisR1FinishDotReturnedFieldProductV1.finishQMDecoded (SAG_DotAdapter.toFinishQ q)=
        CheckpointBytes5Output.ofK (JGv_WeightsData.cell ⟨i.val,hi⟩) := by
    intro i q hi read
    have fetched := SAG_DotWeights.read_getD JGv_WeightsData.value i q JGv_WeightsData.w00 read
    have bound : i.val<JGv_WeightsData.list.length := by rw [JGv_WeightsData.length];exact hi
    have same : q=JGv_WeightsData.cell ⟨i.val,hi⟩ := by
      simpa only [JGv_WeightsData.value,JGv_WeightsData.cell,List.getElem?_eq_getElem bound,Option.getD_some] using fetched.symm
    rw [same,←SAG_DotDecode.q_decode]
  have value := SAG_DotAdapter.sourceDot_reader_law SAG_DotClosed.seed
    (JFw_Frames.window 8007 2048) JGv_WeightsData.value out
    (fun i=>CheckpointBytes5Output.ofE (JGv_DotData.field i))
    (fun i=>CheckpointBytes5Output.ofK (JGv_WeightsData.cell i))
    (by change JGv_WeightsData.list.length=64;exact JGv_WeightsData.length) reader weight run
  rw [←SAG_DotDecode.e_decode] at value
  change CheckpointBytes5Output.ofE out=(∑ i : Fin 64,JGv_DotData.term i) at value
  exact value.trans (JGv_DotSum.finite.trans JGv_DotSum.rhs)
#print axioms source
end AspisR1.JGx_DotMeaning
end
