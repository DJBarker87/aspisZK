import NDO_JGv_DotFieldLift
import NDO_JGo_TX2_Message00
import NDO_JGo_TX2_Message08
import NDO_JGo_TX2_Message16
import NDO_JGo_TX2_Message24
import NDO_JGo_TX2_Message32
import NDO_JGo_TX2_Message40
import NDO_JGo_TX2_Message48
import NDO_JGo_TX2_Message56
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotFields
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
attribute [local irreducible] JFw_Frames.window JFx_NativeBytes.proof

theorem source (i : Usize) (hi : i.val<64) :
    ∃ x,finishField (JFw_Frames.window 8007 2048) i=ok x ∧ CanonicalFinish x := by
  interval_cases h : i.val
  · have same : i=0#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message00.field00 JGo_TX2_Message00.canonical00
  · have same : i=1#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message00.field01 JGo_TX2_Message00.canonical01
  · have same : i=2#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message00.field02 JGo_TX2_Message00.canonical02
  · have same : i=3#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message00.field03 JGo_TX2_Message00.canonical03
  · have same : i=4#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message00.field04 JGo_TX2_Message00.canonical04
  · have same : i=5#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message00.field05 JGo_TX2_Message00.canonical05
  · have same : i=6#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message00.field06 JGo_TX2_Message00.canonical06
  · have same : i=7#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message00.field07 JGo_TX2_Message00.canonical07
  · have same : i=8#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message08.field08 JGo_TX2_Message08.canonical08
  · have same : i=9#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message08.field09 JGo_TX2_Message08.canonical09
  · have same : i=10#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message08.field10 JGo_TX2_Message08.canonical10
  · have same : i=11#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message08.field11 JGo_TX2_Message08.canonical11
  · have same : i=12#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message08.field12 JGo_TX2_Message08.canonical12
  · have same : i=13#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message08.field13 JGo_TX2_Message08.canonical13
  · have same : i=14#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message08.field14 JGo_TX2_Message08.canonical14
  · have same : i=15#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message08.field15 JGo_TX2_Message08.canonical15
  · have same : i=16#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message16.field16 JGo_TX2_Message16.canonical16
  · have same : i=17#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message16.field17 JGo_TX2_Message16.canonical17
  · have same : i=18#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message16.field18 JGo_TX2_Message16.canonical18
  · have same : i=19#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message16.field19 JGo_TX2_Message16.canonical19
  · have same : i=20#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message16.field20 JGo_TX2_Message16.canonical20
  · have same : i=21#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message16.field21 JGo_TX2_Message16.canonical21
  · have same : i=22#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message16.field22 JGo_TX2_Message16.canonical22
  · have same : i=23#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message16.field23 JGo_TX2_Message16.canonical23
  · have same : i=24#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message24.field24 JGo_TX2_Message24.canonical24
  · have same : i=25#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message24.field25 JGo_TX2_Message24.canonical25
  · have same : i=26#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message24.field26 JGo_TX2_Message24.canonical26
  · have same : i=27#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message24.field27 JGo_TX2_Message24.canonical27
  · have same : i=28#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message24.field28 JGo_TX2_Message24.canonical28
  · have same : i=29#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message24.field29 JGo_TX2_Message24.canonical29
  · have same : i=30#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message24.field30 JGo_TX2_Message24.canonical30
  · have same : i=31#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message24.field31 JGo_TX2_Message24.canonical31
  · have same : i=32#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message32.field32 JGo_TX2_Message32.canonical32
  · have same : i=33#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message32.field33 JGo_TX2_Message32.canonical33
  · have same : i=34#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message32.field34 JGo_TX2_Message32.canonical34
  · have same : i=35#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message32.field35 JGo_TX2_Message32.canonical35
  · have same : i=36#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message32.field36 JGo_TX2_Message32.canonical36
  · have same : i=37#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message32.field37 JGo_TX2_Message32.canonical37
  · have same : i=38#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message32.field38 JGo_TX2_Message32.canonical38
  · have same : i=39#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message32.field39 JGo_TX2_Message32.canonical39
  · have same : i=40#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message40.field40 JGo_TX2_Message40.canonical40
  · have same : i=41#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message40.field41 JGo_TX2_Message40.canonical41
  · have same : i=42#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message40.field42 JGo_TX2_Message40.canonical42
  · have same : i=43#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message40.field43 JGo_TX2_Message40.canonical43
  · have same : i=44#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message40.field44 JGo_TX2_Message40.canonical44
  · have same : i=45#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message40.field45 JGo_TX2_Message40.canonical45
  · have same : i=46#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message40.field46 JGo_TX2_Message40.canonical46
  · have same : i=47#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message40.field47 JGo_TX2_Message40.canonical47
  · have same : i=48#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message48.field48 JGo_TX2_Message48.canonical48
  · have same : i=49#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message48.field49 JGo_TX2_Message48.canonical49
  · have same : i=50#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message48.field50 JGo_TX2_Message48.canonical50
  · have same : i=51#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message48.field51 JGo_TX2_Message48.canonical51
  · have same : i=52#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message48.field52 JGo_TX2_Message48.canonical52
  · have same : i=53#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message48.field53 JGo_TX2_Message48.canonical53
  · have same : i=54#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message48.field54 JGo_TX2_Message48.canonical54
  · have same : i=55#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message48.field55 JGo_TX2_Message48.canonical55
  · have same : i=56#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message56.field56 JGo_TX2_Message56.canonical56
  · have same : i=57#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message56.field57 JGo_TX2_Message56.canonical57
  · have same : i=58#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message56.field58 JGo_TX2_Message56.canonical58
  · have same : i=59#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message56.field59 JGo_TX2_Message56.canonical59
  · have same : i=60#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message56.field60 JGo_TX2_Message56.canonical60
  · have same : i=61#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message56.field61 JGo_TX2_Message56.canonical61
  · have same : i=62#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message56.field62 JGo_TX2_Message56.canonical62
  · have same : i=63#usize := UScalar.eq_of_val_eq h
    rw [same]
    exact JGv_DotFieldLift.source _ _ _ JGo_TX2_Message56.field63 JGo_TX2_Message56.canonical63
#print axioms source
end AspisR1.JGv_DotFields
end
