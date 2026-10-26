import JFq_Weights00
import JFq_Weights01
import JFq_Weights02
import JFq_Weights03
import JFq_Weights04
import JFq_Weights05
import JFq_Weights06
import JFq_Weights07
import JFq_Weights08
import JFq_Weights09
import JFq_Weights10
import JFq_Weights11
import JFq_Weights12
import JFq_Weights13
import JFq_Weights14
import JFq_Weights15
import JFq_ReadSequence
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFq_WeightReads
open Aeneas Aeneas.Std Result AspisR1Stage2

def tail15 : List aspis_core.field.QM31 := JFq_WeightBlock15.values
theorem source15 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 4 1672#usize=ok (.Ok (tail15,1736#usize)) :=
  JFq_WeightBlock15.source
#print axioms source15

def tail14 : List aspis_core.field.QM31 := JFq_WeightBlock14.values ++ tail15
theorem source14 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 8 1608#usize=ok (.Ok (tail14,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 4 1608#usize 1672#usize 1736#usize
    JFq_WeightBlock14.values tail15 JFq_WeightBlock14.source source15
#print axioms source14

def tail13 : List aspis_core.field.QM31 := JFq_WeightBlock13.values ++ tail14
theorem source13 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 12 1544#usize=ok (.Ok (tail13,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 8 1544#usize 1608#usize 1736#usize
    JFq_WeightBlock13.values tail14 JFq_WeightBlock13.source source14
#print axioms source13

def tail12 : List aspis_core.field.QM31 := JFq_WeightBlock12.values ++ tail13
theorem source12 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 16 1480#usize=ok (.Ok (tail12,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 12 1480#usize 1544#usize 1736#usize
    JFq_WeightBlock12.values tail13 JFq_WeightBlock12.source source13
#print axioms source12

def tail11 : List aspis_core.field.QM31 := JFq_WeightBlock11.values ++ tail12
theorem source11 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 20 1416#usize=ok (.Ok (tail11,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 16 1416#usize 1480#usize 1736#usize
    JFq_WeightBlock11.values tail12 JFq_WeightBlock11.source source12
#print axioms source11

def tail10 : List aspis_core.field.QM31 := JFq_WeightBlock10.values ++ tail11
theorem source10 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 24 1352#usize=ok (.Ok (tail10,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 20 1352#usize 1416#usize 1736#usize
    JFq_WeightBlock10.values tail11 JFq_WeightBlock10.source source11
#print axioms source10

def tail09 : List aspis_core.field.QM31 := JFq_WeightBlock09.values ++ tail10
theorem source09 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 28 1288#usize=ok (.Ok (tail09,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 24 1288#usize 1352#usize 1736#usize
    JFq_WeightBlock09.values tail10 JFq_WeightBlock09.source source10
#print axioms source09

def tail08 : List aspis_core.field.QM31 := JFq_WeightBlock08.values ++ tail09
theorem source08 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 32 1224#usize=ok (.Ok (tail08,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 28 1224#usize 1288#usize 1736#usize
    JFq_WeightBlock08.values tail09 JFq_WeightBlock08.source source09
#print axioms source08

def tail07 : List aspis_core.field.QM31 := JFq_WeightBlock07.values ++ tail08
theorem source07 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 36 1160#usize=ok (.Ok (tail07,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 32 1160#usize 1224#usize 1736#usize
    JFq_WeightBlock07.values tail08 JFq_WeightBlock07.source source08
#print axioms source07

def tail06 : List aspis_core.field.QM31 := JFq_WeightBlock06.values ++ tail07
theorem source06 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 40 1096#usize=ok (.Ok (tail06,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 36 1096#usize 1160#usize 1736#usize
    JFq_WeightBlock06.values tail07 JFq_WeightBlock06.source source07
#print axioms source06

def tail05 : List aspis_core.field.QM31 := JFq_WeightBlock05.values ++ tail06
theorem source05 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 44 1032#usize=ok (.Ok (tail05,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 40 1032#usize 1096#usize 1736#usize
    JFq_WeightBlock05.values tail06 JFq_WeightBlock05.source source06
#print axioms source05

def tail04 : List aspis_core.field.QM31 := JFq_WeightBlock04.values ++ tail05
theorem source04 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 48 968#usize=ok (.Ok (tail04,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 44 968#usize 1032#usize 1736#usize
    JFq_WeightBlock04.values tail05 JFq_WeightBlock04.source source05
#print axioms source04

def tail03 : List aspis_core.field.QM31 := JFq_WeightBlock03.values ++ tail04
theorem source03 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 52 904#usize=ok (.Ok (tail03,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 48 904#usize 968#usize 1736#usize
    JFq_WeightBlock03.values tail04 JFq_WeightBlock03.source source04
#print axioms source03

def tail02 : List aspis_core.field.QM31 := JFq_WeightBlock02.values ++ tail03
theorem source02 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 56 840#usize=ok (.Ok (tail02,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 52 840#usize 904#usize 1736#usize
    JFq_WeightBlock02.values tail03 JFq_WeightBlock02.source source03
#print axioms source02

def tail01 : List aspis_core.field.QM31 := JFq_WeightBlock01.values ++ tail02
theorem source01 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 60 776#usize=ok (.Ok (tail01,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 56 776#usize 840#usize 1736#usize
    JFq_WeightBlock01.values tail02 JFq_WeightBlock01.source source02
#print axioms source01

def tail00 : List aspis_core.field.QM31 := JFq_WeightBlock00.values ++ tail01
theorem source00 : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 64 712#usize=ok (.Ok (tail00,1736#usize)) :=
  JFq_ReadSequence.join _ _ 4 60 712#usize 776#usize 1736#usize
    JFq_WeightBlock00.values tail01 JFq_WeightBlock00.source source01
#print axioms source00
end AspisR1.JFq_WeightReads
end
