import RPt_JFo_Prepared
import Port4B_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_Count0
open Aeneas Aeneas.Std Result OraclePortFrozenOrder MultiproofConeCountGroups MultiproofConeCountLevels
def indices00 : List Nat := [14297,21248,42158,55377,63860,132355,149624,166165,178080,179622,185637,218094]
def indices01 : List Nat := [7148,10624,21079,27688,31930,66177,74812,83082,89040,89811,92818,109047]
def indices02 : List Nat := [3574,5312,10539,13844,15965,33088,37406,41541,44520,44905,46409,54523]
def indices03 : List Nat := [1787,2656,5269,6922,7982,16544,18703,20770,22260,22452,23204,27261]
def indices04 : List Nat := [893,1328,2634,3461,3991,8272,9351,10385,11130,11226,11602,13630]
def indices05 : List Nat := [446,664,1317,1730,1995,4136,4675,5192,5565,5613,5801,6815]
def indices06 : List Nat := [223,332,658,865,997,2068,2337,2596,2782,2806,2900,3407]
def indices07 : List Nat := [111,166,329,432,498,1034,1168,1298,1391,1403,1450,1703]
def indices08 : List Nat := [55,83,164,216,249,517,584,649,695,701,725,851]
def indices09 : List Nat := [27,41,82,108,124,258,292,324,347,350,362,425]
def indices10 : List Nat := [13,20,41,54,62,129,146,162,173,175,181,212]
def indices11 : List Nat := [6,10,20,27,31,64,73,81,86,87,90,106]
def indices12 : List Nat := [3,5,10,13,15,32,36,40,43,45,53]
def indices13 : List Nat := [1,2,5,6,7,16,18,20,21,22,26]
def indices14 : List Nat := [0,1,2,3,8,9,10,11,13]
def indices15 : List Nat := [0,1,4,5,6]
def indices16 : List Nat := [0,2,3]
def indices17 : List Nat := [0,1]
def indices18 : List Nat := [0]
theorem level00 : sourceLevel indices00.length indices00=(indices01,12) := by rfl
#print axioms level00
theorem level01 : sourceLevel indices01.length indices01=(indices02,12) := by rfl
#print axioms level01
theorem level02 : sourceLevel indices02.length indices02=(indices03,12) := by rfl
#print axioms level02
theorem level03 : sourceLevel indices03.length indices03=(indices04,12) := by rfl
#print axioms level03
theorem level04 : sourceLevel indices04.length indices04=(indices05,12) := by rfl
#print axioms level04
theorem level05 : sourceLevel indices05.length indices05=(indices06,12) := by rfl
#print axioms level05
theorem level06 : sourceLevel indices06.length indices06=(indices07,12) := by rfl
#print axioms level06
theorem level07 : sourceLevel indices07.length indices07=(indices08,12) := by rfl
#print axioms level07
theorem level08 : sourceLevel indices08.length indices08=(indices09,12) := by rfl
#print axioms level08
theorem level09 : sourceLevel indices09.length indices09=(indices10,12) := by rfl
#print axioms level09
theorem level10 : sourceLevel indices10.length indices10=(indices11,12) := by rfl
#print axioms level10
theorem level11 : sourceLevel indices11.length indices11=(indices12,10) := by rfl
#print axioms level11
theorem level12 : sourceLevel indices12.length indices12=(indices13,11) := by rfl
#print axioms level12
theorem level13 : sourceLevel indices13.length indices13=(indices14,7) := by rfl
#print axioms level13
theorem level14 : sourceLevel indices14.length indices14=(indices15,1) := by rfl
#print axioms level14
theorem level15 : sourceLevel indices15.length indices15=(indices16,1) := by rfl
#print axioms level15
theorem level16 : sourceLevel indices16.length indices16=(indices17,1) := by rfl
#print axioms level16
theorem level17 : sourceLevel indices17.length indices17=(indices18,0) := by rfl
#print axioms level17
theorem total17 : sourceCount 1 indices17=0 := by
  rw [sourceCount,level17]
  rfl
#print axioms total17
theorem total16 : sourceCount 2 indices16=1 := by
  rw [sourceCount,level16]
  change 1+sourceCount 1 indices17=1
  rw [total17]
#print axioms total16
theorem total15 : sourceCount 3 indices15=2 := by
  rw [sourceCount,level15]
  change 1+sourceCount 2 indices16=2
  rw [total16]
#print axioms total15
theorem total14 : sourceCount 4 indices14=3 := by
  rw [sourceCount,level14]
  change 1+sourceCount 3 indices15=3
  rw [total15]
#print axioms total14
theorem total13 : sourceCount 5 indices13=10 := by
  rw [sourceCount,level13]
  change 7+sourceCount 4 indices14=10
  rw [total14]
#print axioms total13
theorem total12 : sourceCount 6 indices12=21 := by
  rw [sourceCount,level12]
  change 11+sourceCount 5 indices13=21
  rw [total13]
#print axioms total12
theorem total11 : sourceCount 7 indices11=31 := by
  rw [sourceCount,level11]
  change 10+sourceCount 6 indices12=31
  rw [total12]
#print axioms total11
theorem total10 : sourceCount 8 indices10=43 := by
  rw [sourceCount,level10]
  change 12+sourceCount 7 indices11=43
  rw [total11]
#print axioms total10
theorem total09 : sourceCount 9 indices09=55 := by
  rw [sourceCount,level09]
  change 12+sourceCount 8 indices10=55
  rw [total10]
#print axioms total09
theorem total08 : sourceCount 10 indices08=67 := by
  rw [sourceCount,level08]
  change 12+sourceCount 9 indices09=67
  rw [total09]
#print axioms total08
theorem total07 : sourceCount 11 indices07=79 := by
  rw [sourceCount,level07]
  change 12+sourceCount 10 indices08=79
  rw [total08]
#print axioms total07
theorem total06 : sourceCount 12 indices06=91 := by
  rw [sourceCount,level06]
  change 12+sourceCount 11 indices07=91
  rw [total07]
#print axioms total06
theorem total05 : sourceCount 13 indices05=103 := by
  rw [sourceCount,level05]
  change 12+sourceCount 12 indices06=103
  rw [total06]
#print axioms total05
theorem total04 : sourceCount 14 indices04=115 := by
  rw [sourceCount,level04]
  change 12+sourceCount 13 indices05=115
  rw [total05]
#print axioms total04
theorem total03 : sourceCount 15 indices03=127 := by
  rw [sourceCount,level03]
  change 12+sourceCount 14 indices04=127
  rw [total04]
#print axioms total03
theorem total02 : sourceCount 16 indices02=139 := by
  rw [sourceCount,level02]
  change 12+sourceCount 15 indices03=139
  rw [total03]
#print axioms total02
theorem total01 : sourceCount 17 indices01=151 := by
  rw [sourceCount,level01]
  change 12+sourceCount 16 indices02=151
  rw [total02]
#print axioms total01
theorem total00 : sourceCount 18 indices00=163 := by
  rw [sourceCount,level00]
  change 12+sourceCount 17 indices01=163
  rw [total01]
#print axioms total00
def frontier : Slice U32 := ⟨[14297#u32,21248#u32,42158#u32,55377#u32,63860#u32,132355#u32,149624#u32,166165#u32,178080#u32,179622#u32,185637#u32,218094#u32],by change 12≤Usize.max; scalar_tac⟩
theorem values : frontier.val.map UScalar.val=indices00 := by rfl
#print axioms values
theorem well : wellFormed indices00 := by simp [wellFormed,indices00,List.pairwise_cons]
#print axioms well
theorem source : Port4B_Install.leaves.op11 .Two frontier=ok (some 163#usize) := by
  change Port4B_CountInstall.nodeCount .Two frontier=_
  have count : Port4B_CountInstall.countValue indices00 well=163#usize := by
    apply UScalar.eq_of_val_eq
    change sourceCount 18 indices00=163
    exact total00
  rw [Port4B_CountInstall.nodeCount,values,dif_pos well,count]
#print axioms source
end AspisR1.JGf_TX2_Count0
end
