import RPt_JFo_Prepared
import Port4B_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGr_Count0
open Aeneas Aeneas.Std Result OraclePortFrozenOrder MultiproofConeCountGroups MultiproofConeCountLevels
def indices00 : List Nat := [65593,93499,147529,159813,183859,192317,193093,209371,216823,245899]
def indices01 : List Nat := [32796,46749,73764,79906,91929,96158,96546,104685,108411,122949]
def indices02 : List Nat := [16398,23374,36882,39953,45964,48079,48273,52342,54205,61474]
def indices03 : List Nat := [8199,11687,18441,19976,22982,24039,24136,26171,27102,30737]
def indices04 : List Nat := [4099,5843,9220,9988,11491,12019,12068,13085,13551,15368]
def indices05 : List Nat := [2049,2921,4610,4994,5745,6009,6034,6542,6775,7684]
def indices06 : List Nat := [1024,1460,2305,2497,2872,3004,3017,3271,3387,3842]
def indices07 : List Nat := [512,730,1152,1248,1436,1502,1508,1635,1693,1921]
def indices08 : List Nat := [256,365,576,624,718,751,754,817,846,960]
def indices09 : List Nat := [128,182,288,312,359,375,377,408,423,480]
def indices10 : List Nat := [64,91,144,156,179,187,188,204,211,240]
def indices11 : List Nat := [32,45,72,78,89,93,94,102,105,120]
def indices12 : List Nat := [16,22,36,39,44,46,47,51,52,60]
def indices13 : List Nat := [8,11,18,19,22,23,25,26,30]
def indices14 : List Nat := [4,5,9,11,12,13,15]
def indices15 : List Nat := [2,4,5,6,7]
def indices16 : List Nat := [1,2,3]
def indices17 : List Nat := [0,1]
def indices18 : List Nat := [0]
theorem level00 : sourceLevel indices00.length indices00=(indices01,10) := by rfl
#print axioms level00
theorem level01 : sourceLevel indices01.length indices01=(indices02,10) := by rfl
#print axioms level01
theorem level02 : sourceLevel indices02.length indices02=(indices03,10) := by rfl
#print axioms level02
theorem level03 : sourceLevel indices03.length indices03=(indices04,10) := by rfl
#print axioms level03
theorem level04 : sourceLevel indices04.length indices04=(indices05,10) := by rfl
#print axioms level04
theorem level05 : sourceLevel indices05.length indices05=(indices06,10) := by rfl
#print axioms level05
theorem level06 : sourceLevel indices06.length indices06=(indices07,10) := by rfl
#print axioms level06
theorem level07 : sourceLevel indices07.length indices07=(indices08,10) := by rfl
#print axioms level07
theorem level08 : sourceLevel indices08.length indices08=(indices09,10) := by rfl
#print axioms level08
theorem level09 : sourceLevel indices09.length indices09=(indices10,10) := by rfl
#print axioms level09
theorem level10 : sourceLevel indices10.length indices10=(indices11,10) := by rfl
#print axioms level10
theorem level11 : sourceLevel indices11.length indices11=(indices12,10) := by rfl
#print axioms level11
theorem level12 : sourceLevel indices12.length indices12=(indices13,8) := by rfl
#print axioms level12
theorem level13 : sourceLevel indices13.length indices13=(indices14,5) := by rfl
#print axioms level13
theorem level14 : sourceLevel indices14.length indices14=(indices15,3) := by rfl
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
theorem total14 : sourceCount 4 indices14=5 := by
  rw [sourceCount,level14]
  change 3+sourceCount 3 indices15=5
  rw [total15]
#print axioms total14
theorem total13 : sourceCount 5 indices13=10 := by
  rw [sourceCount,level13]
  change 5+sourceCount 4 indices14=10
  rw [total14]
#print axioms total13
theorem total12 : sourceCount 6 indices12=18 := by
  rw [sourceCount,level12]
  change 8+sourceCount 5 indices13=18
  rw [total13]
#print axioms total12
theorem total11 : sourceCount 7 indices11=28 := by
  rw [sourceCount,level11]
  change 10+sourceCount 6 indices12=28
  rw [total12]
#print axioms total11
theorem total10 : sourceCount 8 indices10=38 := by
  rw [sourceCount,level10]
  change 10+sourceCount 7 indices11=38
  rw [total11]
#print axioms total10
theorem total09 : sourceCount 9 indices09=48 := by
  rw [sourceCount,level09]
  change 10+sourceCount 8 indices10=48
  rw [total10]
#print axioms total09
theorem total08 : sourceCount 10 indices08=58 := by
  rw [sourceCount,level08]
  change 10+sourceCount 9 indices09=58
  rw [total09]
#print axioms total08
theorem total07 : sourceCount 11 indices07=68 := by
  rw [sourceCount,level07]
  change 10+sourceCount 10 indices08=68
  rw [total08]
#print axioms total07
theorem total06 : sourceCount 12 indices06=78 := by
  rw [sourceCount,level06]
  change 10+sourceCount 11 indices07=78
  rw [total07]
#print axioms total06
theorem total05 : sourceCount 13 indices05=88 := by
  rw [sourceCount,level05]
  change 10+sourceCount 12 indices06=88
  rw [total06]
#print axioms total05
theorem total04 : sourceCount 14 indices04=98 := by
  rw [sourceCount,level04]
  change 10+sourceCount 13 indices05=98
  rw [total05]
#print axioms total04
theorem total03 : sourceCount 15 indices03=108 := by
  rw [sourceCount,level03]
  change 10+sourceCount 14 indices04=108
  rw [total04]
#print axioms total03
theorem total02 : sourceCount 16 indices02=118 := by
  rw [sourceCount,level02]
  change 10+sourceCount 15 indices03=118
  rw [total03]
#print axioms total02
theorem total01 : sourceCount 17 indices01=128 := by
  rw [sourceCount,level01]
  change 10+sourceCount 16 indices02=128
  rw [total02]
#print axioms total01
theorem total00 : sourceCount 18 indices00=138 := by
  rw [sourceCount,level00]
  change 10+sourceCount 17 indices01=138
  rw [total01]
#print axioms total00
def frontier : Slice U32 := ⟨[65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32],by change 10≤Usize.max; scalar_tac⟩
theorem values : frontier.val.map UScalar.val=indices00 := by rfl
#print axioms values
theorem well : wellFormed indices00 := by simp [wellFormed,indices00,List.pairwise_cons]
#print axioms well
theorem source : Port4B_Install.leaves.op11 .Two frontier=ok (some 138#usize) := by
  change Port4B_CountInstall.nodeCount .Two frontier=_
  have count : Port4B_CountInstall.countValue indices00 well=138#usize := by
    apply UScalar.eq_of_val_eq
    change sourceCount 18 indices00=138
    exact total00
  rw [Port4B_CountInstall.nodeCount,values,dif_pos well,count]
#print axioms source
end AspisR1.JGr_Count0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGr_Count2
open Aeneas Aeneas.Std Result OraclePortFrozenOrder MultiproofConeCountGroups MultiproofConeCountLevels
def indices00 : List Nat := [16398,23374,36882,39953,45964,48079,48273,52342,54205,61474]
def indices01 : List Nat := [8199,11687,18441,19976,22982,24039,24136,26171,27102,30737]
def indices02 : List Nat := [4099,5843,9220,9988,11491,12019,12068,13085,13551,15368]
def indices03 : List Nat := [2049,2921,4610,4994,5745,6009,6034,6542,6775,7684]
def indices04 : List Nat := [1024,1460,2305,2497,2872,3004,3017,3271,3387,3842]
def indices05 : List Nat := [512,730,1152,1248,1436,1502,1508,1635,1693,1921]
def indices06 : List Nat := [256,365,576,624,718,751,754,817,846,960]
def indices07 : List Nat := [128,182,288,312,359,375,377,408,423,480]
def indices08 : List Nat := [64,91,144,156,179,187,188,204,211,240]
def indices09 : List Nat := [32,45,72,78,89,93,94,102,105,120]
def indices10 : List Nat := [16,22,36,39,44,46,47,51,52,60]
def indices11 : List Nat := [8,11,18,19,22,23,25,26,30]
def indices12 : List Nat := [4,5,9,11,12,13,15]
def indices13 : List Nat := [2,4,5,6,7]
def indices14 : List Nat := [1,2,3]
def indices15 : List Nat := [0,1]
def indices16 : List Nat := [0]
def indices17 : List Nat := [0]
def indices18 : List Nat := [0]
theorem level00 : sourceLevel indices00.length indices00=(indices01,10) := by rfl
#print axioms level00
theorem level01 : sourceLevel indices01.length indices01=(indices02,10) := by rfl
#print axioms level01
theorem level02 : sourceLevel indices02.length indices02=(indices03,10) := by rfl
#print axioms level02
theorem level03 : sourceLevel indices03.length indices03=(indices04,10) := by rfl
#print axioms level03
theorem level04 : sourceLevel indices04.length indices04=(indices05,10) := by rfl
#print axioms level04
theorem level05 : sourceLevel indices05.length indices05=(indices06,10) := by rfl
#print axioms level05
theorem level06 : sourceLevel indices06.length indices06=(indices07,10) := by rfl
#print axioms level06
theorem level07 : sourceLevel indices07.length indices07=(indices08,10) := by rfl
#print axioms level07
theorem level08 : sourceLevel indices08.length indices08=(indices09,10) := by rfl
#print axioms level08
theorem level09 : sourceLevel indices09.length indices09=(indices10,10) := by rfl
#print axioms level09
theorem level10 : sourceLevel indices10.length indices10=(indices11,8) := by rfl
#print axioms level10
theorem level11 : sourceLevel indices11.length indices11=(indices12,5) := by rfl
#print axioms level11
theorem level12 : sourceLevel indices12.length indices12=(indices13,3) := by rfl
#print axioms level12
theorem level13 : sourceLevel indices13.length indices13=(indices14,1) := by rfl
#print axioms level13
theorem level14 : sourceLevel indices14.length indices14=(indices15,1) := by rfl
#print axioms level14
theorem level15 : sourceLevel indices15.length indices15=(indices16,0) := by rfl
#print axioms level15
theorem level16 : sourceLevel indices16.length indices16=(indices17,1) := by rfl
#print axioms level16
theorem level17 : sourceLevel indices17.length indices17=(indices18,1) := by rfl
#print axioms level17
theorem total17 : sourceCount 1 indices17=1 := by
  rw [sourceCount,level17]
  rfl
#print axioms total17
theorem total16 : sourceCount 2 indices16=2 := by
  rw [sourceCount,level16]
  change 1+sourceCount 1 indices17=2
  rw [total17]
#print axioms total16
theorem total15 : sourceCount 3 indices15=2 := by
  rw [sourceCount,level15]
  change 0+sourceCount 2 indices16=2
  rw [total16]
#print axioms total15
theorem total14 : sourceCount 4 indices14=3 := by
  rw [sourceCount,level14]
  change 1+sourceCount 3 indices15=3
  rw [total15]
#print axioms total14
theorem total13 : sourceCount 5 indices13=4 := by
  rw [sourceCount,level13]
  change 1+sourceCount 4 indices14=4
  rw [total14]
#print axioms total13
theorem total12 : sourceCount 6 indices12=7 := by
  rw [sourceCount,level12]
  change 3+sourceCount 5 indices13=7
  rw [total13]
#print axioms total12
theorem total11 : sourceCount 7 indices11=12 := by
  rw [sourceCount,level11]
  change 5+sourceCount 6 indices12=12
  rw [total12]
#print axioms total11
theorem total10 : sourceCount 8 indices10=20 := by
  rw [sourceCount,level10]
  change 8+sourceCount 7 indices11=20
  rw [total11]
#print axioms total10
theorem total09 : sourceCount 9 indices09=30 := by
  rw [sourceCount,level09]
  change 10+sourceCount 8 indices10=30
  rw [total10]
#print axioms total09
theorem total08 : sourceCount 10 indices08=40 := by
  rw [sourceCount,level08]
  change 10+sourceCount 9 indices09=40
  rw [total09]
#print axioms total08
theorem total07 : sourceCount 11 indices07=50 := by
  rw [sourceCount,level07]
  change 10+sourceCount 10 indices08=50
  rw [total08]
#print axioms total07
theorem total06 : sourceCount 12 indices06=60 := by
  rw [sourceCount,level06]
  change 10+sourceCount 11 indices07=60
  rw [total07]
#print axioms total06
theorem total05 : sourceCount 13 indices05=70 := by
  rw [sourceCount,level05]
  change 10+sourceCount 12 indices06=70
  rw [total06]
#print axioms total05
theorem total04 : sourceCount 14 indices04=80 := by
  rw [sourceCount,level04]
  change 10+sourceCount 13 indices05=80
  rw [total05]
#print axioms total04
theorem total03 : sourceCount 15 indices03=90 := by
  rw [sourceCount,level03]
  change 10+sourceCount 14 indices04=90
  rw [total04]
#print axioms total03
theorem total02 : sourceCount 16 indices02=100 := by
  rw [sourceCount,level02]
  change 10+sourceCount 15 indices03=100
  rw [total03]
#print axioms total02
theorem total01 : sourceCount 17 indices01=110 := by
  rw [sourceCount,level01]
  change 10+sourceCount 16 indices02=110
  rw [total02]
#print axioms total01
theorem total00 : sourceCount 18 indices00=120 := by
  rw [sourceCount,level00]
  change 10+sourceCount 17 indices01=120
  rw [total01]
#print axioms total00
def frontier : Slice U32 := ⟨[16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32],by change 10≤Usize.max; scalar_tac⟩
theorem values : frontier.val.map UScalar.val=indices00 := by rfl
#print axioms values
theorem well : wellFormed indices00 := by simp [wellFormed,indices00,List.pairwise_cons]
#print axioms well
theorem source : Port4B_Install.leaves.op11 .Two frontier=ok (some 120#usize) := by
  change Port4B_CountInstall.nodeCount .Two frontier=_
  have count : Port4B_CountInstall.countValue indices00 well=120#usize := by
    apply UScalar.eq_of_val_eq
    change sourceCount 18 indices00=120
    exact total00
  rw [Port4B_CountInstall.nodeCount,values,dif_pos well,count]
#print axioms source
end AspisR1.JGr_Count2
end
