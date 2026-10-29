import PV_2TNV_PublicWindows
import R1Z.PV_RunJoin_RootModelTable
import R1Z.PV_RunJoin_OutputCell3917
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_PublicLiterals
open Aeneas Aeneas.Std R0P PV_2TNV_PublicEncoding PV_2TNV_PublicWindows
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

theorem digest_drop (bytes : List U8) (off start : Nat) :
    digest (bytes.drop off) start = digest bytes (off+start) := by
  funext i
  unfold digest word
  rw [List.drop_drop,Nat.add_assoc]

def d00 : Digest M := ![71235157,561336479,2021715933,831357912,593948515,110335229,1732475008,949858646]
theorem read00 : digest JFx_DataPublic00.bytes 112 = d00 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_00_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read00
def d01 : Digest M := ![1058347432,1215059768,718082286,2029394131,1184875844,2099153903,613239161,1649887145]
theorem read01 : digest JFx_DataPublic00.bytes 304 = d01 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_01_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read01
def d02 : Digest M := ![20384,20401,20418,20435,20452,20469,20486,20503]
theorem read02 : digest JFx_DataPublic00.bytes 336 = d02 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_02_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read02
def d03 : Digest M := ![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536]
theorem read03 : digest JFx_DataPublic00.bytes 368 = d03 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_03_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read03
def d04 : Digest M := ![560027647,109760138,2064904093,345398497,1214731266,366495038,459312327,480913462]
theorem read04 : digest JFx_DataPublic00.bytes 400 = d04 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_04_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read04
def d05 : Digest M := ![1603344092,1242405009,1153352827,393697509,714169239,2094351560,55834509,664305674]
theorem read05 : digest JFx_DataPublic00.bytes 432 = d05 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_05_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read05
def d06 : Digest M := ![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616]
theorem read06 : digest JFx_DataPublic00.bytes 464 = d06 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_06_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read06
def d07 : Digest M := ![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592]
theorem read07 : digest JFx_DataPublic00.bytes 496 = d07 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_07_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read07
def d08 : Digest M := ![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587]
theorem read08 : digest JFx_DataPublic00.bytes 528 = d08 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_08_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read08
def d09 : Digest M := ![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631]
theorem read09 : digest JFx_DataPublic00.bytes 560 = d09 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_09_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read09
def d10 : Digest M := ![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718]
theorem read10 : digest JFx_DataPublic00.bytes 592 = d10 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_10_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read10
def d11 : Digest M := ![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885]
theorem read11 : digest JFx_DataPublic00.bytes 624 = d11 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_11_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read11
def d12 : Digest M := ![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893]
theorem read12 : digest JFx_DataPublic00.bytes 656 = d12 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_12_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read12
def d13 : Digest M := ![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062]
theorem read13 : digest JFx_DataPublic00.bytes 688 = d13 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_13_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read13
def d14 : Digest M := ![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184]
theorem read14 : digest JFx_DataPublic00.bytes 720 = d14 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_14_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read14
def d15 : Digest M := ![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542]
theorem read15 : digest JFx_DataPublic00.bytes 752 = d15 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_15_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read15
def d16 : Digest M := ![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983]
theorem read16 : digest JFx_DataPublic00.bytes 784 = d16 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_16_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read16
def d17 : Digest M := ![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477]
theorem read17 : digest JFx_DataPublic00.bytes 816 = d17 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_17_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read17
def d18 : Digest M := ![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353]
theorem read18 : digest JFx_DataPublic00.bytes 848 = d18 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_18_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read18
def d19 : Digest M := ![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413]
theorem read19 : digest JFx_DataPublic00.bytes 880 = d19 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_19_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read19
def d20 : Digest M := ![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803]
theorem read20 : digest JFx_DataPublic00.bytes 912 = d20 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_20_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read20
def d21 : Digest M := ![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443]
theorem read21 : digest JFx_DataPublic00.bytes 944 = d21 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_21_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read21
def d22 : Digest M := ![67464615,2144218473,1164697229,2001687059,97906516,820214304,716699029,134105794]
theorem read22 : digest JFx_DataPublic00.bytes 992 = d22 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_22_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read22
def d23 : Digest M := ![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732]
theorem read23 : digest JFx_DataPublic00.bytes 1024 = d23 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_23_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read23
def d24 : Digest M := ![248012357,194341198,430781749,501414171,630694870,1921243919,1220508734,1000843895]
theorem read24 : digest JFx_DataPublic00.bytes 1056 = d24 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_24_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read24
def d25 : Digest M := ![560027647,109760138,2064904093,345398497,1214731266,366495038,459312327,480913462]
theorem read25 : digest JFx_DataPublic00.bytes 1088 = d25 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_25_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read25
def d26 : Digest M := ![1603344092,1242405009,1153352827,393697509,714169239,2094351560,55834509,664305674]
theorem read26 : digest JFx_DataPublic00.bytes 1120 = d26 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_26_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read26
def d27 : Digest M := ![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616]
theorem read27 : digest JFx_DataPublic00.bytes 1152 = d27 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_27_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read27
def d28 : Digest M := ![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592]
theorem read28 : digest JFx_DataPublic00.bytes 1184 = d28 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_28_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read28
def d29 : Digest M := ![244193611,984304317,1467689208,2063463197,1766003332,1300835127,1578947755,745931587]
theorem read29 : digest JFx_DataPublic00.bytes 1216 = d29 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_29_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read29
def d30 : Digest M := ![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631]
theorem read30 : digest JFx_DataPublic00.bytes 1248 = d30 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_30_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read30
def d31 : Digest M := ![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718]
theorem read31 : digest JFx_DataPublic00.bytes 1280 = d31 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_31_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read31
def d32 : Digest M := ![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885]
theorem read32 : digest JFx_DataPublic00.bytes 1312 = d32 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_32_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read32
def d33 : Digest M := ![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893]
theorem read33 : digest JFx_DataPublic00.bytes 1344 = d33 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_33_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read33
def d34 : Digest M := ![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062]
theorem read34 : digest JFx_DataPublic00.bytes 1376 = d34 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_34_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read34
def d35 : Digest M := ![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184]
theorem read35 : digest JFx_DataPublic00.bytes 1408 = d35 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_35_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read35
def d36 : Digest M := ![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542]
theorem read36 : digest JFx_DataPublic00.bytes 1440 = d36 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_36_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read36
def d37 : Digest M := ![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983]
theorem read37 : digest JFx_DataPublic00.bytes 1472 = d37 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_37_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read37
def d38 : Digest M := ![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477]
theorem read38 : digest JFx_DataPublic00.bytes 1504 = d38 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_38_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read38
def d39 : Digest M := ![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353]
theorem read39 : digest JFx_DataPublic00.bytes 1536 = d39 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_39_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read39
def d40 : Digest M := ![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413]
theorem read40 : digest JFx_DataPublic00.bytes 1568 = d40 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_40_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read40
def d41 : Digest M := ![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803]
theorem read41 : digest JFx_DataPublic00.bytes 1600 = d41 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_41_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read41
def d42 : Digest M := ![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443]
theorem read42 : digest JFx_DataPublic00.bytes 1632 = d42 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_42_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read42
def d43 : Digest M := ![71235157,561336479,2021715933,831357912,593948515,110335229,1732475008,949858646]
theorem read43 : digest JFx_DataPublic00.bytes 1744 = d43 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_43_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read43
def d44 : Digest M := ![8526811,109678668,1639079956,402852,1893371776,347120802,331397657,1970188241]
theorem read44 : digest JFx_DataPublic00.bytes 1776 = d44 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_44_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read44
def d45 : Digest M := ![1443258150,390107157,739124880,1925983251,420127778,800761649,949547039,74873928]
theorem read45 : digest JFx_DataPublic00.bytes 1816 = d45 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_45_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read45
def d46 : Digest M := ![109581603,2018382657,1175266929,551563770,389056008,563172097,1431420963,351017421]
theorem read46 : digest JFx_DataPublic00.bytes 1848 = d46 := by
  rw [digest_window _ _ _ PV_2TNV_ByteEncoding.digest_46_selected]
  funext i
  fin_cases i <;> rfl
#print axioms read46
theorem anchor : nativePublic.anchor = d43 := by
  change digest (JFx_DataPublic00.bytes.drop 1664) 80 = d43
  rw [digest_drop]
  exact read43
theorem nullifier : nativePublic.nullifier = d44 := by
  change digest (JFx_DataPublic00.bytes.drop 1664) 112 = d44
  rw [digest_drop]
  exact read44
theorem asset : nativePublic.assetId = 77 := by
  change (PV_2TNV_ByteEncoding.littleEndian
    (((JFx_DataPublic00.bytes.drop 1664).drop 144).take 4) : M) = 77
  rw [List.drop_drop]
  exact congrArg (fun n : Nat => (n : M)) PV_2TNV_ByteEncoding.asset_value
theorem recipient : nativePublic.recipient = some d45 := by
  change some (digest (JFx_DataPublic00.bytes.drop 1664) 152) = some d45
  rw [digest_drop]
  exact congrArg some read45
theorem change_value : nativePublic.change = d46 := by
  change digest (JFx_DataPublic00.bytes.drop 1664) 184 = d46
  rw [digest_drop]
  exact read46
theorem nextRoot : nativePublic.nextRoot = d22 := read22
theorem frontier00 : nativePublic.snapshotFrontier ⟨0,by decide⟩ = d02 := read02
theorem frontier01 : nativePublic.snapshotFrontier ⟨1,by decide⟩ = d03 := read03
theorem frontier02 : nativePublic.snapshotFrontier ⟨2,by decide⟩ = d04 := read04
theorem frontier03 : nativePublic.snapshotFrontier ⟨3,by decide⟩ = d05 := read05
theorem frontier04 : nativePublic.snapshotFrontier ⟨4,by decide⟩ = d06 := read06
theorem frontier05 : nativePublic.snapshotFrontier ⟨5,by decide⟩ = d07 := read07
theorem frontier06 : nativePublic.snapshotFrontier ⟨6,by decide⟩ = d08 := read08
theorem frontier07 : nativePublic.snapshotFrontier ⟨7,by decide⟩ = d09 := read09
theorem frontier08 : nativePublic.snapshotFrontier ⟨8,by decide⟩ = d10 := read10
theorem frontier09 : nativePublic.snapshotFrontier ⟨9,by decide⟩ = d11 := read11
theorem frontier10 : nativePublic.snapshotFrontier ⟨10,by decide⟩ = d12 := read12
theorem frontier11 : nativePublic.snapshotFrontier ⟨11,by decide⟩ = d13 := read13
theorem frontier12 : nativePublic.snapshotFrontier ⟨12,by decide⟩ = d14 := read14
theorem frontier13 : nativePublic.snapshotFrontier ⟨13,by decide⟩ = d15 := read15
theorem frontier14 : nativePublic.snapshotFrontier ⟨14,by decide⟩ = d16 := read16
theorem frontier15 : nativePublic.snapshotFrontier ⟨15,by decide⟩ = d17 := read17
theorem frontier16 : nativePublic.snapshotFrontier ⟨16,by decide⟩ = d18 := read18
theorem frontier17 : nativePublic.snapshotFrontier ⟨17,by decide⟩ = d19 := read19
theorem frontier18 : nativePublic.snapshotFrontier ⟨18,by decide⟩ = d20 := read20
theorem frontier19 : nativePublic.snapshotFrontier ⟨19,by decide⟩ = d21 := read21
theorem carry : nativePublic.nextFrontier ⟨1,by decide⟩ = d24 := read24

def pair : Digest M := ![1134794151,415789335,111944968,1818281472,628958070,505282998,905808425,2134856457]

theorem output_pair : AspisR1.SpendRelation.outputPair nativePublic = some pair := by
  change Option.map (fun r => nodeCompress r nativePublic.change) nativePublic.recipient = some pair
  rw [recipient,change_value]
  change some (nodeCompress d45 d46) = some pair
  exact congrArg some R1Z.PV_RunJoin_OutputModel16.node_39
#print axioms digest_drop
#print axioms anchor
#print axioms nullifier
#print axioms asset
#print axioms recipient
#print axioms change_value
#print axioms nextRoot
#print axioms carry
#print axioms output_pair
#print axioms frontier00
#print axioms frontier01
#print axioms frontier02
#print axioms frontier03
#print axioms frontier04
#print axioms frontier05
#print axioms frontier06
#print axioms frontier07
#print axioms frontier08
#print axioms frontier09
#print axioms frontier10
#print axioms frontier11
#print axioms frontier12
#print axioms frontier13
#print axioms frontier14
#print axioms frontier15
#print axioms frontier16
#print axioms frontier17
#print axioms frontier18
#print axioms frontier19
end AspisR1.PV_2TNV_PublicLiterals
