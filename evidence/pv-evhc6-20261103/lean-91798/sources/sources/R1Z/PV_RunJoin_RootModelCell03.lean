import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_3_0 : Fin 16 → Scalar := ![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146,1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,346725128]
def s_3_1 : Fin 16 → Scalar := ![2018217069,816686711,886710852,2140600817,512185582,356042783,885334205,636708281,2018217069,816686711,886710852,2140600817,1608148211,1452005412,2025738445,681149892]
theorem round_3_1 : poseidonExternalLinear s_3_0 = s_3_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_1
def s_3_2 : Fin 16 → Scalar := ![1957088637,308219354,1207484171,829507398,1694236805,1153063074,370268216,1882982857,1876443049,1232374675,129685468,2071828055,555287095,331408408,453740080,1809813836]
theorem round_3_2 : poseidonFullRound s_3_1 (poseidonExternalInitial 0) = s_3_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_2
def s_3_3 : Fin 16 → Scalar := ![2084509909,570403168,1140921786,872120087,1211590728,456091901,1797421848,1566470291,59110815,417932640,406172548,2028658028,1010449177,1980515958,1630141016,1325249501]
theorem round_3_3 : poseidonFullRound s_3_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_3_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_3
def s_3_4 : Fin 16 → Scalar := ![1048521646,1438719942,789899178,1598850989,365442848,1234040631,1135764879,2126352073,354695191,771583075,769101345,391895952,1159913500,1366635053,772940231,973248833]
theorem round_3_4 : poseidonFullRound s_3_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_3_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_4
def s_3_5 : Fin 16 → Scalar := ![1616584543,272320015,2027556350,768169532,569629561,819521182,1630755736,1098125846,47676524,426268433,90236046,1331086531,584866668,1256189633,1783640848,179791853]
theorem round_3_5 : poseidonFullRound s_3_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_3_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_5
def s_3_6 : Fin 16 → Scalar := ![1860113197,561556217,49381608,1214430683,551305396,516673232,933812226,1849813642,2096863980,2039772700,349150485,2106171092,480964001,216910426,717606714,2032826968]
theorem round_3_6 : poseidonInternalRound s_3_5 (poseidonInternalConstants 0) = s_3_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_6
def s_3_7 : Fin 16 → Scalar := ![272142316,1659121583,1196328582,1660320804,1213041240,774402490,914785540,1374037869,1060698931,1440850345,2145376604,1532548199,522169313,872549165,688435068,1002731275]
theorem round_3_7 : poseidonInternalRound s_3_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_3_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_7
def s_3_8 : Fin 16 → Scalar := ![628293529,638400071,1371935652,1325594410,93673820,632300093,335128357,1018356224,1604755542,617263171,1116633750,1349485058,950349407,1173643416,451358624,976518688]
theorem round_3_8 : poseidonInternalRound s_3_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_3_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_8
def s_3_9 : Fin 16 → Scalar := ![2065457495,113931378,71918964,482941653,224921867,1002398207,1609704143,225820233,873294218,728596852,447191103,1490905144,109653076,2028167460,2022529297,1591587475]
theorem round_3_9 : poseidonInternalRound s_3_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_3_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_9
def s_3_10 : Fin 16 → Scalar := ![407813674,2130919727,13342630,1801271314,1668879638,875490485,1987913397,1437097732,2129498609,1706705172,379177363,1320966105,499338848,1350699311,616678731,718047865]
theorem round_3_10 : poseidonInternalRound s_3_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_3_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_10
def s_3_11 : Fin 16 → Scalar := ![131112824,617155111,660404291,1396353346,1099854253,1756664909,1969921972,266177058,479117814,1611062722,216798636,1799578318,261214312,672248120,141258169,809442960]
theorem round_3_11 : poseidonInternalRound s_3_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_3_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_11
def s_3_12 : Fin 16 → Scalar := ![719725564,1642129765,198299589,167937097,1233874090,1214325787,1785451995,880437190,75029083,1140171262,1835962277,1933888678,1998906146,694547271,1945397161,1537753020]
theorem round_3_12 : poseidonInternalRound s_3_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_3_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_12
def s_3_13 : Fin 16 → Scalar := ![2100817816,1749794419,504263832,779413042,1388722786,209524423,1407553672,621069992,1121452690,2081215381,1084845177,1395999606,584004311,54307265,977258754,1176996958]
theorem round_3_13 : poseidonInternalRound s_3_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_3_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_13
def s_3_14 : Fin 16 → Scalar := ![2084232253,2021119371,1279852616,1241493473,643689005,1476232073,215885869,1365098794,2083348570,486518032,903740701,1684242814,1988558795,983324854,1957515607,478847847]
theorem round_3_14 : poseidonInternalRound s_3_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_3_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_14
def s_3_15 : Fin 16 → Scalar := ![1341138104,1791696110,182798324,441583337,625121485,1915453437,236473606,1237553675,151221471,1912625052,1783086353,711668719,1380762884,142664881,452934672,364544120]
theorem round_3_15 : poseidonInternalRound s_3_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_3_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_15
def s_3_16 : Fin 16 → Scalar := ![1180153465,1502115133,76015671,1476752371,416423609,292902957,835123474,1604442931,1886898135,1863644466,229744545,570183068,123596002,669621391,214266702,1865778115]
theorem round_3_16 : poseidonInternalRound s_3_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_3_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_16
def s_3_17 : Fin 16 → Scalar := ![2124371420,862957089,1660356945,972884146,544747181,1899805621,314989360,1113458131,365634772,1859939265,543538513,515964195,394492603,1091243224,328091049,1571493710]
theorem round_3_17 : poseidonInternalRound s_3_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_3_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_17
def s_3_18 : Fin 16 → Scalar := ![163052519,861808767,1172081921,1742904615,61861832,330970556,1488576610,393211711,1702945907,1549417531,384024417,264285750,1866850366,1126472419,583208428,389887412]
theorem round_3_18 : poseidonInternalRound s_3_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_3_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_18
def s_3_19 : Fin 16 → Scalar := ![753953700,27584140,1509939215,1842426539,1808153676,166336975,1703070306,709004760,247003122,679672261,1564754627,1495932932,172923358,1962909598,1430053071,66776199]
theorem round_3_19 : poseidonInternalRound s_3_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_3_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_19
def s_3_20 : Fin 16 → Scalar := ![1064987000,944967821,923350905,1873660585,616515043,627458202,387806357,1899805104,1979561583,723050162,163207011,854670739,892302768,1308080979,1516453904,778924045]
theorem round_3_20 : poseidonFullRound s_3_19 (poseidonExternalFinal 0) = s_3_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_20
def s_3_21 : Fin 16 → Scalar := ![313275635,109535977,950168341,1863077945,1459761351,1490521661,2076241139,90445852,1502283468,107734091,1461121457,1272854911,1072161895,1173602775,279096911,1642883618]
theorem round_3_21 : poseidonFullRound s_3_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_3_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_21
def s_3_22 : Fin 16 → Scalar := ![276058761,1839200401,1292392872,154529416,542645589,1357960322,1330684355,1708902158,1522203871,1347017753,438975300,1758122484,2123700685,713292906,1396849253,1231097153]
theorem round_3_22 : poseidonFullRound s_3_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_3_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_22
def s_3_23 : Fin 16 → Scalar := ![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573,50201850,1265735350,1901385000,1073104840,188179905,1616936462,1651063637,785731865]
theorem round_3_23 : poseidonFullRound s_3_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_3_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_3_23
theorem permutation_3 : poseidonPermutation s_3_0 = s_3_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_3_1,round_3_2,round_3_3,round_3_4,round_3_5,round_3_6,round_3_7,round_3_8,round_3_9,round_3_10,round_3_11,round_3_12,round_3_13,round_3_14,round_3_15,round_3_16,round_3_17,round_3_18,round_3_19,round_3_20,round_3_21,round_3_22,round_3_23]
#print axioms permutation_3
theorem parent_3 : nodeCompress (![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] : Fin 8 → Scalar) ![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] = ![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_3_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_3]
  funext i
  fin_cases i <;> rfl
#print axioms parent_3
end R1Z.PV_RunJoin_RootModel
