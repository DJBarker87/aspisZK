import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_16_0 : Fin 16 → Scalar := ![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477,1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,163202459]
def s_16_1 : Fin 16 → Scalar := ![632693651,1097793200,258473457,338891295,1801677062,799716762,959618985,1583656485,632693651,1097793200,258473457,338891295,750156044,1895679391,2100023225,1628098096]
theorem round_16_1 : poseidonExternalLinear s_16_0 = s_16_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_1
def s_16_2 : Fin 16 → Scalar := ![57397726,1086935753,1709731590,1587655184,248213891,1738135126,908960543,663962388,1203216253,712744454,1898601526,1749470004,55837324,1331007371,2124713946,2146675767]
theorem round_16_2 : poseidonFullRound s_16_1 (poseidonExternalInitial 0) = s_16_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_2
def s_16_3 : Fin 16 → Scalar := ![1382561670,708512093,681079757,1051354382,1660761996,1229663945,1999308037,1370110997,185904566,931215040,1276797748,1403617166,393264516,951484862,347958233,795639344]
theorem round_16_3 : poseidonFullRound s_16_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_16_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_3
def s_16_4 : Fin 16 → Scalar := ![927129467,569336211,152582151,377628132,405490882,71843053,1132838408,1769946622,1447642887,1862615135,1871201016,2083593548,1016787939,1819817913,238354746,1830559871]
theorem round_16_4 : poseidonFullRound s_16_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_16_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_4
def s_16_5 : Fin 16 → Scalar := ![2023146635,339110699,1750724059,1805654043,1149303097,747937632,1924596020,610001430,750062209,1653727781,1073201912,165026069,1658836202,1998403863,706670416,2091230471]
theorem round_16_5 : poseidonFullRound s_16_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_16_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_5
def s_16_6 : Fin 16 → Scalar := ![2003501487,824842666,1839696438,1265897198,1090222155,1715315844,1943262491,871117841,2004414251,785765444,2080346238,2122645433,395380535,1798941197,345757854,1107011530]
theorem round_16_6 : poseidonInternalRound s_16_5 (poseidonInternalConstants 0) = s_16_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_6
def s_16_7 : Fin 16 → Scalar := ![1081938661,1469432589,29015505,1413211421,776432575,172356016,551963872,561556925,1659060058,2084564416,615359811,1986480435,1196592967,284106496,314228223,1312173402]
theorem round_16_7 : poseidonInternalRound s_16_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_16_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_7
def s_16_8 : Fin 16 → Scalar := ![1541053283,864161317,1600243385,752607118,1311222034,4941337,2025187103,974633576,1301018746,467274768,310466621,1350535652,768949484,598496143,988536274,155641732]
theorem round_16_8 : poseidonInternalRound s_16_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_16_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_8
def s_16_9 : Fin 16 → Scalar := ![169571640,1872616493,2061458299,1871400001,760813213,1087516568,1389933062,1107978277,35130198,371711552,1098695324,884611096,1673091453,1358929886,721750260,597680278]
theorem round_16_9 : poseidonInternalRound s_16_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_16_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_9
def s_16_10 : Fin 16 → Scalar := ![2119396251,1327597457,1430413915,498130027,1246519374,1822860523,983166008,1646113988,1804162661,123857808,1385045359,17117691,179528786,1199264739,1677579880,1075442339]
theorem round_16_10 : poseidonInternalRound s_16_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_16_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_10
def s_16_11 : Fin 16 → Scalar := ![1742074560,206869302,1740099675,871791953,261492249,127752802,275813043,1151352021,31342224,522099635,1973996088,273857477,700272209,304869218,677867426,802589656]
theorem round_16_11 : poseidonInternalRound s_16_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_16_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_11
def s_16_12 : Fin 16 → Scalar := ![1140978528,1730151554,708514308,715482770,1467736597,1419843437,1759365040,47883951,1240119630,2036802698,2113164537,109560663,76913596,1453587042,312252852,1722011897]
theorem round_16_12 : poseidonInternalRound s_16_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_16_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_12
def s_16_13 : Fin 16 → Scalar := ![318724161,878470185,565347247,2010249711,152793172,390977153,1760908736,65407848,1117325040,878766745,512771990,1232195703,11788492,1272253176,437678659,506866926]
theorem round_16_13 : poseidonInternalRound s_16_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_16_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_13
def s_16_14 : Fin 16 → Scalar := ![104276919,739474715,991699024,1459552433,1083349906,1821671684,375509260,1899623155,1144688948,1486991962,953512422,348033568,1943050526,980762332,819507976,614815070]
theorem round_16_14 : poseidonInternalRound s_16_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_16_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_14
def s_16_15 : Fin 16 → Scalar := ![1815148596,36557376,1280480709,840325099,1521430968,526542194,575960746,613880349,1935863656,2009903061,736227051,1060919228,1765683736,634483295,798918141,729325167]
theorem round_16_15 : poseidonInternalRound s_16_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_16_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_15
def s_16_16 : Fin 16 → Scalar := ![1504198136,748073381,1124993776,1925332754,2145545514,546256521,1962390701,1345152695,1541444568,1998107988,841256132,1877256012,1890318772,117486158,1835503363,1222129238]
theorem round_16_16 : poseidonInternalRound s_16_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_16_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_16
def s_16_17 : Fin 16 → Scalar := ![1048136259,1140242975,494673499,1651049669,376664530,542339342,911646263,582596194,128578774,806706536,697506315,1641338486,378971301,1140034554,1591866849,1303812650]
theorem round_16_17 : poseidonInternalRound s_16_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_16_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_17
def s_16_18 : Fin 16 → Scalar := ![407128042,1739367043,1588471066,760871803,1464956661,686618952,1854517073,1378058485,2024821611,957567172,1881019824,1897747614,2018151945,112495198,514246470,1038123985]
theorem round_16_18 : poseidonInternalRound s_16_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_16_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_18
def s_16_19 : Fin 16 → Scalar := ![1771296830,1147434371,437525813,304070893,390302381,1804035972,770555195,1704464488,887195896,1879611249,1427019392,838975779,779686162,2135905881,1079701926,1619611328]
theorem round_16_19 : poseidonInternalRound s_16_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_16_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_19
def s_16_20 : Fin 16 → Scalar := ![102493434,515376903,1535524051,1191247957,1398873519,410238728,1963552885,1555676225,1378940714,1316488816,77054880,557812995,629753674,1929309911,1182350402,2114173410]
theorem round_16_20 : poseidonFullRound s_16_19 (poseidonExternalFinal 0) = s_16_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_20
def s_16_21 : Fin 16 → Scalar := ![1837759166,516715820,1351551144,553446025,2099034219,1907003445,1863056094,1079728562,1486190490,1393148835,1375682785,327749132,1299258694,1171869226,1384944599,44763691]
theorem round_16_21 : poseidonFullRound s_16_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_16_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_21
def s_16_22 : Fin 16 → Scalar := ![1087274445,509501773,744231544,910133299,1616799171,1109192386,299131932,355316570,422000030,1614483760,532993469,1426644542,1556322480,1142114478,53306896,530920529]
theorem round_16_22 : poseidonFullRound s_16_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_16_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_22
def s_16_23 : Fin 16 → Scalar := ![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353,701233224,1812188754,562447655,1604367107,314773713,155650608,883346428,1520501354]
theorem round_16_23 : poseidonFullRound s_16_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_16_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_16_23
theorem permutation_16 : poseidonPermutation s_16_0 = s_16_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_16_1,round_16_2,round_16_3,round_16_4,round_16_5,round_16_6,round_16_7,round_16_8,round_16_9,round_16_10,round_16_11,round_16_12,round_16_13,round_16_14,round_16_15,round_16_16,round_16_17,round_16_18,round_16_19,round_16_20,round_16_21,round_16_22,round_16_23]
#print axioms permutation_16
theorem parent_16 : nodeCompress (![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] : Fin 8 → Scalar) ![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] = ![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_16_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_16]
  funext i
  fin_cases i <;> rfl
#print axioms parent_16
end R1Z.PV_RunJoin_RootModel
