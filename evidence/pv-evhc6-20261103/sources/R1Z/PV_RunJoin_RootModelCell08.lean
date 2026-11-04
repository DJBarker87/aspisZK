import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_8_0 : Fin 16 → Scalar := ![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631,673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,1807663260]
def s_8_1 : Fin 16 → Scalar := ![386440736,1500958331,1604437282,2117908344,1206069373,609565981,989911155,558701770,386440736,1500958331,1604437282,2117908344,154548355,1705528610,2130315395,603143381]
theorem round_8_1 : poseidonExternalLinear s_8_0 = s_8_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_1
def s_8_2 : Fin 16 → Scalar := ![434756091,978775248,740545746,338063333,712944872,975244345,1762171767,1919778047,1983341930,434258894,49943363,1378968897,1364573386,1834766943,1178544730,1878315437]
theorem round_8_2 : poseidonFullRound s_8_1 (poseidonExternalInitial 0) = s_8_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_2
def s_8_3 : Fin 16 → Scalar := ![209942031,1970135774,255984404,53061673,216782114,1744280962,562892825,463225462,1073857606,1899327327,1548673227,1501941987,1752795167,927168545,637086131,1314255616]
theorem round_8_3 : poseidonFullRound s_8_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_8_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_3
def s_8_4 : Fin 16 → Scalar := ![1126804579,1718603569,562681080,1638495417,699739168,1085222060,904408843,1157964787,2123732329,1208645087,224748275,1114880484,2116327411,736358193,638723268,1781907919]
theorem round_8_4 : poseidonFullRound s_8_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_8_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_4
def s_8_5 : Fin 16 → Scalar := ![1779066932,540230672,520404958,817654371,1544444109,756696448,1683717672,1473124642,2075630796,1394140879,1379077664,1754533112,1869508655,1176608992,104831080,828826597]
theorem round_8_5 : poseidonFullRound s_8_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_8_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_5
def s_8_6 : Fin 16 → Scalar := ![1874725619,144627995,645207239,727531160,1222531960,974122256,1943755299,1542577590,1144650630,22176945,883169180,691741213,913412326,1352906779,882875210,1280374744]
theorem round_8_6 : poseidonInternalRound s_8_5 (poseidonInternalConstants 0) = s_8_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_6
def s_8_7 : Fin 16 → Scalar := ![517434743,453226893,1599013376,1071239891,1498919990,862169465,231742703,249316896,794991542,1690929524,583223831,1149676953,1149347342,7061700,1611271441,171798804]
theorem round_8_7 : poseidonInternalRound s_8_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_8_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_7
def s_8_8 : Fin 16 → Scalar := ![1410749777,1668017701,117850266,1204783078,321248846,2124600366,40622716,2138686623,2041976775,301052258,1435539886,859952425,2099908024,949566670,1324424354,964448531]
theorem round_8_8 : poseidonInternalRound s_8_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_8_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_8
def s_8_9 : Fin 16 → Scalar := ![1069075042,1424561345,2139727823,280708662,179050765,1537894795,1056470556,1341017755,1284049557,1663994047,870572360,248495364,859063782,1085326056,2144236940,1116772756]
theorem round_8_9 : poseidonInternalRound s_8_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_8_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_9
def s_8_10 : Fin 16 → Scalar := ![988289479,540418640,1247829294,238691943,548263415,99853898,710660382,1189131382,265443419,2044054868,1523724077,1193103208,1409931867,2080845286,101944669,1692504751]
theorem round_8_10 : poseidonInternalRound s_8_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_8_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_10
def s_8_11 : Fin 16 → Scalar := ![1243846114,1152087313,959843614,1566436445,702808699,61847394,1877964427,1554149476,228687953,2051188660,1831995799,2037111716,1606469571,1877938372,1797511380,925179012]
theorem round_8_11 : poseidonInternalRound s_8_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_8_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_11
def s_8_12 : Fin 16 → Scalar := ![1400530251,1559291078,179407346,230498604,1734706063,1396762069,372523313,1088522467,1761974338,1525490857,1617678110,1442823906,826140581,1551280044,78633689,885644799]
theorem round_8_12 : poseidonInternalRound s_8_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_8_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_12
def s_8_13 : Fin 16 → Scalar := ![737505936,1112284965,2059292226,474988303,545740509,426350521,736321668,498955071,1747409863,1384113172,345486690,1632199966,575661742,256272538,1388822286,1130013682]
theorem round_8_13 : poseidonInternalRound s_8_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_8_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_13
def s_8_14 : Fin 16 → Scalar := ![433548355,1389275603,100607796,29460203,347947416,656148033,216963897,2145344124,607153814,275160915,1868043090,651458263,223892290,715723345,1879694709,880087395]
theorem round_8_14 : poseidonInternalRound s_8_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_8_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_14
def s_8_15 : Fin 16 → Scalar := ![545495371,1195381901,7321890,2071430757,442201979,1714540238,306500061,1816660473,212383198,1527823834,1421784628,1004461972,2128195087,956678158,1663851203,97833892]
theorem round_8_15 : poseidonInternalRound s_8_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_8_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_15
def s_8_16 : Fin 16 → Scalar := ![1150612030,966613708,1933359234,1614503894,1161363992,1434071851,989299171,73385141,1186477387,52109557,1832261860,1616285114,673138165,1650516673,532621675,1174491624]
theorem round_8_16 : poseidonInternalRound s_8_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_8_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_16
def s_8_17 : Fin 16 → Scalar := ![1514503351,1020853744,1773474857,69804671,755217384,1524553182,1647042450,455921766,1599490282,509384746,1537160845,1813466926,1811565867,1005327444,401687267,1428434726]
theorem round_8_17 : poseidonInternalRound s_8_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_8_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_17
def s_8_18 : Fin 16 → Scalar := ![910066461,457821245,836433568,1863669832,1183739279,207498296,602718373,698673114,160777132,990443657,1531643177,1399045071,672549195,1669721154,2145543741,228030613]
theorem round_8_18 : poseidonInternalRound s_8_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_8_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_18
def s_8_19 : Fin 16 → Scalar := ![2138811408,1845820967,913383211,252744462,120495719,413005164,1347634835,1005922431,492636148,1538505568,2127550660,242756695,467966960,1305207725,98185677,1263553817]
theorem round_8_19 : poseidonInternalRound s_8_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_8_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_19
def s_8_20 : Fin 16 → Scalar := ![239481709,1618332140,692785913,340128028,389421262,1795744105,1480514566,50174675,369453695,565127921,366956916,2002114633,1554218731,2073003438,9905010,1765536736]
theorem round_8_20 : poseidonFullRound s_8_19 (poseidonExternalFinal 0) = s_8_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_20
def s_8_21 : Fin 16 → Scalar := ![1851618327,2126928815,586181575,1389841391,1400394921,500965891,530744883,1305114885,863633608,153294125,283410795,1245284494,946668242,1447189058,132576336,632416993]
theorem round_8_21 : poseidonFullRound s_8_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_8_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_21
def s_8_22 : Fin 16 → Scalar := ![940645572,2053517872,27777319,1869696757,381631012,1530112623,1903805796,2027284550,1562076032,965834425,1886622110,1513515683,13418620,627793483,1862028852,275204076]
theorem round_8_22 : poseidonFullRound s_8_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_8_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_22
def s_8_23 : Fin 16 → Scalar := ![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718,1687363642,505936980,1770241955,645712015,1436503326,756902735,780351771,1599493554]
theorem round_8_23 : poseidonFullRound s_8_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_8_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_8_23
theorem permutation_8 : poseidonPermutation s_8_0 = s_8_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_8_1,round_8_2,round_8_3,round_8_4,round_8_5,round_8_6,round_8_7,round_8_8,round_8_9,round_8_10,round_8_11,round_8_12,round_8_13,round_8_14,round_8_15,round_8_16,round_8_17,round_8_18,round_8_19,round_8_20,round_8_21,round_8_22,round_8_23]
#print axioms permutation_8
theorem parent_8 : nodeCompress (![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] : Fin 8 → Scalar) ![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] = ![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![673192756,38070812,1453532835,1340577407,368420458,1834405704,270061815,711700631] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_8_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_8]
  funext i
  fin_cases i <;> rfl
#print axioms parent_8
end R1Z.PV_RunJoin_RootModel
