import R1Z.PV_RunJoin_SentinelPermutation0
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Sentinel
open R0P
def s_1_0 : Fin 16 → Scalar := ![820016634,1956929410,1636681145,160015189,2049520563,517511614,7712408,2135765442,1052160426,1760438459,984102268,2100198862,1388088310,2056866746,1028884314,340520453]
def s_1_1 : Fin 16 → Scalar := ![2099051879,456179880,1001440525,922985597,586587865,190659553,1313356296,1199644063,1113987759,277788812,1257519337,355747197,960232025,1728724646,995371667,332868011]
theorem round_1_1 : poseidonExternalLinear s_1_0 = s_1_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_1
def s_1_2 : Fin 16 → Scalar := ![163601464,1247895723,1011592819,1951821822,1406947265,694581921,377690129,2035268597,734056874,946992606,234451406,688965472,1551059128,1899052151,402562089,1666709698]
theorem round_1_2 : poseidonFullRound s_1_1 (poseidonExternalInitial 0) = s_1_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_2
def s_1_3 : Fin 16 → Scalar := ![1863485266,651115128,498724309,279960666,330952735,2115490709,1953785986,427832654,587203260,1190149483,605561961,1539386273,821742613,373214530,1180825545,2078224780]
theorem round_1_3 : poseidonFullRound s_1_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_1_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_3
def s_1_4 : Fin 16 → Scalar := ![1759193004,1505422430,931839127,354461358,2138598316,1224319458,848008104,1921037353,1529658655,1362522623,970567191,984211147,913920395,1856331934,1825258853,1002128625]
theorem round_1_4 : poseidonFullRound s_1_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_1_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_4
def s_1_5 : Fin 16 → Scalar := ![1687096777,167090697,830466675,502449315,1838354475,702365493,806733377,1202757854,1250107427,2135051280,773899427,1617948728,710960737,580217878,824637801,174466929]
theorem round_1_5 : poseidonFullRound s_1_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_1_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_5
def s_1_6 : Fin 16 → Scalar := ![1100981516,1531321603,877680609,1226544519,1038681177,1864660559,1409895206,1031322270,316708037,329028601,1415778411,1347686152,1578937746,743838789,1308963873,2025953222]
theorem round_1_6 : poseidonInternalRound s_1_5 (poseidonInternalConstants 0) = s_1_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_6
def s_1_7 : Fin 16 → Scalar := ![2064971140,1200613659,1424653274,280502838,1536290531,1586573589,1836265708,1249407926,1553215146,148751679,2022406842,758797858,33301407,1901797954,106600989,68205979]
theorem round_1_7 : poseidonInternalRound s_1_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_1_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_7
def s_1_8 : Fin 16 → Scalar := ![1558918391,991694968,492904210,913092661,1343987322,1553938616,569525496,296293634,1034124473,1364289134,561451809,418270468,2013267931,1008525322,1083878839,824651646]
theorem round_1_8 : poseidonInternalRound s_1_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_1_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_8
def s_1_9 : Fin 16 → Scalar := ![408624146,1605576469,1599689921,2118768498,628361842,1854579240,1658828197,249321254,1985311578,1979548991,14916521,157768123,630363293,1553577131,2071123767,1410693355]
theorem round_1_9 : poseidonInternalRound s_1_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_1_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_9
def s_1_10 : Fin 16 → Scalar := ![1690714225,297012958,1890816331,724059540,1570847578,447416918,234331265,1763094863,1555731774,797321140,1081052111,664574197,76845357,522966549,496821051,720146419]
theorem round_1_10 : poseidonInternalRound s_1_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_1_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_10
def s_1_11 : Fin 16 → Scalar := ![1182203197,1178565746,368218156,1630307301,563431530,1597772535,1937702327,2050474376,299240689,984818163,1924836247,2115682951,1186008761,705740074,640224049,1149158253]
theorem round_1_11 : poseidonInternalRound s_1_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_1_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_11
def s_1_12 : Fin 16 → Scalar := ![1774619824,1708569886,1266440452,608782403,742489086,324560936,259452841,763861737,178106686,1387867169,172333122,1270855791,1097755224,1323421108,623894229,1661256105]
theorem round_1_12 : poseidonInternalRound s_1_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_1_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_12
def s_1_13 : Fin 16 → Scalar := ![1426971674,1291087998,2115399016,2017647724,1227463506,480525794,1442558083,1225029046,905337450,541711621,2105459633,1654961367,879283131,1519051472,1451778191,684163433]
theorem round_1_13 : poseidonInternalRound s_1_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_1_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_13
def s_1_14 : Fin 16 → Scalar := ![1881589543,1985191386,629934126,174759696,1923876848,1940065151,1758805457,1786551040,613180050,1933324956,611185992,1957472688,1121360502,1645435553,1504117732,717782763]
theorem round_1_14 : poseidonInternalRound s_1_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_1_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_14
def s_1_15 : Fin 16 → Scalar := ![1705727907,83362066,1505522579,944693111,604283582,1221925685,692854129,768287596,1423289435,1255604253,1182368858,1497330124,1643328492,1699533888,278314206,227522760]
theorem round_1_15 : poseidonInternalRound s_1_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_1_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_15
def s_1_16 : Fin 16 → Scalar := ![1619339398,603176785,1383376230,3619869,1059116081,743272856,1216310377,298096982,164752404,1979440084,84748403,370706791,91838140,1410068709,2104151765,1472452958]
theorem round_1_16 : poseidonInternalRound s_1_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_1_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_16
def s_1_17 : Fin 16 → Scalar := ![2119617544,831495992,847588020,242798683,111313267,1383266668,495545625,2126656879,1989274096,158840019,1111337999,372396714,947085637,164973037,1963384145,1727696750]
theorem round_1_17 : poseidonInternalRound s_1_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_1_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_17
def s_1_18 : Fin 16 → Scalar := ![465153645,1396361998,112558399,1536060738,1455372142,1222296224,1389940477,1379436501,1788879948,425721577,408644072,1188417180,231987699,1948676288,273948893,823785931]
theorem round_1_18 : poseidonInternalRound s_1_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_1_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_18
def s_1_19 : Fin 16 → Scalar := ![659597106,1836169968,664924768,141599981,1345366871,669194731,1968230294,676914507,1783174732,2050349332,132026533,1998633148,360010583,912730613,715489334,335696406]
theorem round_1_19 : poseidonInternalRound s_1_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_1_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_19
def s_1_20 : Fin 16 → Scalar := ![188739112,1849363334,1295350757,475526330,1931687491,1096485125,1288761074,1388157893,2132590703,539653417,236594285,1424640160,577476112,304397901,749487549,823987032]
theorem round_1_20 : poseidonFullRound s_1_19 (poseidonExternalFinal 0) = s_1_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_20
def s_1_21 : Fin 16 → Scalar := ![631350397,629737971,1033652909,45110965,2068628921,344098612,624274722,1759051833,915827695,1629109491,680707547,1595677128,2083728757,1251070303,107987092,424570632]
theorem round_1_21 : poseidonFullRound s_1_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_1_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_21
def s_1_22 : Fin 16 → Scalar := ![282578927,1809631521,1501799364,945961481,1298450737,691677665,185726876,2040440478,1768462041,609197160,1779982460,250777283,1303675435,1075020953,756228459,1895050507]
theorem round_1_22 : poseidonFullRound s_1_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_1_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_22
def s_1_23 : Fin 16 → Scalar := ![610922330,126079099,1982917466,933735870,584773491,1304060905,1184384122,1101204160,1241709131,291159182,1920935269,477452604,517989461,1708406445,652837039,1855831084]
theorem round_1_23 : poseidonFullRound s_1_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_1_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_23
theorem permutation_1 : poseidonPermutation s_1_0 = s_1_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_1_1,round_1_2,round_1_3,round_1_4,round_1_5,round_1_6,round_1_7,round_1_8,round_1_9,round_1_10,round_1_11,round_1_12,round_1_13,round_1_14,round_1_15,round_1_16,round_1_17,round_1_18,round_1_19,round_1_20,round_1_21,round_1_22,round_1_23]
#print axioms permutation_1
end R1Z.PV_RunJoin_Sentinel
