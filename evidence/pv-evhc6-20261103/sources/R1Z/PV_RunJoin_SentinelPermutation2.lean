import R1Z.PV_RunJoin_SentinelPermutation1
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Sentinel
open R0P
def s_2_0 : Fin 16 → Scalar := ![610923033,126079819,1982917466,933735870,584773491,1304060905,1184384122,1101204160,1241709131,291159182,1920935269,477452604,517989461,1708406445,652837039,1855831084]
def s_2_1 : Fin 16 → Scalar := ![761174700,497118517,1968743808,370396450,1464270173,598799405,2025913534,1006332146,1999719522,815833484,1271795077,1453285378,619334927,500692130,1416778003,40548714]
theorem round_2_1 : poseidonExternalLinear s_2_0 = s_2_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_1
def s_2_2 : Fin 16 → Scalar := ![517870518,766030585,1679737726,876570802,1157488556,534904700,901262929,1151221750,1866651866,5087512,187841385,664017602,460832059,1199365754,142349329,1890448261]
theorem round_2_2 : poseidonFullRound s_2_1 (poseidonExternalInitial 0) = s_2_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_2
def s_2_3 : Fin 16 → Scalar := ![321586733,1336220967,739851012,724569205,1912339620,1371450650,1025549762,516818937,2000893132,626305916,976952625,1131794811,1815836220,1186086782,1714443285,1612737083]
theorem round_2_3 : poseidonFullRound s_2_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_2_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_3
def s_2_4 : Fin 16 → Scalar := ![236083993,229054494,1558444880,240874016,182782554,577686495,1826676041,2038507686,428873409,285491390,1602240141,1653884963,631956031,1204955360,1850973619,1958348401]
theorem round_2_4 : poseidonFullRound s_2_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_2_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_4
def s_2_5 : Fin 16 → Scalar := ![1628038568,534634968,1373347503,685679214,834854644,2005475485,636714880,1040895763,1541872002,827483676,296517522,1482681661,923786792,1825154533,1150386374,332707660]
theorem round_2_5 : poseidonFullRound s_2_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_2_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_5
def s_2_6 : Fin 16 → Scalar := ![828419102,625830162,690406553,686428403,327581405,2114031896,1138718531,136530969,2029799573,1473618844,929943495,71524934,20223230,1860763038,1171442635,1018932963]
theorem round_2_6 : poseidonInternalRound s_2_5 (poseidonInternalConstants 0) = s_2_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_6
def s_2_7 : Fin 16 → Scalar := ![2134460533,1313119127,2068102071,1285518930,1160456558,152060949,619059958,835336393,656113022,2124074804,1614172224,1595642637,999748306,1751050745,249362520,1473948668]
theorem round_2_7 : poseidonInternalRound s_2_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_2_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_7
def s_2_8 : Fin 16 → Scalar := ![627547360,2121367239,649484960,1655356538,1501965988,1093739649,1290813945,582686089,1038852695,1258035245,158197298,1767751443,243741206,1789613919,744026637,1546228453]
theorem round_2_8 : poseidonInternalRound s_2_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_2_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_8
def s_2_9 : Fin 16 → Scalar := ![1195727201,1449624294,627226975,1654715913,606566724,1795705910,1979597649,112944752,1304899548,1410216372,261016682,870793546,1043908544,768473460,1358737527,1792785521]
theorem round_2_9 : poseidonInternalRound s_2_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_2_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_9
def s_2_10 : Fin 16 → Scalar := ![2100885183,1210911240,1015740896,2085183304,318853444,575294095,831385951,547300133,1432188271,2146909129,754397086,1708797342,180197040,1881316872,1241602078,775380185]
theorem round_2_10 : poseidonInternalRound s_2_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_2_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_10
def s_2_11 : Fin 16 → Scalar := ![2069387553,340183114,1160753666,1027554149,1680099426,1891526453,2111302189,1944225681,2060744214,1129678913,685258665,1861462780,2129641712,1939600978,2015955010,687020720]
theorem round_2_11 : poseidonInternalRound s_2_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_2_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_11
def s_2_12 : Fin 16 → Scalar := ![988439250,1732086264,1565926835,1207152452,1947796676,1591555340,234096494,1268295208,1026673961,679412533,869623541,229019533,1259659626,1351318396,1461205463,1839666068]
theorem round_2_12 : poseidonInternalRound s_2_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_2_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_12
def s_2_13 : Fin 16 → Scalar := ![714055130,1037785915,290069674,1986825812,2003171177,1148264974,354336518,1019698024,1870947839,1436616339,741975777,1066836727,1925915655,897382792,1938401370,1781705872]
theorem round_2_13 : poseidonInternalRound s_2_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_2_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_13
def s_2_14 : Fin 16 → Scalar := ![1193578042,189371157,1879208237,656437549,144569129,343955650,1900419230,2135233015,262223817,1853148036,873053499,933081036,837760140,198202008,563850083,2046757950]
theorem round_2_14 : poseidonInternalRound s_2_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_2_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_14
def s_2_15 : Fin 16 → Scalar := ![1771258599,135366219,1556927889,424261611,1102548094,1154318168,629868306,1309438261,1298388933,1905489938,599580886,1472510505,1666809777,292419870,1383699665,151447348]
theorem round_2_15 : poseidonInternalRound s_2_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_2_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_15
def s_2_16 : Fin 16 → Scalar := ![1566960061,817269687,1648275599,231466265,912353632,1971124980,1510336437,734089939,1519446073,1008539727,472407690,1950851172,1486569026,653037091,1930287077,265885562]
theorem round_2_16 : poseidonInternalRound s_2_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_2_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_16
def s_2_17 : Fin 16 → Scalar := ![1867082542,961812354,1293610218,1070407727,1000920782,1617771289,1230668417,2029142176,1360111781,632675139,706196652,44292692,1885725169,740712257,1955626712,538422141]
theorem round_2_17 : poseidonInternalRound s_2_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_2_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_17
def s_2_18 : Fin 16 → Scalar := ![1884599082,1001149579,479074014,26000839,1604252540,153874085,766020923,1055417669,187469786,942899284,1630203481,1073577309,1050048802,438866716,1103409561,768965944]
theorem round_2_18 : poseidonInternalRound s_2_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_2_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_18
def s_2_19 : Fin 16 → Scalar := ![1581659196,359631330,316629779,1609968754,1455083836,1820467111,248831170,333219510,1879777889,222529991,92052576,832114006,686261500,2122990186,848295707,1459327233]
theorem round_2_19 : poseidonInternalRound s_2_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_2_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_19
def s_2_20 : Fin 16 → Scalar := ![902963347,1309678057,1361955959,1185735330,1107344400,780094164,895207154,1277218022,1820219389,1547126449,476102619,894446537,2105738375,717720740,1514558535,322042458]
theorem round_2_20 : poseidonFullRound s_2_19 (poseidonExternalFinal 0) = s_2_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_20
def s_2_21 : Fin 16 → Scalar := ![295316488,1122376660,1563103270,1131541806,1346233181,488393208,491217391,641843236,1779725813,1448734030,1466879999,551776991,734337340,1336550979,1950869053,465829782]
theorem round_2_21 : poseidonFullRound s_2_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_2_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_21
def s_2_22 : Fin 16 → Scalar := ![618069300,1565057802,2018246712,1161512296,1565879221,1311040926,1387043714,1983964220,64447861,504667810,713200831,554560172,541832378,625192843,1489878971,2066150455]
theorem round_2_22 : poseidonFullRound s_2_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_2_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_22
def s_2_23 : Fin 16 → Scalar := ![109581603,2018382657,1175266929,551563770,389056008,563172097,1431420963,351017421,577252873,534492782,457882179,521839167,1510356726,1912197148,679163485,1361667582]
theorem round_2_23 : poseidonFullRound s_2_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_2_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_23
theorem permutation_2 : poseidonPermutation s_2_0 = s_2_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_2_1,round_2_2,round_2_3,round_2_4,round_2_5,round_2_6,round_2_7,round_2_8,round_2_9,round_2_10,round_2_11,round_2_12,round_2_13,round_2_14,round_2_15,round_2_16,round_2_17,round_2_18,round_2_19,round_2_20,round_2_21,round_2_22,round_2_23]
#print axioms permutation_2
end R1Z.PV_RunJoin_Sentinel
