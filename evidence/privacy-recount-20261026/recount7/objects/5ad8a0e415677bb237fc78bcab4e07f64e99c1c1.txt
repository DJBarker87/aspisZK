import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_19_0 : Fin 16 → Scalar := ![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803,1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,1546489432]
def s_19_1 : Fin 16 → Scalar := ![1095691683,1738382790,1932965182,1343418881,52350442,619563626,1982589172,1853158690,1095691683,1738382790,1932965182,1343418881,1148313071,1715526255,975509765,1897600301]
theorem round_19_1 : poseidonExternalLinear s_19_0 = s_19_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_1
def s_19_2 : Fin 16 → Scalar := ![632640798,919577867,567760648,193225404,1333131270,1959597494,543988226,2042738296,1523956007,247400239,615904786,513204232,957682291,772530777,937824050,922950045]
theorem round_19_2 : poseidonFullRound s_19_1 (poseidonExternalInitial 0) = s_19_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_2
def s_19_3 : Fin 16 → Scalar := ![89322514,40583132,710367919,37339893,101447560,339210064,180670018,113415279,2022580529,678777267,483501645,1546769479,1370017721,1506302473,1082799573,579691826]
theorem round_19_3 : poseidonFullRound s_19_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_19_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_3
def s_19_4 : Fin 16 → Scalar := ![1804428867,838123301,94015122,316917943,1280196530,1504587257,309244838,1782944928,927027688,2010832039,975377137,27085745,1095197662,1850776134,75601557,758288061]
theorem round_19_4 : poseidonFullRound s_19_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_19_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_4
def s_19_5 : Fin 16 → Scalar := ![672924914,1095368232,1377519441,988596925,1854190419,470166966,813482868,1263281484,2111226944,1640791789,2055317201,1034254616,1703530628,919324046,148967605,1754968987]
theorem round_19_5 : poseidonFullRound s_19_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_19_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_5
def s_19_6 : Fin 16 → Scalar := ![1676682400,1373440135,885627138,2084975956,79209726,1358292418,539719915,1671191940,2079664860,1561458722,388911667,1747227155,1252238273,32941509,418222912,1143921556]
theorem round_19_6 : poseidonInternalRound s_19_5 (poseidonInternalConstants 0) = s_19_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_6
def s_19_7 : Fin 16 → Scalar := ![1796266383,599006811,996820952,1123019559,2006728131,1630892541,1464218427,955152133,1282180175,1674524813,186638989,452481752,1179601020,2068338382,460795585,762027569]
theorem round_19_7 : poseidonInternalRound s_19_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_19_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_7
def s_19_8 : Fin 16 → Scalar := ![1883605155,188000629,1582635722,1933588407,610433337,2060954357,1346826895,589188214,499299046,918100193,1728757618,1823346296,1351621805,2100578493,2128684688,95544817]
theorem round_19_8 : poseidonInternalRound s_19_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_19_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_8
def s_19_9 : Fin 16 → Scalar := ![340408120,1255491544,2085278712,211909955,1655990317,1830505922,1216278615,120830965,553259393,2025422800,1788766619,545795065,1127633543,1372593405,1391009092,630303175]
theorem round_19_9 : poseidonInternalRound s_19_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_19_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_9
def s_19_10 : Fin 16 → Scalar := ![955766906,1562124530,182223116,1154272806,669653640,1677440327,572843020,1597363805,256874939,1271310859,200099951,352742699,1553451495,428229122,552152067,1007559741]
theorem round_19_10 : poseidonInternalRound s_19_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_19_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_10
def s_19_11 : Fin 16 → Scalar := ![1469709131,399295869,1349101218,1306778916,2046916812,2053896454,2135762450,136723450,1652392473,22720546,1876058345,562255659,871209904,1261515085,1353860467,1592663206]
theorem round_19_11 : poseidonInternalRound s_19_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_19_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_11
def s_19_12 : Fin 16 → Scalar := ![1237951444,2043907781,47847054,429276635,840077232,147216824,1269533608,1804978124,549967403,1018620747,730493127,393837945,360502852,777662177,79731195,2125301540]
theorem round_19_12 : poseidonInternalRound s_19_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_19_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_12
def s_19_13 : Fin 16 → Scalar := ![868386441,643626064,842896038,316824823,1025368845,955187467,570088093,301684928,276069163,1668591875,1447854822,1147205753,1196550889,943832247,2038884938,867066597]
theorem round_19_13 : poseidonInternalRound s_19_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_19_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_13
def s_19_14 : Fin 16 → Scalar := ![224333835,985469902,2027635914,1609143130,2102343657,592457781,1404793638,322326407,1318958350,152118085,1181465136,602388490,1371361618,59636639,159750405,2001045210]
theorem round_19_14 : poseidonInternalRound s_19_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_19_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_14
def s_19_15 : Fin 16 → Scalar := ![1759133817,943353751,1865672030,2099489075,1744247576,847273757,1961607325,1259421074,1280828183,245407963,744889852,2029912133,665301048,2087001487,1241507150,72895060]
theorem round_19_15 : poseidonInternalRound s_19_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_19_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_15
def s_19_16 : Fin 16 → Scalar := ![1130911513,1482835167,2123341829,347503128,1608560142,1210959646,1033890053,1685535213,1276731668,1086894181,949995179,2897000,372170546,1737216890,315563848,1786502648]
theorem round_19_16 : poseidonInternalRound s_19_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_19_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_16
def s_19_17 : Fin 16 → Scalar := ![488870005,675421086,1291785930,582598431,1323648820,1388071079,64812910,1840140848,1552965898,412105792,1325040771,321279684,734403658,1153337988,1602480525,769174454]
theorem round_19_17 : poseidonInternalRound s_19_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_19_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_17
def s_19_18 : Fin 16 → Scalar := ![1723803971,1108865452,869532579,616354443,285216691,1167745160,359973839,90858053,1644583786,705828415,65528966,2135038066,1566515455,1014429805,245151122,1166815679]
theorem round_19_18 : poseidonInternalRound s_19_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_19_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_18
def s_19_19 : Fin 16 → Scalar := ![583548242,840388468,1470588174,49457141,2013256544,1235576400,513267629,1251471114,1932333865,34970908,261191143,294030768,1411339551,773504003,1254648932,566159584]
theorem round_19_19 : poseidonInternalRound s_19_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_19_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_19
def s_19_20 : Fin 16 → Scalar := ![946432929,1966291417,1700610166,747812097,786808069,141543240,1319271352,2042640589,150233968,1232966713,392384886,300641990,109217419,1369633564,734957738,1287051545]
theorem round_19_20 : poseidonFullRound s_19_19 (poseidonExternalFinal 0) = s_19_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_20
def s_19_21 : Fin 16 → Scalar := ![551081507,1102893820,1700495832,2067506477,1472966816,855758171,2133849360,1304566923,1607772786,2077146555,1387374041,1205670139,2059295988,55053940,720893276,177236503]
theorem round_19_21 : poseidonFullRound s_19_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_19_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_21
def s_19_22 : Fin 16 → Scalar := ![244797523,1025288427,2078434048,2037305380,1141733285,162928332,1873313062,1478215448,2058065737,25472682,1076319802,801203889,510994598,710395898,1943751955,345414681]
theorem round_19_22 : poseidonFullRound s_19_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_19_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_22
def s_19_23 : Fin 16 → Scalar := ![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443,1565763859,466615194,85454389,1827383417,30837075,880695140,368266061,1590058256]
theorem round_19_23 : poseidonFullRound s_19_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_19_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_19_23
theorem permutation_19 : poseidonPermutation s_19_0 = s_19_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_19_1,round_19_2,round_19_3,round_19_4,round_19_5,round_19_6,round_19_7,round_19_8,round_19_9,round_19_10,round_19_11,round_19_12,round_19_13,round_19_14,round_19_15,round_19_16,round_19_17,round_19_18,round_19_19,round_19_20,round_19_21,round_19_22,round_19_23]
#print axioms permutation_19
theorem parent_19 : nodeCompress (![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] : Fin 8 → Scalar) ![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] = ![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1519171444,1235587172,1671492368,1449613582,547369941,1621086153,266860322,450526803] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_19_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_19]
  funext i
  fin_cases i <;> rfl
#print axioms parent_19
end R1Z.PV_RunJoin_RootModel
