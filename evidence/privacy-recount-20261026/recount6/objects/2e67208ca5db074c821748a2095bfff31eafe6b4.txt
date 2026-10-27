import R1Z.PV_RunJoin_SentinelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Sentinel
open R0P
def s_0_3 : Fin 16 → Scalar := ![762016729,565510605,1906574424,327137009,1469492065,1000395838,1640999462,123535710,1310812671,526659980,2091127956,2086196313,479426859,1274515274,209172887,777693849]
theorem round_0_3 : poseidonFullRound s_0_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_0_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_3
def s_0_4 : Fin 16 → Scalar := ![1822354768,1403515575,1985732624,1390554222,427718679,1258225045,645991145,867355638,1953648337,400793745,2032338236,1070744521,967204077,1393308279,666263557,916747496]
theorem round_0_4 : poseidonFullRound s_0_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_0_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_4
def s_0_5 : Fin 16 → Scalar := ![2013032249,1693549659,76475413,422075573,915066585,368908306,1697279812,687239913,2007292098,1203078888,797452934,2025166584,1190006585,821262758,813779994,1398515942]
theorem round_0_5 : poseidonFullRound s_0_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_0_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_5
def s_0_6 : Fin 16 → Scalar := ![1139952903,575644139,1182528953,570396772,1907659866,489660082,1655440936,2063259619,264929031,1927611934,1577596683,382577830,2135248714,466073097,1667976720,1715782726]
theorem round_0_6 : poseidonInternalRound s_0_5 (poseidonInternalConstants 0) = s_0_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_6
def s_0_7 : Fin 16 → Scalar := ![2116776270,1263903721,905833841,822363023,917152981,2080369953,2122762006,1740372731,239437198,235675876,1239560430,63988952,1391419855,378032098,1343120745,1833750151]
theorem round_0_7 : poseidonInternalRound s_0_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_0_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_7
def s_0_8 : Fin 16 → Scalar := ![267740787,1939395351,339675665,1817460075,1570264537,1749156173,2031882765,390196770,1258681916,878973770,822536573,781234088,343745514,1010547314,1526202172,1993017799]
theorem round_0_8 : poseidonInternalRound s_0_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_0_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_8
def s_0_9 : Fin 16 → Scalar := ![1827977018,510137298,1397576924,1545614953,395440008,787436951,1313964664,2068498757,768237317,249727779,1182086722,902416012,1330415065,426499800,711826354,882323024]
theorem round_0_9 : poseidonInternalRound s_0_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_0_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_9
def s_0_10 : Fin 16 → Scalar := ![183962304,1353290839,1490823742,583162412,1859189958,557242875,2087833496,83087875,393282355,348955555,119179961,1319782206,1123857496,704089403,1747699,1620175283]
theorem round_0_10 : poseidonInternalRound s_0_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_0_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_10
def s_0_11 : Fin 16 → Scalar := ![1085046947,1789842438,1270715436,621717600,277685734,762503011,675230414,1459208305,1384569158,1722344152,70263784,1048127876,814764142,2102662314,1870577609,62456019]
theorem round_0_11 : poseidonInternalRound s_0_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_0_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_11
def s_0_12 : Fin 16 → Scalar := ![571152350,871771367,1623359801,1568799329,1303414801,544558870,1361949354,129463628,213122099,1915367853,165083394,1541382319,1398088964,1316099978,690767967,1243242578]
theorem round_0_12 : poseidonInternalRound s_0_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_0_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_12
def s_0_13 : Fin 16 → Scalar := ![339121806,93339460,320804048,1201798115,1058951913,1492059072,2001758128,1064789344,731393001,2076950592,763239083,1269108184,1983555377,1467791765,1976155016,837592721]
theorem round_0_13 : poseidonInternalRound s_0_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_0_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_13
def s_0_14 : Fin 16 → Scalar := ![1040731371,1371441375,1919710011,1790327081,1159782631,1528726950,909852601,705143227,407125575,401509011,1150875399,487314192,554993450,2056500569,703774565,1925164404]
theorem round_0_14 : poseidonInternalRound s_0_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_0_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_14
def s_0_15 : Fin 16 → Scalar := ![721383412,434801693,755296693,1929701348,1899170425,2048155048,261356139,1242853906,1783310037,917935725,738730338,89982687,1494305666,897745031,668904752,1973479612]
theorem round_0_15 : poseidonInternalRound s_0_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_0_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_15
def s_0_16 : Fin 16 → Scalar := ![898262835,1595742353,524050399,289811464,1321918531,1719166723,934402520,1246695705,1791358814,2076768737,1706563028,362839328,1856168632,1700030261,466269267,770668470]
theorem round_0_16 : poseidonInternalRound s_0_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_0_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_16
def s_0_17 : Fin 16 → Scalar := ![833317688,980111130,432469575,543614633,1369782437,1121232581,1367962006,1863482605,1045030387,608704640,1000704438,1663056188,933581361,1964747058,897045075,1392808551]
theorem round_0_17 : poseidonInternalRound s_0_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_0_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_17
def s_0_18 : Fin 16 → Scalar := ![116774577,872263531,757091551,2066610933,112993662,652004521,717263653,1043438536,512055823,1101717657,263797294,2099653812,601394746,1675565790,1656493512,200935002]
theorem round_0_18 : poseidonInternalRound s_0_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_0_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_18
def s_0_19 : Fin 16 → Scalar := ![216936047,1404600119,2046519690,208845732,1436285884,226990689,2009937014,740409835,1650972522,1251699023,77826122,42344305,830609602,1718780347,715076232,638904256]
theorem round_0_19 : poseidonInternalRound s_0_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_0_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_19
def s_0_20 : Fin 16 → Scalar := ![2062425436,1053000321,895617359,1399189988,1520096717,1255663492,1764783521,619268904,1444969759,1929813589,1054200481,1459670468,507847738,1054604320,1777046818,873135833]
theorem round_0_20 : poseidonFullRound s_0_19 (poseidonExternalFinal 0) = s_0_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_20
def s_0_21 : Fin 16 → Scalar := ![1001432613,1554034013,188901664,1527836795,398755270,1734656809,1103609659,1763565440,895357394,1407394186,1396413784,482803487,1879962288,614913847,1908485933,940979007]
theorem round_0_21 : poseidonFullRound s_0_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_0_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_21
def s_0_22 : Fin 16 → Scalar := ![508624232,78779457,2033712154,419048307,866652961,1709126591,2051823971,241717202,265888714,1018498456,1092419105,494317695,121994764,1057863807,35557680,883432964]
theorem round_0_22 : poseidonFullRound s_0_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_0_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_22
def s_0_23 : Fin 16 → Scalar := ![820016234,1956929333,1636680544,160014571,2049519928,517510962,7711739,2135764756,1052160426,1760438459,984102268,2100198862,1388088310,2056866746,1028884314,340520453]
theorem round_0_23 : poseidonFullRound s_0_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_0_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_23
theorem permutation_0 : poseidonPermutation s_0_0 = s_0_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_0_1,round_0_2,round_0_3,round_0_4,round_0_5,round_0_6,round_0_7,round_0_8,round_0_9,round_0_10,round_0_11,round_0_12,round_0_13,round_0_14,round_0_15,round_0_16,round_0_17,round_0_18,round_0_19,round_0_20,round_0_21,round_0_22,round_0_23]
#print axioms permutation_0
end R1Z.PV_RunJoin_Sentinel
