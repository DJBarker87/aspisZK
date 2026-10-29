import R1Z.PV_RunJoin_PathCell0616
import R1Z.PV_RunJoin_PathCell0716
import R1Z.PV_RunJoin_PathCell0816
import R1Z.PV_RunJoin_PathCell0916
import R1Z.PV_RunJoin_PathCell1016
import R1Z.PV_RunJoin_PathCell1116
import R1Z.PV_RunJoin_PathCell1216
import R1Z.PV_RunJoin_PathCell1316
import R1Z.PV_RunJoin_PathCell1416
import R1Z.PV_RunJoin_PathCell1516
import R1Z.PV_RunJoin_PathCell1616
import R1Z.PV_RunJoin_PathCell1716
import R1Z.PV_RunJoin_PathCell1816
import R1Z.PV_RunJoin_PathCell1916
import R1Z.PV_RunJoin_PathCell2016
import R1Z.PV_RunJoin_PathCell2116
import R1Z.PV_RunJoin_PathCell2216
import R1Z.PV_RunJoin_PathCell2316
import R1Z.PV_RunJoin_PathCell2416
import R1Z.PV_RunJoin_PathCell2516
import R1Z.PV_RunJoin_PathCell2616
import R1Z.PV_RunJoin_PathCell2716
import R1Z.PV_RunJoin_PathCell2816
import R1Z.PV_RunJoin_PathCell2916
import R1Z.PV_RunJoin_FixtureInputCommitment
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PathValues16
open R0P PV_RunJoin_PathModel16
attribute [local irreducible] nodeCompress poseidonPermutation
local notation "leaf" => digestOf PV_RunJoin_FixtureHashModel.s_3_23
theorem prefix_1 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 1 = (![1055864870,1015153496,899228473,2043224478,1075657363,1804637297,712143154,1156362644] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 0 < 24 by decide)]
  change nodeCompress _ _ = _
  trans nodeCompress (![2028667570,45893279,894642502,1930282162,1562116262,823639309,745717450,1034934647] : Fin 8 → Scalar) ![901,918,935,952,969,986,1003,1020]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_6
#print axioms prefix_1
theorem prefix_2 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 2 = (![1292573235,1255372443,1043307233,1891352131,920017154,1033317521,170537605,505604950] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 1 < 24 by decide),prefix_1]
  change nodeCompress _ _ = _
  trans nodeCompress (![2001,2018,2035,2052,2069,2086,2103,2120] : Fin 8 → Scalar) ![1055864870,1015153496,899228473,2043224478,1075657363,1804637297,712143154,1156362644]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_7
#print axioms prefix_2
theorem prefix_3 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 3 = (![1088882418,1343804471,734616548,13922508,2033036789,781570573,1154493927,1197511955] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 2 < 24 by decide),prefix_2]
  change nodeCompress _ _ = _
  trans nodeCompress (![1292573235,1255372443,1043307233,1891352131,920017154,1033317521,170537605,505604950] : Fin 8 → Scalar) ![2021,2038,2055,2072,2089,2106,2123,2140]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_8
#print axioms prefix_3
theorem prefix_4 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 4 = (![600625215,237354909,439972622,263907834,1075778621,569932161,1744169643,1373371366] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 3 < 24 by decide),prefix_3]
  change nodeCompress _ _ = _
  trans nodeCompress (![1088882418,1343804471,734616548,13922508,2033036789,781570573,1154493927,1197511955] : Fin 8 → Scalar) ![2041,2058,2075,2092,2109,2126,2143,2160]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_9
#print axioms prefix_4
theorem prefix_5 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 5 = (![1180202183,1734852885,1208353062,189889914,943421826,507090805,389529953,896398700] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 4 < 24 by decide),prefix_4]
  change nodeCompress _ _ = _
  trans nodeCompress (![600625215,237354909,439972622,263907834,1075778621,569932161,1744169643,1373371366] : Fin 8 → Scalar) ![2061,2078,2095,2112,2129,2146,2163,2180]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_10
#print axioms prefix_5
theorem prefix_6 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 6 = (![439700881,730194574,1601626633,1478607356,953523754,1749099081,333248178,1763090787] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 5 < 24 by decide),prefix_5]
  change nodeCompress _ _ = _
  trans nodeCompress (![1180202183,1734852885,1208353062,189889914,943421826,507090805,389529953,896398700] : Fin 8 → Scalar) ![2081,2098,2115,2132,2149,2166,2183,2200]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_11
#print axioms prefix_6
theorem prefix_7 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 7 = (![891777458,519287294,1981395871,1193798350,1897410699,1175699129,1224545956,757035799] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 6 < 24 by decide),prefix_6]
  change nodeCompress _ _ = _
  trans nodeCompress (![2101,2118,2135,2152,2169,2186,2203,2220] : Fin 8 → Scalar) ![439700881,730194574,1601626633,1478607356,953523754,1749099081,333248178,1763090787]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_12
#print axioms prefix_7
theorem prefix_8 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 8 = (![1134127212,1758195919,1492236623,1856566444,896074385,533821444,2118230281,1863638021] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 7 < 24 by decide),prefix_7]
  change nodeCompress _ _ = _
  trans nodeCompress (![891777458,519287294,1981395871,1193798350,1897410699,1175699129,1224545956,757035799] : Fin 8 → Scalar) ![2121,2138,2155,2172,2189,2206,2223,2240]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_13
#print axioms prefix_8
theorem prefix_9 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 9 = (![785640667,939877614,365887579,1554146132,884924304,1762346545,308452542,617980080] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 8 < 24 by decide),prefix_8]
  change nodeCompress _ _ = _
  trans nodeCompress (![1134127212,1758195919,1492236623,1856566444,896074385,533821444,2118230281,1863638021] : Fin 8 → Scalar) ![2141,2158,2175,2192,2209,2226,2243,2260]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_14
#print axioms prefix_9
theorem prefix_10 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 10 = (![1563279367,1990384079,1317503545,1053962530,1761249440,14780773,549276084,1614233662] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 9 < 24 by decide),prefix_9]
  change nodeCompress _ _ = _
  trans nodeCompress (![2161,2178,2195,2212,2229,2246,2263,2280] : Fin 8 → Scalar) ![785640667,939877614,365887579,1554146132,884924304,1762346545,308452542,617980080]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_15
#print axioms prefix_10
theorem prefix_11 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 11 = (![620824211,300099494,1668011682,374649414,1359169338,1742041081,1575185854,1782871725] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 10 < 24 by decide),prefix_10]
  change nodeCompress _ _ = _
  trans nodeCompress (![2181,2198,2215,2232,2249,2266,2283,2300] : Fin 8 → Scalar) ![1563279367,1990384079,1317503545,1053962530,1761249440,14780773,549276084,1614233662]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_16
#print axioms prefix_11
theorem prefix_12 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 12 = (![1843107484,377090426,1232835735,1598963180,1994057985,1261374148,1230772006,1621463387] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 11 < 24 by decide),prefix_11]
  change nodeCompress _ _ = _
  trans nodeCompress (![620824211,300099494,1668011682,374649414,1359169338,1742041081,1575185854,1782871725] : Fin 8 → Scalar) ![2201,2218,2235,2252,2269,2286,2303,2320]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_17
#print axioms prefix_12
theorem prefix_13 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 13 = (![784754526,653487580,1331396859,1248357024,70404971,1215624494,880337038,1016952666] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 12 < 24 by decide),prefix_12]
  change nodeCompress _ _ = _
  trans nodeCompress (![1843107484,377090426,1232835735,1598963180,1994057985,1261374148,1230772006,1621463387] : Fin 8 → Scalar) ![2221,2238,2255,2272,2289,2306,2323,2340]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_18
#print axioms prefix_13
theorem prefix_14 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 14 = (![1675309617,1189999060,110604265,1111112896,1601727123,1630516452,660958964,1526316434] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 13 < 24 by decide),prefix_13]
  change nodeCompress _ _ = _
  trans nodeCompress (![784754526,653487580,1331396859,1248357024,70404971,1215624494,880337038,1016952666] : Fin 8 → Scalar) ![2241,2258,2275,2292,2309,2326,2343,2360]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_19
#print axioms prefix_14
theorem prefix_15 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 15 = (![493855764,1737005017,1044011334,780794261,292608247,1805935865,972083531,346637554] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 14 < 24 by decide),prefix_14]
  change nodeCompress _ _ = _
  trans nodeCompress (![1675309617,1189999060,110604265,1111112896,1601727123,1630516452,660958964,1526316434] : Fin 8 → Scalar) ![2261,2278,2295,2312,2329,2346,2363,2380]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_20
#print axioms prefix_15
theorem prefix_16 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 16 = (![516145591,463254876,1878652377,174797573,1017414220,839141147,732445005,1267400728] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 15 < 24 by decide),prefix_15]
  change nodeCompress _ _ = _
  trans nodeCompress (![2281,2298,2315,2332,2349,2366,2383,2400] : Fin 8 → Scalar) ![493855764,1737005017,1044011334,780794261,292608247,1805935865,972083531,346637554]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_21
#print axioms prefix_16
theorem prefix_17 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 17 = (![1275343547,688077093,1851184479,402597576,2135776699,632730450,2036489921,1092402184] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 16 < 24 by decide),prefix_16]
  change nodeCompress _ _ = _
  trans nodeCompress (![516145591,463254876,1878652377,174797573,1017414220,839141147,732445005,1267400728] : Fin 8 → Scalar) ![2301,2318,2335,2352,2369,2386,2403,2420]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_22
#print axioms prefix_17
theorem prefix_18 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 18 = (![2136837586,679543585,225002526,1101048270,2134488188,1020968422,1342497638,1907691591] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 17 < 24 by decide),prefix_17]
  change nodeCompress _ _ = _
  trans nodeCompress (![2321,2338,2355,2372,2389,2406,2423,2440] : Fin 8 → Scalar) ![1275343547,688077093,1851184479,402597576,2135776699,632730450,2036489921,1092402184]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_23
#print axioms prefix_18
theorem prefix_19 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 19 = (![2081739590,582598927,447833412,1551242300,10472096,1276966930,111682118,132339882] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 18 < 24 by decide),prefix_18]
  change nodeCompress _ _ = _
  trans nodeCompress (![2136837586,679543585,225002526,1101048270,2134488188,1020968422,1342497638,1907691591] : Fin 8 → Scalar) ![2341,2358,2375,2392,2409,2426,2443,2460]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_24
#print axioms prefix_19
theorem prefix_20 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 20 = (![1272212618,615811090,570892109,1073257360,1217412274,1723220283,85709078,537745032] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 19 < 24 by decide),prefix_19]
  change nodeCompress _ _ = _
  trans nodeCompress (![2361,2378,2395,2412,2429,2446,2463,2480] : Fin 8 → Scalar) ![2081739590,582598927,447833412,1551242300,10472096,1276966930,111682118,132339882]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_25
#print axioms prefix_20
theorem prefix_21 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 21 = (![9991919,1366070145,2057247444,1742688934,729806222,499041299,1681224112,1485431753] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 20 < 24 by decide),prefix_20]
  change nodeCompress _ _ = _
  trans nodeCompress (![1272212618,615811090,570892109,1073257360,1217412274,1723220283,85709078,537745032] : Fin 8 → Scalar) ![2381,2398,2415,2432,2449,2466,2483,2500]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_26
#print axioms prefix_21
theorem prefix_22 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 22 = (![1542818520,1882037664,1251951877,1554108809,81746851,159927545,2111428769,132405182] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 21 < 24 by decide),prefix_21]
  change nodeCompress _ _ = _
  trans nodeCompress (![3001,3018,3035,3052,3069,3086,3103,3120] : Fin 8 → Scalar) ![9991919,1366070145,2057247444,1742688934,729806222,499041299,1681224112,1485431753]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_27
#print axioms prefix_22
theorem prefix_23 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 23 = (![407525056,1458948676,1930040251,1044760048,961029422,441494278,1982425121,1368876468] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 22 < 24 by decide),prefix_22]
  change nodeCompress _ _ = _
  trans nodeCompress (![1542818520,1882037664,1251951877,1554108809,81746851,159927545,2111428769,132405182] : Fin 8 → Scalar) ![3101,3118,3135,3152,3169,3186,3203,3220]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_28
#print axioms prefix_23
theorem prefix_24 : merkleRootAux leaf PV_RunJoin_FixtureRecords.path 24 = (![71235157,561336479,2021715933,831357912,593948515,110335229,1732475008,949858646] : Fin 8 → Scalar) := by
  rw [merkleRootAux,dif_pos (show 23 < 24 by decide),prefix_23]
  change nodeCompress _ _ = _
  trans nodeCompress (![3201,3218,3235,3252,3269,3286,3303,3320] : Fin 8 → Scalar) ![407525056,1458948676,1930040251,1044760048,961029422,441494278,1982425121,1368876468]
  · apply congrArg₂ nodeCompress <;> funext i <;> fin_cases i <;> rfl
  · exact node_29
#print axioms prefix_24
end R1Z.PV_RunJoin_PathValues16
