import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_13_0 : Fin 16 → Scalar := ![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184,2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,1001875166]
def s_13_1 : Fin 16 → Scalar := ![1958005276,866286399,806017692,1452269400,1175089853,1678825548,1727708014,1613380171,1958005276,866286399,806017692,1452269400,123568835,627304530,720628607,1657821782]
theorem round_13_1 : poseidonExternalLinear s_13_0 = s_13_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_1
def s_13_2 : Fin 16 → Scalar := ![1091607090,623519046,409302687,505698088,1504733996,179293503,423610525,1149338559,707467912,1758038553,1246452373,1437888189,1194336955,394035147,1864528364,1765656518]
theorem round_13_2 : poseidonFullRound s_13_1 (poseidonExternalInitial 0) = s_13_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_2
def s_13_3 : Fin 16 → Scalar := ![1990413254,452403353,1374970420,1113900599,1639489039,1034845966,106111072,1454992363,1845127400,1431163648,1056825873,2109554497,1219558769,1163379294,1854213063,1424529700]
theorem round_13_3 : poseidonFullRound s_13_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_13_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_3
def s_13_4 : Fin 16 → Scalar := ![244368237,1934658060,1173596256,1122572033,50975222,985000097,1100540681,793097247,1196014460,1364347047,1341283596,988856592,1939188060,1187591206,255653387,1608567865]
theorem round_13_4 : poseidonFullRound s_13_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_13_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_4
def s_13_5 : Fin 16 → Scalar := ![1283705792,1124911174,495199619,296360263,2122745919,651842219,673024045,811482571,1098378444,297934342,1214478717,710095162,371134801,1489178914,992452539,2140231175]
theorem round_13_5 : poseidonFullRound s_13_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_13_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_5
def s_13_6 : Fin 16 → Scalar := ![365317186,1821206385,1686694449,1881736263,498393387,388352480,758228181,1091572227,1702298988,1805559118,929469806,1553220725,195740851,1841908620,2036226642,2139659853]
theorem round_13_6 : poseidonInternalRound s_13_5 (poseidonInternalConstants 0) = s_13_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_6
def s_13_7 : Fin 16 → Scalar := ![235163399,1444389643,849088509,707677369,1462846707,1541855644,264164933,764329082,621605375,137333361,65008981,768710444,1109433988,1013805694,380876024,131611307]
theorem round_13_7 : poseidonInternalRound s_13_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_13_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_7
def s_13_8 : Fin 16 → Scalar := ![1542528717,952498578,1206285953,191334764,473464356,555479122,1518935850,1180529949,1764185643,305710999,1652796069,2082544704,1988028174,1062073533,1026190650,492398135]
theorem round_13_8 : poseidonInternalRound s_13_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_13_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_8
def s_13_9 : Fin 16 → Scalar := ![931757858,713398973,25988654,526239451,1401131596,58631759,1122207361,152889486,90879764,713504847,6961215,58962095,1319206602,1861157073,677174869,1475795933]
theorem round_13_9 : poseidonInternalRound s_13_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_13_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_9
def s_13_10 : Fin 16 → Scalar := ![2004096213,1937692940,1276271275,1181768124,1695928500,14918464,627707520,271802836,2119485524,1345424804,1910127186,67382976,2027065847,153990599,941876908,618065469]
theorem round_13_10 : poseidonInternalRound s_13_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_13_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_10
def s_13_11 : Fin 16 → Scalar := ![30597485,2073858694,541224657,568270956,818691872,374861178,895453571,351678082,847373304,967532058,1896285448,1258928634,1516025774,1972338192,2071196061,1985676071]
theorem round_13_11 : poseidonInternalRound s_13_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_13_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_11
def s_13_12 : Fin 16 → Scalar := ![303083592,1542342207,550932827,1741567337,1723051195,1171295067,205710374,501044291,558084075,196070956,2087049024,2079415577,2001177167,1070984832,1495314220,1668915310]
theorem round_13_12 : poseidonInternalRound s_13_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_13_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_12
def s_13_13 : Fin 16 → Scalar := ![357354950,1863674176,1423197623,845150376,1220839647,1882183865,461612996,175911888,889133218,1123372824,713303780,687391359,74522835,247939820,1790802977,865462772]
theorem round_13_13 : poseidonInternalRound s_13_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_13_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_13
def s_13_14 : Fin 16 → Scalar := ![333196258,2142190819,977428242,1511634500,1455299231,328687425,17746986,799459240,270935256,99150889,557147383,482461890,884225215,1632951046,1319812704,2056141518]
theorem round_13_14 : poseidonInternalRound s_13_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_13_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_14
def s_13_15 : Fin 16 → Scalar := ![1528046759,1767401337,1580067002,1376781224,530186131,589242024,193114070,1398477997,2092668581,1385517985,1060964255,104156718,1883314114,543873856,1222211904,611852210]
theorem round_13_15 : poseidonInternalRound s_13_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_13_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_15
def s_13_16 : Fin 16 → Scalar := ![127163405,2107642043,1352891063,1552398308,286762460,1178178502,77440005,1796002987,1913846846,698043111,140912444,1764395528,926942546,1259846007,1357378075,872018482]
theorem round_13_16 : poseidonInternalRound s_13_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_13_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_16
def s_13_17 : Fin 16 → Scalar := ![2102377121,214923384,813063467,21907279,401381021,1925751844,585361501,1382322865,414025518,712658703,667703295,936375521,265926028,2106412359,138229924,23187376]
theorem round_13_17 : poseidonInternalRound s_13_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_13_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_17
def s_13_18 : Fin 16 → Scalar := ![1021511730,1084519001,348238904,957224733,1933160138,1616854063,273810826,1291429450,177770746,774113590,1697969951,857936091,1787198935,119994536,1344733726,59047077]
theorem round_13_18 : poseidonInternalRound s_13_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_13_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_18
def s_13_19 : Fin 16 → Scalar := ![2142308817,1820409954,1432368761,269822591,1168786528,835752197,907902797,1782997167,2015709971,1340474469,2142850354,1558873197,2073544874,1778831772,753671728,679597331]
theorem round_13_19 : poseidonInternalRound s_13_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_13_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_19
def s_13_20 : Fin 16 → Scalar := ![990322354,103363234,839016442,1243051412,2015381683,840212747,275388143,1910212409,1365189401,951977237,444207711,1223578973,205160840,1834463964,632533352,228853894]
theorem round_13_20 : poseidonFullRound s_13_19 (poseidonExternalFinal 0) = s_13_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_20
def s_13_21 : Fin 16 → Scalar := ![892158936,97854807,2035240530,434635898,1456856018,1296397224,1442750874,666068526,456558916,990072842,1826717852,1260067854,1113670550,1445991653,157459510,985412544]
theorem round_13_21 : poseidonFullRound s_13_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_13_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_21
def s_13_22 : Fin 16 → Scalar := ![908876591,1951154975,575851959,2057990698,1630655387,568747715,1120442092,558409250,668082036,2118717429,1254025679,779484984,1484410835,161458182,205644240,268441323]
theorem round_13_22 : poseidonFullRound s_13_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_13_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_22
def s_13_23 : Fin 16 → Scalar := ![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542,126244620,707951397,845782733,167939532,115390596,1321881680,945634777,787827070]
theorem round_13_23 : poseidonFullRound s_13_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_13_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_13_23
theorem permutation_13 : poseidonPermutation s_13_0 = s_13_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_13_1,round_13_2,round_13_3,round_13_4,round_13_5,round_13_6,round_13_7,round_13_8,round_13_9,round_13_10,round_13_11,round_13_12,round_13_13,round_13_14,round_13_15,round_13_16,round_13_17,round_13_18,round_13_19,round_13_20,round_13_21,round_13_22,round_13_23]
#print axioms permutation_13
theorem parent_13 : nodeCompress (![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] : Fin 8 → Scalar) ![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] = ![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_13_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_13]
  funext i
  fin_cases i <;> rfl
#print axioms parent_13
end R1Z.PV_RunJoin_RootModel
