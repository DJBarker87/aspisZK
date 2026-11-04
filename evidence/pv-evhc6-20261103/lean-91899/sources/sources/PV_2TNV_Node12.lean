import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node12
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![932605221,382022248,683061747,928614086,159839169,394479800,1976348339,777778117,986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,228521044]
def s1 : Fin 16 → M := ![523610354,797999289,1633777072,809247201,157901529,1631688501,860050202,1642504898,1320567775,1921087338,1200262012,628694527,1123527134,2036779861,764150086,282437640]
def s2 : Fin 16 → M := ![1917931658,1583887539,2120610359,733341184,210716498,17144910,1031091803,1489501197,141828570,1622881387,233620927,1958648983,945270331,411910745,598321141,564636848]
def s3 : Fin 16 → M := ![1004204218,1804796397,866586988,1977982918,1430102189,546530020,1189095513,2105197573,396085243,319200517,2051370,1467832570,1081462254,1733571063,571590628,21323608]
def s4 : Fin 16 → M := ![1662915887,1974482091,837727918,302818490,284597668,535091374,795547436,1086817296,576016128,936951392,522144546,1538963180,1934690172,2009376240,35709222,1070394395]
def s5 : Fin 16 → M := ![2140573866,513631094,1813090685,979618976,322828214,1036598023,100304235,380701770,565827954,456987182,1080649525,601614044,524247980,1833518394,1855773079,202728899]
def s6 : Fin 16 → M := ![1036257856,391293229,1356359858,1648654392,312804200,1430844974,939914008,620255298,1436679896,902263789,508697530,925043250,1697303942,1241775195,1702966355,1584946657]
def s7 : Fin 16 → M := ![199484614,1379159056,1553101896,1140032454,1342815780,259065294,1000343025,2029499253,199298873,39161935,55610326,1803864519,345144366,972589029,1426819172,415457236]
def s8 : Fin 16 → M := ![1594776506,1938503214,1518064303,824506680,564452163,409421568,358066253,1598277530,299796138,1994864930,1669743160,1844668302,1893510978,1129334554,1703493417,19602341]
def s9 : Fin 16 → M := ![20315814,943576463,2041201855,155616322,1373206906,1260851043,1873258757,363103760,871756914,736870990,1572569724,2066451742,1520106391,1450787080,1682408681,1616355766]
def s10 : Fin 16 → M := ![398325117,946790488,1938134088,625679313,251451038,849477890,1965435780,1767018195,2066433020,1811110176,1849359798,956496430,1604583791,1349727749,1118170896,568839032]
def s11 : Fin 16 → M := ![94125712,1535374498,169884892,943817615,452708667,1295328368,1205503207,2008598846,951521989,376321314,252440508,1387789162,591596595,1888910467,446519024,1854756889]
def s12 : Fin 16 → M := ![1722046462,470701060,1422579993,563113375,409512251,333227627,1004207187,784117533,471056922,784302478,1883852761,1078004152,571525170,1605064620,1812101630,413416572]
def s13 : Fin 16 → M := ![2100408145,1961539460,41031092,1595808253,471969114,380029491,1413213679,134752984,1656582300,408809950,2115750658,1769466760,1910680580,784831318,366727043,358126793]
def s14 : Fin 16 → M := ![99194513,388729192,656735563,515455450,55458997,212694294,700354520,608929767,16326726,3321876,292347348,553213714,2009165403,118909255,167929791,923401364]
def s15 : Fin 16 → M := ![313161588,1636612242,413870529,1162221203,1691555026,356024460,36907573,1564682492,1190220331,2098283306,2111340469,1616008009,2016193818,1689449141,2118170924,1190501694]
def s16 : Fin 16 → M := ![1562210492,1056294891,247423707,1921083814,67220975,821106715,600724985,775114375,1444029727,1856780882,1063774023,43887459,1930194275,437682610,973049241,2057805123]
def s17 : Fin 16 → M := ![1538670088,45199349,1631235519,230788773,1674155905,1389193663,1032234802,1351584224,1288599519,1878407910,1666778628,510793821,1365796044,1680373012,176726537,1627381080]
def s18 : Fin 16 → M := ![2015634287,915807929,1985595971,1793763672,1378953938,1622870718,1689867539,1472653036,455106193,706696612,402424287,1433027218,1082000158,1361682648,82377037,289222852]
def s19 : Fin 16 → M := ![1642333822,405319018,1313219384,222114836,1931208005,1833122460,2025664809,1397508572,1908528971,15217413,1402604400,96188766,569794256,1237890885,1580798873,307671339]
def s20 : Fin 16 → M := ![1026800305,902710842,537413122,1934359086,704765453,108041030,784761045,2041925320,1700771449,1504873559,112025428,539302505,764870756,1906230105,1273703503,286866816]
def s21 : Fin 16 → M := ![1975399447,1345779744,851003006,496184852,1527243509,906723802,2049438785,689433977,15698628,1080137650,1412396671,691246287,168460051,955139752,1664518399,1719110886]
def s22 : Fin 16 → M := ![764480343,736222498,642411712,428297636,1869130844,1521148766,128540345,1506118569,1157176893,18459156,1840870500,384748413,1324203807,638783519,1680645465,36701256]
def s23 : Fin 16 → M := ![709969142,47554429,1690110982,171189941,234684882,1407902945,1942746655,1390452334,1782721163,570764354,1129273624,764308541,1434013431,2065019928,1573017828,1487282382]
theorem r1 : poseidonExternalLinear s0 = s1 := by
  funext i
  fin_cases i <;> rfl
#print axioms r1
theorem r2 : poseidonFullRound s1 (poseidonExternalInitial 0) = s2 := by
  funext i
  fin_cases i <;> rfl
#print axioms r2
theorem r3 : poseidonFullRound s2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s3 := by
  funext i
  fin_cases i <;> rfl
#print axioms r3
theorem r4 : poseidonFullRound s3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s4 := by
  funext i
  fin_cases i <;> rfl
#print axioms r4
theorem r5 : poseidonFullRound s4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s5 := by
  funext i
  fin_cases i <;> rfl
#print axioms r5
theorem r6 : poseidonInternalRound s5 (poseidonInternalConstants 0) = s6 := by
  funext i
  fin_cases i <;> rfl
#print axioms r6
theorem r7 : poseidonInternalRound s6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s7 := by
  funext i
  fin_cases i <;> rfl
#print axioms r7
theorem r8 : poseidonInternalRound s7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s8 := by
  funext i
  fin_cases i <;> rfl
#print axioms r8
theorem r9 : poseidonInternalRound s8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s9 := by
  funext i
  fin_cases i <;> rfl
#print axioms r9
theorem r10 : poseidonInternalRound s9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s10 := by
  funext i
  fin_cases i <;> rfl
#print axioms r10
theorem r11 : poseidonInternalRound s10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s11 := by
  funext i
  fin_cases i <;> rfl
#print axioms r11
theorem r12 : poseidonInternalRound s11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s12 := by
  funext i
  fin_cases i <;> rfl
#print axioms r12
theorem r13 : poseidonInternalRound s12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s13 := by
  funext i
  fin_cases i <;> rfl
#print axioms r13
theorem r14 : poseidonInternalRound s13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s14 := by
  funext i
  fin_cases i <;> rfl
#print axioms r14
theorem r15 : poseidonInternalRound s14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s15 := by
  funext i
  fin_cases i <;> rfl
#print axioms r15
theorem r16 : poseidonInternalRound s15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s16 := by
  funext i
  fin_cases i <;> rfl
#print axioms r16
theorem r17 : poseidonInternalRound s16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s17 := by
  funext i
  fin_cases i <;> rfl
#print axioms r17
theorem r18 : poseidonInternalRound s17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s18 := by
  funext i
  fin_cases i <;> rfl
#print axioms r18
theorem r19 : poseidonInternalRound s18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s19 := by
  funext i
  fin_cases i <;> rfl
#print axioms r19
theorem r20 : poseidonFullRound s19 (poseidonExternalFinal 0) = s20 := by
  funext i
  fin_cases i <;> rfl
#print axioms r20
theorem r21 : poseidonFullRound s20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s21 := by
  funext i
  fin_cases i <;> rfl
#print axioms r21
theorem r22 : poseidonFullRound s21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s22 := by
  funext i
  fin_cases i <;> rfl
#print axioms r22
theorem r23 : poseidonFullRound s22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s23 := by
  funext i
  fin_cases i <;> rfl
#print axioms r23
theorem permutation : poseidonPermutation s0 = s23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23]
#print axioms permutation
def left : Fin 8 → M := ![932605221,382022248,683061747,928614086,159839169,394479800,1976348339,777778117]
def right : Fin 8 → M := ![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062]
def output : Fin 8 → M := ![709969142,47554429,1690110982,171189941,234684882,1407902945,1942746655,1390452334]
theorem source : nodeCompress left right = output := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then left ⟨l.val,h⟩
    else if l.val = 15 then right 7 - (1051521018 : M)
    else right ⟨l.val-8,by omega⟩) = s0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation]
  funext i
  fin_cases i <;> rfl
#print axioms source
end AspisR1.PV_2TNV_Node12
