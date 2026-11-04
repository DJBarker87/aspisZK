import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node05
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![1202730148,379935560,1636959529,914430904,1136987334,1121513481,1449673835,22736703,1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,803983598]
def s1 : Fin 16 → M := ![518619095,1336299183,1377853587,1629347167,1532887335,1300160928,1151518350,203022550,478562836,1550342352,713971783,568842898,1791993869,62361656,6275177,688041220]
def s2 : Fin 16 → M := ![1848865457,1998007275,10045801,729510825,1913558861,841206935,410963348,1190564733,701386639,1774784348,2145404150,312406622,228362107,481796118,747123962,326045208]
def s3 : Fin 16 → M := ![130641221,974766937,864504528,440098266,27762768,1295086210,1526987742,287147715,952246673,1852661821,2055354286,1872463656,2109604775,372908772,1013515289,1111268980]
def s4 : Fin 16 → M := ![69933239,1528651766,1517373365,848877400,188931781,893999938,276793037,701022604,587407601,1560728374,86002868,1529792854,668205642,1962200689,1182259893,1202028035]
def s5 : Fin 16 → M := ![712764888,1414906546,529765623,940236731,1722951859,264250046,139835208,1147583742,1527104610,1609358503,494735929,208243967,819660656,1406891038,1618156535,336992585]
def s6 : Fin 16 → M := ![1712160552,146805739,1938914086,345362470,1778095830,812416282,1059142202,1310298330,927761043,558299384,682833444,1295663813,358112623,292682534,1113993643,1303607652]
def s7 : Fin 16 → M := ![1141220612,1083759513,519814652,170920007,129334885,1050712404,469765886,1044184661,1578766693,2127675376,78731508,1543840085,1132899588,916607079,1353615892,826106645]
def s8 : Fin 16 → M := ![648820395,571121455,526991246,171041970,522041022,1266374877,1634968412,1890670836,1853519475,858895507,651531195,864493334,923948151,1972084454,645665860,1149707792]
def s9 : Fin 16 → M := ![235788001,1276673568,1759534605,1389719993,586912995,1640197322,1484933769,1449401385,1732843743,1539469911,6081576,469714274,1956433077,298293687,875562349,1344169983]
def s10 : Fin 16 → M := ![29422657,359913386,454825381,347152496,1631060131,1704076853,1503963839,1650615284,1843906928,198029633,1015806348,1035042057,1660032688,801710701,1276251577,828045766]
def s11 : Fin 16 → M := ![69583352,698941465,1248678841,1727638063,502607245,1834453963,1221230693,751707552,135913693,1642490246,1142643283,738574373,1460355371,1557168211,454161537,234588965]
def s12 : Fin 16 → M := ![1389247817,2094713239,1745645809,1863873085,1121662440,682264124,1820448304,112931221,1612855302,966479938,1083905951,791944959,995573569,1934014438,1299342480,1582753141]
def s13 : Fin 16 → M := ![2043357689,813465904,62560636,1879277711,1249601244,1045044061,1138523571,1651383515,1153284856,1324481035,536884637,1972481406,462022254,1637577019,1709835530,420967494]
def s14 : Fin 16 → M := ![1767953339,948039606,259694974,1209233605,1541449066,1822893149,60105975,596419959,1726147274,2046786083,148628358,584932664,1154692456,1683251027,176870512,2085331124]
def s15 : Fin 16 → M := ![425702356,399034209,2117868198,2140445376,1045168896,699997576,1374385803,1114649980,1354513681,1589705630,1322577905,890919942,1173612767,1998309844,1233052213,2147209281]
def s16 : Fin 16 → M := ![1723458515,1223772650,765507543,796585357,596155021,1287281422,1855411197,1295376810,256314202,1914970438,82331904,1458104620,776238086,597540375,574835720,23757441]
def s17 : Fin 16 → M := ![724481021,1737853437,2045095873,1552938568,988353661,1783230716,1905180622,1813818041,1110043938,1120241399,1070088250,758582000,757402532,237638114,1151885910,556090088]
def s18 : Fin 16 → M := ![1819328850,588188886,793043548,767122427,314713796,1612223141,1834056884,1118056782,1349522458,16808542,1551527126,740853887,1559105057,1072826861,1822738304,2120336674]
def s19 : Fin 16 → M := ![2100262961,797919966,1795818176,1130737141,579957801,235497572,917492899,898404777,1149913944,217750538,1983092971,352859021,1313109315,251371009,1883286188,1369651915]
def s20 : Fin 16 → M := ![934763809,1532826805,1109328076,1027949310,2113515428,1473134759,1835243203,1821501197,533808386,534243074,541981158,755856307,732015164,749497382,1252221552,108804249]
def s21 : Fin 16 → M := ![1841760212,324115578,1466019626,330550045,1409359483,1434520167,738320934,1275667314,1411602781,1685967083,1033907685,1580075178,1310188652,477229750,8902928,1641693098]
def s22 : Fin 16 → M := ![404729214,1743863086,1381499695,1088584035,559883904,1266000294,672574314,1962357737,1927704072,1723938403,2137152870,1598066674,252462607,690060617,1110044097,818684180]
def s23 : Fin 16 → M := ![708564806,100495163,988693857,52379155,474573668,874069195,2050287843,1592187062,109527705,1990034002,1474175273,4347769,1526845626,1978631460,1865630594,1137662453]
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
def left : Fin 8 → M := ![1202730148,379935560,1636959529,914430904,1136987334,1121513481,1449673835,22736703]
def right : Fin 8 → M := ![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616]
def output : Fin 8 → M := ![708564806,100495163,988693857,52379155,474573668,874069195,2050287843,1592187062]
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
end AspisR1.PV_2TNV_Node05
