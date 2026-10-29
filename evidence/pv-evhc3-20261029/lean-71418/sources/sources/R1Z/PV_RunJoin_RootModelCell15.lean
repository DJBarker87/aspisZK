import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_15_0 : Fin 16 → Scalar := ![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983,1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,628703965]
def s_15_1 : Fin 16 → Scalar := ![131944609,144717421,1314078057,750189496,673379757,1433574022,364653237,1748630333,131944609,144717421,1314078057,750189496,1769342386,382053004,1505057477,1793071944]
theorem round_15_1 : poseidonExternalLinear s_15_0 = s_15_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_1
def s_15_2 : Fin 16 → Scalar := ![940852786,174316211,1814819195,357500364,279878174,38947105,1297821572,1068096455,1322501321,1084596481,1027143950,1747129717,1930772653,341652320,1513631726,1338100074]
theorem round_15_2 : poseidonFullRound s_15_1 (poseidonExternalInitial 0) = s_15_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_2
def s_15_3 : Fin 16 → Scalar := ![145875834,2086388771,8242957,478393556,1782022546,1925094593,1326660815,939906696,598232855,922917339,1498047738,1183496504,433572304,634038200,1147385802,1202860004]
theorem round_15_3 : poseidonFullRound s_15_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_15_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_3
def s_15_4 : Fin 16 → Scalar := ![1903467932,312155985,630475096,195530966,1170620964,1629061650,1319243600,1028922952,208631600,155472620,1550888910,644336169,1715582948,938154922,1582311849,1454546613]
theorem round_15_4 : poseidonFullRound s_15_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_15_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_4
def s_15_5 : Fin 16 → Scalar := ![357268985,1222951563,1173186011,1148677105,1862118316,258773318,605761925,258700053,105508300,1005470949,1030548667,643878309,902159768,1596820971,1368117303,586828473]
theorem round_15_5 : poseidonFullRound s_15_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_15_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_5
def s_15_6 : Fin 16 → Scalar := ![1494497723,1497652138,473588950,574441701,139261574,120106369,331729352,1799118438,894861093,2124709526,1142064906,490335723,1276290704,1943701685,2021354154,1528356627]
theorem round_15_6 : poseidonInternalRound s_15_5 (poseidonInternalConstants 0) = s_15_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_6
def s_15_7 : Fin 16 → Scalar := ![1245953934,754589379,204115141,1554704045,371029833,1178639145,1282341917,583883982,2130007501,2016696853,500297017,1922332351,679990813,1977826565,151731092,852064586]
theorem round_15_7 : poseidonInternalRound s_15_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_15_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_7
def s_15_8 : Fin 16 → Scalar := ![752715565,110119549,1911244099,1279379056,176285187,1033887314,1735765868,216883019,1413550776,233849258,558567592,553789964,1415173595,685221547,2002793668,1390448972]
theorem round_15_8 : poseidonInternalRound s_15_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_15_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_8
def s_15_9 : Fin 16 → Scalar := ![433257369,1193493697,610895052,1905923078,346171997,445701996,793307102,2078985482,1629247128,819242080,1825938254,1664335460,2068737882,708693680,1526034852,1373609989]
theorem round_15_9 : poseidonInternalRound s_15_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_15_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_9
def s_15_10 : Fin 16 → Scalar := ![1352355887,1314551269,1342847676,1302298943,742949901,809838567,1884564719,32142306,358776197,1541116293,1571056778,1126006154,1428328439,2061715010,1074367513,658298083]
theorem round_15_10 : poseidonInternalRound s_15_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_15_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_10
def s_15_11 : Fin 16 → Scalar := ![969135174,483393439,1854537522,83070648,817474084,1388841007,1492854709,1225949754,2142522446,705105777,1613214886,642658845,544505602,537282347,344082883,593025075]
theorem round_15_11 : poseidonInternalRound s_15_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_15_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_11
def s_15_12 : Fin 16 → Scalar := ![1398163833,104980243,1183178201,2101353043,1866412182,368206446,148297258,772959768,1134036723,1887523015,138705525,1284748349,2035427216,2067574646,240350198,1101342245]
theorem round_15_12 : poseidonInternalRound s_15_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_15_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_12
def s_15_13 : Fin 16 → Scalar := ![849990550,2060408751,26817616,1770906092,1854340435,1404280703,258489823,2032729779,1083241056,1977499773,108481759,802247215,964663025,543897147,780699376,447937511]
theorem round_15_13 : poseidonInternalRound s_15_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_15_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_13
def s_15_14 : Fin 16 → Scalar := ![605281859,1476152309,1616862437,56916985,1365565156,409398336,1244966953,661430594,631645318,997028401,979398777,1917839935,1342907045,716948603,547693262,1494493611]
theorem round_15_14 : poseidonInternalRound s_15_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_15_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_14
def s_15_15 : Fin 16 → Scalar := ![1475693235,854183460,464272378,1753182738,1712617811,1633437233,562268001,907399874,771736916,1214231461,1554999297,1502707832,1061303857,1275877260,1817486035,77149271]
theorem round_15_15 : poseidonInternalRound s_15_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_15_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_15
def s_15_16 : Fin 16 → Scalar := ![1917227679,1050407924,1124769220,766504475,1012265070,561416428,1008931320,287757931,194301950,1801833312,1230122165,599372034,1383617952,563432406,1562120740,1074343682]
theorem round_15_16 : poseidonInternalRound s_15_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_15_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_16
def s_15_17 : Fin 16 → Scalar := ![338604584,1236909147,288556016,1105035476,1842170842,579229483,260048758,1423139631,1434830706,1894328637,1406181041,640543966,366075141,1578326321,338699651,975194233]
theorem round_15_17 : poseidonInternalRound s_15_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_15_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_17
def s_15_18 : Fin 16 → Scalar := ![439377997,1471298190,811501075,359563653,2086853897,912126183,2113498358,1121012253,1356609416,1998699540,1349731537,1824940792,1234772903,1682238780,549065315,1450308211]
theorem round_15_18 : poseidonInternalRound s_15_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_15_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_18
def s_15_19 : Fin 16 → Scalar := ![1056414987,257134116,408838076,224090538,448281573,494952972,1993273972,1811143414,633149414,1499293827,78944793,500228398,1544963579,1928365495,1087566927,706019449]
theorem round_15_19 : poseidonInternalRound s_15_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_15_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_19
def s_15_20 : Fin 16 → Scalar := ![222679257,940749895,578891397,1292857479,1728432207,606144375,1147708738,1418972602,778706816,808353285,1261028362,240203075,143305486,1199154239,1961184549,804438402]
theorem round_15_20 : poseidonFullRound s_15_19 (poseidonExternalFinal 0) = s_15_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_20
def s_15_21 : Fin 16 → Scalar := ![496829764,1885895562,1440965488,1375186404,611893893,828236218,717499537,516890978,1135297580,377994898,651596424,424865854,1966052276,1848583580,1182904605,1267902662]
theorem round_15_21 : poseidonFullRound s_15_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_15_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_21
def s_15_22 : Fin 16 → Scalar := ![751269463,783224816,2103330775,524448089,1862814382,1481287637,80700568,535108654,1319611964,511047077,36562075,204567212,1877945534,1115950550,955687446,1725123868]
theorem round_15_22 : poseidonFullRound s_15_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_15_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_22
def s_15_23 : Fin 16 → Scalar := ![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477,1083194641,1301976153,161405951,718614618,1083699140,1391935707,1944496679,1074534982]
theorem round_15_23 : poseidonFullRound s_15_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_15_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_15_23
theorem permutation_15 : poseidonPermutation s_15_0 = s_15_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_15_1,round_15_2,round_15_3,round_15_4,round_15_5,round_15_6,round_15_7,round_15_8,round_15_9,round_15_10,round_15_11,round_15_12,round_15_13,round_15_14,round_15_15,round_15_16,round_15_17,round_15_18,round_15_19,round_15_20,round_15_21,round_15_22,round_15_23]
#print axioms permutation_15
theorem parent_15 : nodeCompress (![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] : Fin 8 → Scalar) ![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] = ![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_15_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_15]
  funext i
  fin_cases i <;> rfl
#print axioms parent_15
end R1Z.PV_RunJoin_RootModel
