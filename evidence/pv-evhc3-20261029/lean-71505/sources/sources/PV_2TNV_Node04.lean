import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node04
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![1603344092,1242405009,1153352827,393697509,714169239,2094351560,55834509,664305674,1032062983,1528648228,154569178,2087313457,1156495396,824542697,187424622,1505167535]
def s1 : Fin 16 → M := ![2109899114,919649676,1371126578,1546275241,2060478908,859904783,2098169782,1321878892,373415205,1765603653,2021885587,359639733,108156607,2145729061,1908969238,1044878688]
def s2 : Fin 16 → M := ![1742655976,408455343,708866268,1739301192,880253507,1397946866,1665341855,527968047,1982641133,451264697,477415441,2080872029,199320626,869492078,1054888890,448193938]
def s3 : Fin 16 → M := ![440608717,1494837301,1561351045,63370477,404234958,1004927886,1919055266,1820804952,1711323527,645196431,578532720,187086887,1027617292,1622357190,776989616,564960705]
def s4 : Fin 16 → M := ![842505488,894986065,406044837,422305997,729792750,158892321,1302624394,2063580888,1374345207,1976912714,320952541,268420877,1867682606,1376792936,1214660975,1700626885]
def s5 : Fin 16 → M := ![105970477,386085360,462048644,1542610633,529705978,562903866,1606047656,1906464715,725646724,1537535927,117149024,872466698,1940613699,981167688,1042042857,742359469]
def s6 : Fin 16 → M := ![1013100188,1365395637,1903407565,707301868,921990807,1395837545,833227741,586484158,1520294128,1599000188,680826621,1190116677,665293744,368129027,1649661153,1007447876]
def s7 : Fin 16 → M := ![1529840120,412130282,706066128,1875942117,2127693807,2052782542,2087702240,74498758,370854799,368889843,428492921,1124248594,967073054,338632237,832517512,913492813]
def s8 : Fin 16 → M := ![994340171,862537994,1862539968,1511725239,292088992,1082673679,684886335,923360930,675181750,396927052,1140494828,1167709568,645692297,1650718519,899473087,1713773061]
def s9 : Fin 16 → M := ![1426963182,390370352,1105428647,1279766020,1864544294,1818225693,2116842255,640873409,51750478,209426261,1310915909,20141017,1934390468,1638480983,1396375746,2111903601]
def s10 : Fin 16 → M := ![1357745305,451756961,124760256,885483395,2092839079,1235710286,1228345712,275095492,242996852,2134901897,261998050,954613655,306269252,1388224581,67764908,454732595]
def s11 : Fin 16 → M := ![18841880,1021580906,819344457,1964273878,132667401,1013835698,1222181083,996066257,1608649943,1643863239,420371270,99633638,1266636633,1242053672,592238291,1294600446]
def s12 : Fin 16 → M := ![712556844,920246628,1537354636,1313310293,960004930,1087651361,353754732,1369880407,1794911961,1968343741,862116802,2123637687,1692464601,150988798,1700750918,49569102]
def s13 : Fin 16 → M := ![668572694,1661908776,1668887773,1699936026,1979250647,964214748,1324395337,367178669,709642927,2126486446,933488479,1852857750,1257248508,640967236,1599619875,159572909]
def s14 : Fin 16 → M := ![27760209,870755133,399138256,1713623167,10466004,1751380443,787307848,1233444703,1996311486,276013842,1618309585,1454465506,1404536528,1768490798,1919538028,881133338]
def s15 : Fin 16 → M := ![2105897069,574949042,502470421,116235636,1935405588,1956477233,1275724928,1335243609,1828993771,1644260757,1143317112,75269707,1597534306,808063017,1477758430,1970848894]
def s16 : Fin 16 → M := ![335854523,216977422,646969222,106970924,92887555,880893050,1810520430,1345757123,1824997192,1813471007,20163453,856586731,2025201961,1857298800,1368990064,791196749]
def s17 : Fin 16 → M := ![681763698,788206032,1865167054,999112306,1314329050,1780615528,525823901,800338602,95151663,963338650,1891251659,162199588,1714520047,711489820,851743579,1448714259]
def s18 : Fin 16 → M := ![406365540,2141072910,788233692,1054348808,1130081043,1925427915,999362534,1034929878,647377860,1006941873,964316100,2448756,10556875,1860841842,441503491,1891027185]
def s19 : Fin 16 → M := ![1392759643,333000086,1915878207,261838761,790124579,1081486405,106757206,2929958,1599398317,418492671,2104103250,1779580811,921984943,546813692,2075957719,1563222260]
def s20 : Fin 16 → M := ![413059757,1059967207,1935932055,482629847,166110758,1254984548,1684137315,1881296607,191600020,653544421,1136610736,1133802263,1258060759,1735726134,1223595993,664141302]
def s21 : Fin 16 → M := ![1320560143,1732345778,12331359,1095671173,2097111995,1838716537,325825924,1001522905,2051677033,1697230188,965673933,1400840888,1825583279,2122899738,1316563326,1958828776]
def s22 : Fin 16 → M := ![1148040655,759340301,1118670149,9496203,1538637827,774124709,886868154,42585972,1478459553,1449526326,1774952735,756492534,1265414590,1061558687,347869493,1022502405]
def s23 : Fin 16 → M := ![1202730148,379935560,1636959529,914430904,1136987334,1121513481,1449673835,22736703,1283717555,1643969689,429117615,2064929601,1723195770,1022071331,336572525,835781575]
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
def left : Fin 8 → M := ![1603344092,1242405009,1153352827,393697509,714169239,2094351560,55834509,664305674]
def right : Fin 8 → M := ![1032062983,1528648228,154569178,2087313457,1156495396,824542697,187424622,409204906]
def output : Fin 8 → M := ![1202730148,379935560,1636959529,914430904,1136987334,1121513481,1449673835,22736703]
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
end AspisR1.PV_2TNV_Node04
