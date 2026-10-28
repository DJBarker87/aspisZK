import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node11
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![782654342,937915787,1712321222,2116602281,1407017630,1177878323,1825454929,2010056932,418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,749307875]
def s1 : Fin 16 → M := ![892472475,1355212671,1831017017,1192854324,720191370,544873156,454490561,1058466086,203125805,1962318863,1856607668,1200641167,261380631,598039584,1224963934,1452443645]
def s2 : Fin 16 → M := ![1607202291,47158692,98027716,964738964,294134967,599107398,596400539,2128948403,659896771,1149678166,664994941,1640752577,1828166187,38750582,1824799638,1716196712]
def s3 : Fin 16 → M := ![583173025,1216809466,215074055,1472115843,1367090822,1191217957,1729558436,634880827,899079244,1315338871,1352461365,2087038532,177808999,2029210462,1029707932,1943184408]
def s4 : Fin 16 → M := ![1865594771,1055149823,2074979644,1653942372,1331356768,1982738736,428479360,1684361075,696861032,155237597,460988405,182665201,1068996102,1878538072,1266321312,699618154]
def s5 : Fin 16 → M := ![1990303488,1195337059,649990986,923202474,1212859741,391507193,806868129,1759282217,137301160,1914055506,1008565473,729686869,1634358246,1188070513,96748436,1377565382]
def s6 : Fin 16 → M := ![1063113733,118251036,222895949,468240226,35857317,892061771,1120373988,1995309868,1465076928,1442335644,901807769,570576424,172609811,1625906208,1637285500,982752496]
def s7 : Fin 16 → M := ![33010841,1618118301,1945659163,1225344522,1786725801,740470072,844612882,350679997,51153113,1370604845,1533054511,2118692033,327715604,812538102,1487178264,1985387944]
def s8 : Fin 16 → M := ![262108245,1244658365,1370374743,232950858,1035444590,736642981,884348524,595223402,1879171234,461545923,1811297018,1955173352,2065692929,2147159126,784977092,124149965]
def s9 : Fin 16 → M := ![184992256,1357547961,706155435,1044693028,1953995375,1161759057,494754953,1699965325,128639084,157045299,1602648667,536419725,98225604,1238388473,1830600133,1736941000]
def s10 : Fin 16 → M := ![1026916755,1761418386,1816181295,287675243,1003447896,1812146161,1203643392,1827468875,1837287648,1952761323,838599125,703293144,1909134415,735115201,1995800565,903569896]
def s11 : Fin 16 → M := ![654889234,1479424989,1202885546,868707575,1303138830,795057768,1727373148,711897665,815108024,1408699187,1597535450,631153800,1371216829,757167411,791418432,1360628481]
def s12 : Fin 16 → M := ![521311721,241201186,1167547289,89122850,596952249,745282250,350625758,1373553817,16388213,758999020,403021630,544913656,430565555,327092949,1095918448,1093916279]
def s13 : Fin 16 → M := ![1902476496,1776541459,1722951204,1891831673,2015990971,574954391,2017946294,1395955034,1485547890,418077516,1912629169,118682369,412734812,507033777,222015556,838529369]
def s14 : Fin 16 → M := ![1624500617,415145458,2084506407,1910963397,1881629885,1395423314,935859644,2080380295,1957656630,439749392,813270638,1577766848,1770407172,1560743418,117230618,540287700]
def s15 : Fin 16 → M := ![479793712,242687732,1849071441,1028944921,1995679472,679478828,1857763471,1975378687,1299487862,734236982,1540504197,582257859,1046027107,959917957,1539672062,411877738]
def s16 : Fin 16 → M := ![586118862,782803150,2090774653,360927808,1473165665,674358431,2006488021,262816213,1518320935,1673705521,1763416248,1761457712,1134424432,1813175925,1680924063,1637593843]
def s17 : Fin 16 → M := ![1416060408,1980742336,1084521198,494166771,98362624,1250255847,981046448,838307642,122006989,169823162,902430011,583673618,93661914,2131005435,909573667,2052775209]
def s18 : Fin 16 → M := ![918613017,529547650,717847710,525472398,1483189953,1373029690,2025004239,660886874,1280798024,1221345493,1366652015,1274129178,1323026470,1300203075,680672504,111836023]
def s19 : Fin 16 → M := ![240138398,1971920786,730584909,1396779081,422990878,1936011706,1817999374,789460132,28279389,574206882,734698652,1890224014,1325248967,931775696,1953826466,1366289253]
def s20 : Fin 16 → M := ![1734821756,338387517,426833433,707838730,1673588128,980358314,554042456,265007251,1623195437,1900455714,188561756,1109748367,1892070069,324585772,1809060995,733874846]
def s21 : Fin 16 → M := ![531314826,1504965067,691597017,422193011,508740070,503782065,927624837,2031574424,1733401510,1331508520,754190647,2066298373,840795486,1765567140,438928491,1208842065]
def s22 : Fin 16 → M := ![1333168655,475685609,960150936,1942109717,1745695856,305477945,550133342,454805994,1212633336,1399433764,50164188,1429159530,1645412900,568882399,1742768794,1478330147]
def s23 : Fin 16 → M := ![932605221,382022248,683061747,928614086,159839169,394479800,1976348339,777778117,1851176207,2007851242,1117347773,1295054889,468435075,1700774765,1580680705,159240487]
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
def left : Fin 8 → M := ![782654342,937915787,1712321222,2116602281,1407017630,1177878323,1825454929,2010056932]
def right : Fin 8 → M := ![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893]
def output : Fin 8 → M := ![932605221,382022248,683061747,928614086,159839169,394479800,1976348339,777778117]
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
end AspisR1.PV_2TNV_Node11
