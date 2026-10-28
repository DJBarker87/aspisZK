import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node20
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![1583862150,1769341315,1908435521,764954908,376807725,1915039637,915881628,1026970083,19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,1761530072]
def s1 : Fin 16 → M := ![1979301055,140396787,257477633,1595132802,1419232100,804059796,144542916,1946111600,1964598870,985117448,490323822,646087723,327287408,837920765,314987873,1236606609]
def s2 : Fin 16 → M := ![291481321,793078632,1846415350,1798376739,1245034842,1404559938,1896077475,1041900127,1752145405,1274770858,1435603743,1515813582,160105161,36803311,376318256,2024358877]
def s3 : Fin 16 → M := ![1021479524,1332699691,1632868014,1276713578,1303669711,1376496251,1282769149,937727778,542869494,648408976,1870644916,1874429455,1589856834,1530933446,1353946938,1186418864]
def s4 : Fin 16 → M := ![1724535170,2039517160,1248841599,1434777131,37507156,1622999200,1968612395,837244699,1529778693,1839721684,1963021068,346371659,62961929,707727450,583892188,1010975138]
def s5 : Fin 16 → M := ![501225238,384901975,766018358,1812116116,1324614341,1829310343,1757570310,646002175,601369509,855242910,1423850391,1743269959,1830271312,1431677806,1859836498,1576390966]
def s6 : Fin 16 → M := ![345748073,1069334194,68985288,1490445742,543928712,2036110296,1092107317,1226382126,350318079,583285185,565836290,735058008,536196769,329729542,368380470,2046973766]
def s7 : Fin 16 → M := ![1730432350,1802725295,871361677,252723128,789853503,1098901132,1321086893,1912435873,476948626,1878026818,329167371,758918775,1653264634,2100835024,819052274,50175234]
def s8 : Fin 16 → M := ![992868123,828554981,768553040,36722198,1049690416,1575862269,498420969,1162641326,2093195345,911841813,1085768658,148294877,537833432,1386452433,627607559,1659985200]
def s9 : Fin 16 → M := ![1867603000,1933997249,495064701,1252331060,913031008,549434808,2022527747,352559487,598990553,461228873,536018914,783386359,400473568,660086574,99048261,521436095]
def s10 : Fin 16 → M := ![681746532,789161114,1992776914,1717004458,1864444635,1203669852,1299026006,2091618210,364027004,965638415,130201816,1412605358,327103952,1133429636,1768273343,931294721]
def s11 : Fin 16 → M := ![21781855,240708128,1289617195,2024597552,1482202212,1530395470,218189913,171126340,949846939,1841845496,1781704131,162148364,1175013989,271607629,976170731,1297134730]
def s12 : Fin 16 → M := ![1029303910,2118734445,162293413,1386481937,850742131,594550073,270168945,2092693842,1051866630,944070953,981956511,317794691,423434704,163819622,124134013,612041455]
def s13 : Fin 16 → M := ![1402842647,1283138411,1636474439,415364420,1675373720,87270546,1367359265,2100307387,659346492,328399470,1813008081,1623851867,1902892876,978015711,1601198179,1361123827]
def s14 : Fin 16 → M := ![1600150061,842015733,684342553,1220335002,76965200,955206058,364700862,834563976,203366065,2024763056,653281258,99269795,1621007588,992796079,300343290,2141758155]
def s15 : Fin 16 → M := ![1240664241,2008460715,387646441,1752817696,1782166582,1417356381,2099454331,891448271,1427497538,1962228391,111555310,1901116019,421732830,2096260940,897817501,1750239495]
def s16 : Fin 16 → M := ![1039554427,1982313877,749146044,542673005,1346283936,1176718788,584398697,1191967684,157428031,1940631507,389857311,169362964,1655492146,407127651,1279245677,125360271]
def s17 : Fin 16 → M := ![451133576,1009908068,525886279,1198286211,1207931091,675225623,548483319,151598322,1998512983,1908021173,957005960,1248560401,1607507065,1470304240,616632334,513364672]
def s18 : Fin 16 → M := ![412103601,1807488891,1849353381,1295758373,1871094963,863772556,1169177855,1909938843,1056688654,1772213242,1519140831,1742419812,1125733899,1938180584,932266712,38427466]
def s19 : Fin 16 → M := ![1405676249,1382935473,1126669697,463512780,1659304404,510905596,481915943,1552448302,1687608180,142987017,397497098,438837553,292766972,2032930296,136186823,1107024074]
def s20 : Fin 16 → M := ![1395117814,1796590151,399785637,154536037,1929505133,1008879756,676545341,1834559760,1918541993,608846699,413083101,1862312339,1416011476,1930353832,2134586338,909321912]
def s21 : Fin 16 → M := ![1187996464,456368646,1474075434,1849690088,1118244940,1765420386,1886140117,548009894,1234186426,946836166,200757022,661514462,1090625551,448517607,1159405406,1274900404]
def s22 : Fin 16 → M := ![507176338,526798407,138095346,1179213339,186710490,1681751255,669891794,1942086029,546762680,1313907328,372385603,677485201,1800582702,2069087504,215685822,2134228824]
def s23 : Fin 16 → M := ![67464615,2144218473,1164697229,2001687059,97906516,820214304,716699029,134105794,382485274,1438297454,313219866,815130429,226379188,695258693,1708545804,81826835]
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
def left : Fin 8 → M := ![1583862150,1769341315,1908435521,764954908,376807725,1915039637,915881628,1026970083]
def right : Fin 8 → M := ![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443]
def output : Fin 8 → M := ![67464615,2144218473,1164697229,2001687059,97906516,820214304,716699029,134105794]
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
end AspisR1.PV_2TNV_Node20
