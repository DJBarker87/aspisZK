import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node06
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![708564806,100495163,988693857,52379155,474573668,874069195,2050287843,1592187062,1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,1657047221]
def s1 : Fin 16 → M := ![372704683,1811483781,957302937,266679572,531879102,1406779631,1797046583,184522696,1115325707,928103183,1680177347,1060753910,1077558887,303358549,666447607,403102118]
def s2 : Fin 16 → M := ![1997202280,463502200,1479152775,2128531473,30149336,840999644,2038695264,82405965,1350467053,1615784449,1484259314,2130703543,1911816240,399548494,1899718816,1935575273]
def s3 : Fin 16 → M := ![705555814,1679325013,1936734109,788560439,406232321,1055811027,2035466468,1941928196,1462809348,1559410298,1582716720,451070866,1686187893,440587458,1073384641,511940380]
def s4 : Fin 16 → M := ![1579363072,1495031954,1134125046,564687247,123860942,1182781207,920021474,1007516479,1049268877,1962511651,658959099,861622855,611232313,859706094,1274514203,2065600353]
def s5 : Fin 16 → M := ![1686772715,1326998423,1431374534,919616176,2131627151,1148188955,1936846469,981919479,1776172430,1398188032,1803100651,418470498,1038820549,1552425081,420335960,153179763]
def s6 : Fin 16 → M := ![304024776,1390279950,778546948,1594262584,2083913206,1254435631,1912826419,629102420,1927569632,1517132317,1749895378,426491029,1751009521,199493563,1819390596,1513663417]
def s7 : Fin 16 → M := ![878535658,805580221,972394167,1497383313,1054220390,158917544,496203563,1023149505,1331077409,1254116963,306805745,418350044,642017990,1595209376,912825632,148890912]
def s8 : Fin 16 → M := ![518519459,1899026193,890750659,640528283,937274504,1488643029,1939574459,3021235,1820146211,24841450,1729916390,963275890,1317368549,2127878366,264036285,642562836]
def s9 : Fin 16 → M := ![278717055,638259464,520734589,1301346403,1942462009,1082685265,676073843,1080075958,1937198050,803677177,647091503,1537302819,1664544151,1796340064,616090035,1877902991]
def s10 : Fin 16 → M := ![1557538211,964551543,1367761257,1236710397,833602622,469387143,485818585,731676687,1327023074,2056702926,1523027875,696585699,1898302268,298518520,2018277159,436384332]
def s11 : Fin 16 → M := ![1292287072,148669940,1919640911,1983476338,1557972079,251861744,1845411235,914269778,1539347403,1714057585,1839018322,540858285,147209926,291285858,183671497,27973250]
def s12 : Fin 16 → M := ![1259127639,781703192,177347780,2124487663,211908002,367853862,1704134303,1164240575,101005312,1345111024,444636561,1932928555,1838421077,1351867090,1931468054,2084394361]
def s13 : Fin 16 → M := ![1677217750,2015245559,1588237927,1141558431,781322736,676753218,2078748888,583011522,1277320421,1984580991,1274847667,736697158,1276188740,1077609769,940691455,520115546]
def s14 : Fin 16 → M := ![420406347,993477269,7223917,1396981787,933846304,1216348610,1073686716,1931230766,1413972073,224824714,899668989,1422750490,1713479841,73625019,723043759,410209182]
def s15 : Fin 16 → M := ![310620463,1634308267,655278832,1933790852,1669150489,775055935,639067558,1833032143,1240629994,213899313,631391171,2103703727,1514571678,27332680,151648559,1909489404]
def s16 : Fin 16 → M := ![1042320565,96950554,1920683598,1902838401,1078427964,126119012,1732934967,1960066148,496975288,1681258887,762107291,1676199962,1968283391,1752156478,552948088,593144847]
def s17 : Fin 16 → M := ![1007623050,1331778904,781228252,256247366,1272317474,1105248895,854172472,2125010296,423155804,2140374022,2096130473,1444653243,2105145746,1005170806,1918246195,1974026995]
def s18 : Fin 16 → M := ![1655810397,539593100,770270700,232803660,796419400,1859410987,771529536,2064487026,1832149580,1682717490,309255195,190050039,268080018,1021694504,1600267913,331095942]
def s19 : Fin 16 → M := ![174660936,987294933,1988243233,1378916473,376606092,133506567,1514326868,1578369030,887130550,1726649873,1444925404,1503581363,1830922055,255427004,770982571,976587457]
def s20 : Fin 16 → M := ![1020168570,471884886,200432770,120369755,98568679,437978563,2104016437,871857910,445253117,839656072,1930964195,508770684,1590773756,1831928273,149662583,455324890]
def s21 : Fin 16 → M := ![1521942752,134886600,175564832,789909224,1801374615,1733449703,870184336,1558856126,2115501316,1268558168,1793599659,141495623,971172640,2065154668,646465234,1147253094]
def s22 : Fin 16 → M := ![1965833593,80603293,1844994272,342385278,1697989645,1687754431,1533554224,1641504067,1294507564,2099278064,245468992,1235945013,1410412695,131081320,1743684483,268299176]
def s23 : Fin 16 → M := ![1155231487,231917266,23510830,1282340338,1179486231,882350493,608913733,1480730980,837142164,314790033,1272678713,2085954473,1566875849,395055805,1252555366,353381109]
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
def left : Fin 8 → M := ![708564806,100495163,988693857,52379155,474573668,874069195,2050287843,1592187062]
def right : Fin 8 → M := ![1442759752,1540325866,188964047,101815282,1883549730,1774537487,1306717763,561084592]
def output : Fin 8 → M := ![1155231487,231917266,23510830,1282340338,1179486231,882350493,608913733,1480730980]
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
end AspisR1.PV_2TNV_Node06
