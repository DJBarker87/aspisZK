import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node15
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![679809621,1897894089,763660077,1555132944,1225618854,509736473,1208445302,908065390,1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,628703965]
def s1 : Fin 16 → M := ![319482295,772830793,955962720,1455762684,1339312878,1377096562,1209465772,855682884,416434878,335262725,760482574,687731409,2053832655,572598308,951461994,1730613857]
def s2 : Fin 16 → M := ![286443717,368279587,1914400193,383664690,363235448,421834726,467254935,2003689636,1447449674,372403212,849832136,1418207905,1014377034,1948171534,358019197,1285511813]
def s3 : Fin 16 → M := ![420748576,650117723,2126114848,626975420,1445450138,405755264,1354039428,1964526137,1639866696,676827882,544606044,1999436489,479205967,659782220,397654193,901298958]
def s4 : Fin 16 → M := ![857128509,1430935097,142267402,1065984905,199551320,1579411760,2092230017,1520584615,1253975915,1423697259,1816069593,1445305168,1298815030,1611822952,2031239614,1246474199]
def s5 : Fin 16 → M := ![832131467,1884877357,372705476,1516361494,1263768087,662720775,1321999013,917685256,423409508,706610681,915520427,1488386487,1567137256,887593324,370376181,1233657889]
def s6 : Fin 16 → M := ![93886912,644354162,1652371404,529955487,279686913,773074617,261255928,1656758367,1416286301,1410668440,2097007608,631937371,1238119838,476723384,1963570263,1446031700]
def s7 : Fin 16 → M := ![214791658,1172911365,1685816364,500895504,618568860,12849193,298812311,1334393988,1424577383,882425147,380700795,1226234184,641005318,766456520,2041387420,1356189940]
def s8 : Fin 16 → M := ![1766350383,175722155,226959871,1006392806,1803878023,1355881525,2122353801,652163789,960089466,1565349134,145884763,841261768,1668342578,289550461,1365152594,361020241]
def s9 : Fin 16 → M := ![1216541349,121899345,400096932,1824264767,1492299492,165445120,1289505765,882470393,431060959,1243597152,1155802859,1190609130,422646658,149553991,1182010372,941352367]
def s10 : Fin 16 → M := ![894100707,1390709125,2069003644,2123417907,322303834,1768448053,1730804967,1912340110,610037710,1802100936,1547447899,1068443923,1846593152,1282557097,1369622184,827322476]
def s11 : Fin 16 → M := ![1037185790,746156429,1345970945,1406667991,1933877976,1880812388,1054115073,1486130112,130862892,1131786462,1246648041,1277566973,1919222667,1790922304,1021917610,1241598631]
def s12 : Fin 16 → M := ![479419378,840544393,638846207,1426092634,533026243,122615114,1613815595,717434664,1812452611,2068913538,1056695630,1738545280,638696341,1496347739,578124773,1346884350]
def s13 : Fin 16 → M := ![134829701,1751530211,41194585,172905413,880228468,725343995,1013477330,1729647727,976686150,124390737,635552850,936679246,1841247198,1399027442,1950297295,155921130]
def s14 : Fin 16 → M := ![1722526323,779976031,1258318637,1867551119,1775306270,2044015152,1394949322,204234351,1637705141,807703434,1294502826,260843894,747838955,601091117,1551840954,1895912721]
def s15 : Fin 16 → M := ![482360680,33973200,1770634443,281750704,571545447,1893468543,942702533,1587577398,574341458,2015129808,1974964441,371214434,927355285,1318336602,1860584175,681232499]
def s16 : Fin 16 → M := ![199629466,1231710969,444039361,177256938,1475134051,1428463399,1299447767,1870959832,1699000395,1674893337,631729879,1273637357,295089403,1434103411,1759245839,265771103]
def s17 : Fin 16 → M := ![1926559585,1013862761,670230514,491179544,845805965,1162729706,562291043,1411980455,358354005,1205600311,280970141,362987501,1235438293,513855789,1846267723,1264780830]
def s18 : Fin 16 → M := ![144025732,1552702427,1879300694,356074195,862836445,1962645786,1352283866,711275612,1310995719,2082357761,489455352,1276960038,158907611,1416190402,130283646,641507640]
def s19 : Fin 16 → M := ![1152859700,555142410,613557724,426736763,1610164249,340001501,1473334402,1574406211,1453651196,1657565990,1988514327,308075186,1545982860,452664163,1086945522,1707261351]
def s20 : Fin 16 → M := ![1862686923,579260064,168699326,1202078094,563022474,6190624,1587164373,1263816995,449794426,559153536,597424526,2017856615,1335198684,1894917009,1199205596,114600342]
def s21 : Fin 16 → M := ![1118531820,1913108770,998302531,524138500,1295203499,557300843,213341310,1213472166,326009853,289735804,694550238,668867981,778338551,560827388,2127396036,1140245785]
def s22 : Fin 16 → M := ![155699948,1919946093,247805437,517927301,421210403,1643325399,1559358710,1654149377,365252680,1910573394,1539831857,1639331047,2107910783,1452433666,1807040104,931089467]
def s23 : Fin 16 → M := ![1905130866,103172962,879709043,1820432331,505138134,43749841,2088595767,1314077240,540238016,83036264,2071299537,530906279,289765002,425572497,974053953,1442624737]
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
def left : Fin 8 → M := ![679809621,1897894089,763660077,1555132944,1225618854,509736473,1208445302,908065390]
def right : Fin 8 → M := ![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983]
def output : Fin 8 → M := ![1905130866,103172962,879709043,1820432331,505138134,43749841,2088595767,1314077240]
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
end AspisR1.PV_2TNV_Node15
