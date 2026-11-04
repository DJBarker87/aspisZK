import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node09
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![1179016775,1681327293,1727920564,737377660,1373988789,1506472451,64326735,1181453800,27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,1649667347]
def s1 : Fin 16 → M := ![1677550569,450109107,1396868329,1690416335,323412382,43633384,1569509910,1325035986,285632846,1307101374,539644570,685517558,1861745370,1822739280,1638917249,1300549932]
def s2 : Fin 16 → M := ![631071418,2122587596,1145336054,366764505,1154482898,487184364,844428827,1515376548,1762526946,1812701268,643614430,1275790634,475787786,794148910,1676897163,316789095]
def s3 : Fin 16 → M := ![1255537446,175871652,866753480,630210144,1939990503,288154556,2026033064,69782041,786953674,1180091221,2000474518,1396278048,547200601,209649027,1059880890,739365750]
def s4 : Fin 16 → M := ![325968146,1999105336,89481434,1653091210,1446355408,1961082184,300807133,1627324752,2032743228,521909649,1425687559,1432193263,1642491531,790354184,405248828,1869423589]
def s5 : Fin 16 → M := ![1187892990,1007885276,1446466968,803137836,560255764,635243434,338237946,212491872,1845032690,2107905445,2047076533,767759477,818245834,1703313936,1685484026,69011123]
def s6 : Fin 16 → M := ![1899167298,1139043240,876608253,1196225661,318236782,1705118320,217354001,845735890,72141114,736556487,393488284,957916548,904567805,676692623,1087288386,243554310]
def s7 : Fin 16 → M := ![937251915,1468010263,2082183529,818902373,727377632,1841056379,841844114,768972808,973095027,2056350406,1681527850,502524562,1729843433,1950316441,1841095741,1805762679]
def s8 : Fin 16 → M := ![1448029676,1395517768,1944390916,1055633350,1451561267,1467122158,1096715389,1897126983,2077103082,219717926,1677624658,978779631,1707807735,1502893136,1842137069,1009103220]
def s9 : Fin 16 → M := ![1787617435,1452179616,1797960033,2131711601,931733749,2055779906,791815944,1213704528,1785367763,469876082,2104877687,1933545122,1709150410,410305570,1733788964,886378403]
def s10 : Fin 16 → M := ![1142747988,176109444,172366247,808325291,1882832526,1551637266,439719919,1239091975,1765220557,900606235,192583375,752543051,638193755,1694057245,1988304442,1133781133]
def s11 : Fin 16 → M := ![1101394249,1828172706,1996795756,590397132,1682337941,708455754,690715141,1497054723,2114511623,279025546,1288943738,281883066,612623777,859827867,1905652385,50725703]
def s12 : Fin 16 → M := ![341266190,2048897527,2066832686,434829702,794526467,818598650,848772863,1542946625,295273043,784304246,1544153275,1615044718,165422966,147773429,108589035,275711073]
def s13 : Fin 16 → M := ![475497759,639464967,576749165,329886248,651811882,950727605,2128978939,702387325,2025778592,1803958892,1403040495,1711583255,820807302,1643841654,603146888,811525357]
def s14 : Fin 16 → M := ![857798181,1176789213,1690822576,1856869238,1456852008,716580397,2092657237,392956459,2138946382,641816493,584231283,1795712918,819443473,1646566355,1162546889,83118996]
def s15 : Fin 16 → M := ![214960188,966426860,1023799152,774663658,707035476,517505764,182676174,1316530906,844351374,885902683,1042017573,2045742447,1784171588,443224353,2061165913,1057630711]
def s16 : Fin 16 → M := ![1431310746,776034320,1857205764,760778445,1170923974,1647248743,1360277734,315723211,512400982,1114911373,1683713300,1836963425,2117038521,955196505,1733546494,513692984]
def s17 : Fin 16 → M := ![492250301,487873570,1278767131,607469383,489296454,298015374,291053798,590771931,874655536,1661309334,1552373556,1278812609,1560953757,938041481,1473407845,1141588302]
def s18 : Fin 16 → M := ![1069024168,550342113,472519158,344862428,1829356528,535747233,786255491,1364650128,349227507,155895941,555091107,366299974,1278011649,1541115315,963381649,1158134229]
def s19 : Fin 16 → M := ![1678903862,1898382681,145595237,580006633,950507263,1330061708,738412516,638819233,952004877,455212171,678167681,621664819,1836690051,868640102,1428304100,170852744]
def s20 : Fin 16 → M := ![248788197,1445568276,809276345,221284353,759505415,838479122,379153261,1564839934,1461734064,1428166647,1030365646,174492953,1852160681,52486650,275880229,639162625]
def s21 : Fin 16 → M := ![555476437,1299812399,265457056,1838595656,1267922313,949142343,493479774,795537738,1517298316,352753507,1517547268,1792540333,750498564,309209322,1851733480,922582633]
def s22 : Fin 16 → M := ![1458488867,787193389,468709777,1748513887,1743286844,1724944975,1011851617,1808556666,1130548414,586390299,673069128,137596618,115393210,1183247885,2145590480,273209571]
def s23 : Fin 16 → M := ![1197839198,449684346,391417085,13476115,411598282,1584375671,1644734677,28127165,1749647352,370415505,283233201,406837960,373095554,2005376064,951902704,134029442]
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
def left : Fin 8 → M := ![1179016775,1681327293,1727920564,737377660,1373988789,1506472451,64326735,1181453800]
def right : Fin 8 → M := ![27092219,1272373356,998194489,1458413288,887470405,1204987730,864453460,553704718]
def output : Fin 8 → M := ![1197839198,449684346,391417085,13476115,411598282,1584375671,1644734677,28127165]
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
end AspisR1.PV_2TNV_Node09
