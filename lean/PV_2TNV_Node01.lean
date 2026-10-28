import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node01
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![20384,20401,20418,20435,20452,20469,20486,20503,1134794151,415789335,111944968,1818281472,628958070,505282998,905808425,1083335439]
def s1 : Fin 16 → M := ![1620586105,971268490,540709445,148843328,1620586581,971268966,540709921,148843804,625175087,796647518,1327433416,1274929246,2088384985,2116443101,293979813,1318369704]
def s2 : Fin 16 → M := ![562792929,1587235168,1917654313,1433367213,1678295270,921082166,340565952,1250796682,273339023,1515986625,511565726,189191632,1916729529,334606762,623609139,1810112193]
def s3 : Fin 16 → M := ![320821670,250873685,1009381933,1029149469,1593861143,1895401232,95743667,682752669,491229523,424377342,382265494,648005724,425848525,1933209603,43919966,393891286]
def s4 : Fin 16 → M := ![483279967,107589768,666600520,1383571056,2141944284,72242492,2048491979,973031828,22795074,1481424500,1687138545,465978820,1078697139,103327995,254034507,2135717112]
def s5 : Fin 16 → M := ![756794835,565248258,582225686,459379423,89795417,586782705,1299109342,709802183,1154366364,1629527869,1841065617,1795832791,1558063256,372135542,1418722415,1302967323]
def s6 : Fin 16 → M := ![741982418,488543164,1087746278,1760812598,641658242,721883598,692604557,253478031,1653301502,470601852,1831328295,522915867,1082173937,285941201,2040883017,797519373]
def s7 : Fin 16 → M := ![380674850,853363927,392829672,965620214,1203119405,1177540096,1053330117,1555029218,1534015613,579810643,891771012,1187015936,721217851,1563623840,1231270592,1137449005]
def s8 : Fin 16 → M := ![1861604938,1021002213,953297630,1882635495,1202658938,1828410646,1661947325,905260476,1100624873,422791251,660604599,281935334,656760781,1248207783,1667120753,573275302]
def s9 : Fin 16 → M := ![423186145,518628161,1404221208,585716987,528962864,834908873,1140332820,1599721590,791172637,358003854,1646870166,1106035573,235408165,1794655886,21447866,1588897202]
def s10 : Fin 16 → M := ![668857740,242450714,384781322,2066690501,1808041818,197462639,1854734441,1174272904,62188680,1178496003,344209642,1002518038,1894678874,19764053,300343072,356293442]
def s11 : Fin 16 → M := ![1764345154,629637729,1156749659,64014431,1966619677,1399105592,1756630658,378725226,1904887114,1434453203,670542315,712337599,1732205954,2078884317,111416110,844508096]
def s12 : Fin 16 → M := ![84606091,2014212293,1550590235,1640632288,2085146451,147943919,1762180798,2000668911,396989398,1384890895,825138084,689103795,1043810356,587099225,1545467144,2118603536]
def s13 : Fin 16 → M := ![1351684145,1592777158,532261688,1846126723,1227350944,1945667569,133775579,919839996,1001083928,1923315877,558889610,354197027,1340602510,33012352,1634059550,972187023]
def s14 : Fin 16 → M := ![1904193188,1654107980,1125854198,1003386773,1290203786,1127240868,47182056,949032097,1498538433,656440171,1133641360,1300891689,45721984,1917310593,1714894571,1765230954]
def s15 : Fin 16 → M := ![761148992,992575662,1590176078,1204531127,1070163382,194452394,848293474,2094463421,25342523,2030910639,546050942,2031381266,230806032,1311918725,1946662808,570205136]
def s16 : Fin 16 → M := ![1344936228,811251947,851544794,341833499,1937532400,782430942,1194263689,720349115,915035582,40757295,629092673,1004693343,796081069,131243862,1358801988,419527734]
def s17 : Fin 16 → M := ![904812459,152999235,1044836876,709081284,1957104606,1123224125,1050963337,346934061,502184846,1185680220,1435033987,2134496211,1077512244,10051649,786836821,1425673818]
def s18 : Fin 16 → M := ![2033864675,87073789,2023748306,622916043,558525873,725791378,1352646633,663017988,1936709079,673016647,530062694,424627873,756588232,1411534598,314359200,174897326]
def s19 : Fin 16 → M := ![109913299,865871691,531327220,1122978427,952037592,1654041715,1113817218,262276194,1716940609,1272367774,249633867,592811640,1111789204,1110256991,222008843,1729730599]
def s20 : Fin 16 → M := ![1456971886,1241281793,383605091,341424982,1589795963,622334715,1969554619,830184376,565231491,447734811,1375926522,334252029,1469122466,1577570619,2114233986,722825452]
def s21 : Fin 16 → M := ![1118545438,5304146,1100120931,241597267,1304975378,1715683586,651017693,1203057629,328216037,496160059,2089023983,289982458,1276504891,825455468,1030725686,1241326340]
def s22 : Fin 16 → M := ![1582321133,135570833,565412141,1146632590,1754591991,1295155360,1584893925,1746299213,2017172003,757665519,855372795,888511670,1391586913,696798018,358120876,579551107]
def s23 : Fin 16 → M := ![248012357,194341198,430781749,501414171,630694870,1921243919,1220508734,1000843895,2088944426,427049379,1231810352,575744566,327705620,1488022655,637735615,536291515]
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
def left : Fin 8 → M := ![20384,20401,20418,20435,20452,20469,20486,20503]
def right : Fin 8 → M := ![1134794151,415789335,111944968,1818281472,628958070,505282998,905808425,2134856457]
def output : Fin 8 → M := ![248012357,194341198,430781749,501414171,630694870,1921243919,1220508734,1000843895]
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
end AspisR1.PV_2TNV_Node01
