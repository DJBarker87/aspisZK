import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node03
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![560027647,109760138,2064904093,345398497,1214731266,366495038,459312327,480913462,419899633,1577591246,694069026,1900771153,373160155,13932930,808890691,658007395]
def s1 : Fin 16 → M := ![1136043930,1572367611,763725899,1491816655,1745579067,206764344,1018009428,230616929,1148851521,1810769268,1868393180,2131690319,1678906465,2033381689,1054314736,204591365]
def s2 : Fin 16 → M := ![1020439488,2063809571,1430792408,139965292,1498482970,133340513,1972741764,439620115,1904270627,183860968,1590416992,84298171,789265547,985910893,944305305,304927337]
def s3 : Fin 16 → M := ![1253550037,189826429,603073331,1761817410,62019238,920072232,80524491,91450891,1531254457,1759185598,370552846,779239169,105468707,142228828,914076646,969667015]
def s4 : Fin 16 → M := ![1911691765,851718954,2138804005,1722114271,508731772,265880230,680129344,380328424,26613614,1145537757,467946842,2129854767,586306874,808245983,897560708,708463442]
def s5 : Fin 16 → M := ![2021622715,1522566190,1241453870,974803838,1616038364,134638399,1712450729,228535413,1910854007,1643604702,1856971220,330659642,883522482,710108399,1060387133,724295836]
def s6 : Fin 16 → M := ![338317804,2073774129,886632032,155455997,594612969,557938676,1662540092,145088842,327385077,407216839,1566709624,2018403961,1347490093,2048301356,1031373623,24582747]
def s7 : Fin 16 → M := ![1495387438,208627747,2055601329,904161253,744273723,619421493,1944012681,978088565,1385437828,1450632993,422707932,2000404218,855233541,924802300,1383062890,724509407]
def s8 : Fin 16 → M := ![1559358915,1786453574,1394061191,899503545,1089564670,751151480,1509205856,1898468224,672725110,1425201104,639051501,435905803,411853538,894095795,1287719059,15404162]
def s9 : Fin 16 → M := ![238680951,1703730789,557915950,1367807748,43859987,1198282660,967224373,1160159319,126745415,1844023496,1470985551,828535646,124651074,796826308,2136706271,127123957]
def s10 : Fin 16 → M := ![315548380,232568439,1792153197,1852584995,1027201193,521491034,1562730175,1912073715,1867348888,299933933,1579488974,1334165053,1763187180,1325461456,1858066284,1782900536]
def s11 : Fin 16 → M := ![1288771853,1711801044,768571705,299637997,1106907561,1233154561,2094474324,1445382486,2129205452,952908161,1820755790,873408078,1533601443,337605598,1138866973,1063526631]
def s12 : Fin 16 → M := ![9140325,67570681,2040396694,1701805272,768579184,906373437,954438595,665935567,311127971,1782090389,941376648,274984870,986939390,2062979891,2072890629,1055295468]
def s13 : Fin 16 → M := ![1483687280,1704681715,1422937128,2001881181,1343293565,1106700497,2114375016,1307314382,659302029,438233807,1386641083,546223879,1368662959,107041398,1209487496,1770050247]
def s14 : Fin 16 → M := ![1947533770,223578710,1364771251,83970778,675310927,1193719418,1754388097,582638857,1305178121,1185085590,1100158967,321428852,741219783,2085989522,1341944185,2055208035]
def s15 : Fin 16 → M := ![727678876,1460310962,1818791107,1572615364,196768727,1008890117,1542576534,2018397101,795807274,1823449065,370599785,1401834433,225440872,886818695,41146713,1176174172]
def s16 : Fin 16 → M := ![435642042,1491656057,1521443662,2026839257,1605494911,1141201438,1670302,359740739,962944758,830354336,1568403063,1721394232,7032099,1941972020,1854590010,3855869]
def s17 : Fin 16 → M := ![1211096412,2145490446,1549238066,171256829,612891795,1733188221,707284053,54921568,1504195534,623663352,380802945,1295795560,278730928,805696117,219555616,2096478474]
def s18 : Fin 16 → M := ![350307861,88790535,1041776221,775811052,698950802,2051991508,1249036962,1458280441,1501767505,834811970,1338459309,1237305759,679429151,33986555,418991374,1047804387]
def s19 : Fin 16 → M := ![1774640172,1458733661,1306011921,178220040,519098601,1989552549,536936617,210610882,322655536,333442746,1857708756,1312925070,975935094,2007395673,2016331087,193669439]
def s20 : Fin 16 → M := ![704399483,663639497,1939355859,872473441,2097233888,981764860,1110329848,1008005355,356426666,380580855,1750869247,1510139256,434170388,214914363,784668807,1572204562]
def s21 : Fin 16 → M := ![1782178661,1536858282,1483561676,352587336,701526053,904778946,1772893738,667190903,573134329,1647274433,2130219122,452916085,1877356910,951730840,900941461,941288019]
def s22 : Fin 16 → M := ![1483366082,1693477442,438703574,1100826906,37053470,1713146572,1360840730,1942092496,189638564,1334358779,1542866855,1085314978,2038863975,672440992,207256797,1934819445]
def s23 : Fin 16 → M := ![1032062983,1528648228,154569178,2087313457,1156495396,824542697,187424622,409204906,1613491024,337153401,143750701,957235572,980980848,1046874961,1944227107,1519210945]
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
def left : Fin 8 → M := ![560027647,109760138,2064904093,345398497,1214731266,366495038,459312327,480913462]
def right : Fin 8 → M := ![419899633,1577591246,694069026,1900771153,373160155,13932930,808890691,1709528413]
def output : Fin 8 → M := ![1032062983,1528648228,154569178,2087313457,1156495396,824542697,187424622,409204906]
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
end AspisR1.PV_2TNV_Node03
