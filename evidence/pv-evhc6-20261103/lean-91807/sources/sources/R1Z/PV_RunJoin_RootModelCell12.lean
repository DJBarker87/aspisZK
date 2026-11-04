import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_12_0 : Fin 16 → Scalar := ![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062,986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,228521044]
def s_12_1 : Fin 16 → Scalar := ![1987188172,205820471,1677926243,1191116631,694184902,1373034012,101410077,800418133,1987188172,205820471,1677926243,1191116631,1790147531,321512994,1241814317,844859744]
theorem round_12_1 : poseidonExternalLinear s_12_0 = s_12_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_1
def s_12_2 : Fin 16 → Scalar := ![2075784374,976051548,939693972,1388604255,1838146386,578404812,298658773,1459217408,1919347094,1709098668,162011893,1153704733,149526297,1171423636,500877974,468784495]
theorem round_12_2 : poseidonFullRound s_12_1 (poseidonExternalInitial 0) = s_12_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_2
def s_12_3 : Fin 16 → Scalar := ![807705573,1159421812,1176001975,742465630,1976974580,1613314189,1341785741,1204381263,43079564,2121593223,529543575,752364382,1253127536,118880340,1564389200,810308223]
theorem round_12_3 : poseidonFullRound s_12_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_12_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_3
def s_12_4 : Fin 16 → Scalar := ![58845312,280490968,1878362317,1361114138,1730847010,4008985,1285706708,1424640931,1307193924,1131439677,1524680131,416186015,235369861,591980801,1578550315,153243850]
theorem round_12_4 : poseidonFullRound s_12_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_12_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_4
def s_12_5 : Fin 16 → Scalar := ![1587565100,1512348080,1263629805,448041697,182576186,1209165121,1154107328,279215481,1708159908,1087402113,336887029,1900305442,1699489616,71666602,2129356101,316404281]
theorem round_12_5 : poseidonFullRound s_12_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_12_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_5
def s_12_6 : Fin 16 → Scalar := ![373615567,1671471035,538898918,1951289743,1619732443,178412068,583335452,849044563,1907742832,1508673420,1534057131,1329476659,241573726,1818658861,1008665846,2075470786]
theorem round_12_6 : poseidonInternalRound s_12_5 (poseidonInternalConstants 0) = s_12_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_6
def s_12_7 : Fin 16 → Scalar := ![1350401518,1446854484,853181285,1138091480,1995824758,482492890,1262248737,427144306,1300813834,1596206156,839339636,1440733568,914907954,346559948,1964497847,509581059]
theorem round_12_7 : poseidonInternalRound s_12_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_12_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_7
def s_12_8 : Fin 16 → Scalar := ![1753224413,518331250,777839336,1476359039,5689301,348912065,808730704,638908586,219406699,1825843419,1709288877,1178592985,1426991551,1310385777,914608437,1605048540]
theorem round_12_8 : poseidonInternalRound s_12_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_12_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_8
def s_12_9 : Fin 16 → Scalar := ![2025795673,105121298,1142468720,1197258910,1779788103,874415794,1843852459,1822233906,1901043756,998753913,1846911438,1707901799,748085219,553341357,1341759779,3910134]
theorem round_12_9 : poseidonInternalRound s_12_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_12_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_9
def s_12_10 : Fin 16 → Scalar := ![590556020,888520096,920852591,1277467144,2136801740,1889149620,1804619017,1442251844,1451347455,913846533,87618303,1994929223,179184308,52234252,2135132039,1487386629]
theorem round_12_10 : poseidonInternalRound s_12_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_12_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_10
def s_12_11 : Fin 16 → Scalar := ![1848401396,2003061936,808763375,1929443122,1029086584,1276164702,880291915,1076863035,55938791,983536765,641370938,1169362413,113578428,74551455,103976532,2054439007]
theorem round_12_11 : poseidonInternalRound s_12_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_12_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_11
def s_12_12 : Fin 16 → Scalar := ![1674125313,812507208,426972022,84766819,599687003,2048211328,1208982788,1156686455,1674643226,1486754060,590773449,1776839757,1530991944,489772496,3381706,2036959359]
theorem round_12_12 : poseidonInternalRound s_12_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_12_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_12
def s_12_13 : Fin 16 → Scalar := ![1862090836,741504554,782941390,268064622,431526076,488123889,2109224563,942486468,1682449221,433431187,1438104315,42562335,510504114,1362666618,1219073557,71600309]
theorem round_12_13 : poseidonInternalRound s_12_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_12_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_13
def s_12_14 : Fin 16 → Scalar := ![1785422864,382288009,1206666235,713041943,945508416,1008314738,563976414,1977858938,245919043,1077501330,1233303820,29932208,539824634,330658555,899781384,1934349031]
theorem round_12_14 : poseidonInternalRound s_12_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_12_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_14
def s_12_15 : Fin 16 → Scalar := ![1770075540,1167741748,1051302562,1490137864,1907070126,1886104018,1652829811,666890598,50836538,1747887403,968180983,981209828,1360026294,193977478,2018854988,28899651]
theorem round_12_15 : poseidonInternalRound s_12_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_12_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_15
def s_12_16 : Fin 16 → Scalar := ![171054965,980848211,1915711587,1478690625,37281942,2073483340,1164052887,1691915442,2025216033,595683055,1240471788,906658414,3346275,1811792102,419607412,1847541392]
theorem round_12_16 : poseidonInternalRound s_12_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_12_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_16
def s_12_17 : Fin 16 → Scalar := ![1951439003,1054271866,1757363182,1693218861,371679191,1036902390,815894040,981829593,1603038239,96946798,1153699190,747061736,1716304691,1956253989,1578791977,1123104613]
theorem round_12_17 : poseidonInternalRound s_12_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_12_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_17
def s_12_18 : Fin 16 → Scalar := ![260279988,1806974238,2119945089,1083126875,1578652253,163271436,1091507888,1312770561,1930650499,1948762543,1024667082,553376053,1145294135,824626673,1727148478,1682102662]
theorem round_12_18 : poseidonInternalRound s_12_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_12_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_18
def s_12_19 : Fin 16 → Scalar := ![326034051,664503824,949936117,1042553439,749329375,1469872562,1573527297,1270466904,1167657700,1672018137,144601818,2038078736,898513410,1868800388,1422307299,359534967]
theorem round_12_19 : poseidonInternalRound s_12_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_12_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_19
def s_12_20 : Fin 16 → Scalar := ![812948195,1426887972,134973598,289054646,1052417037,1538843632,685022182,1766457423,680792202,30341799,1986879093,319380704,1710492667,260089322,606727084,394414829]
theorem round_12_20 : poseidonFullRound s_12_19 (poseidonExternalFinal 0) = s_12_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_20
def s_12_21 : Fin 16 → Scalar := ![188005086,1851656260,870084979,1654862778,455846859,699543090,1352905871,1140551217,475263508,1035888201,567033302,1334822479,1904527531,1040165311,102423269,964358141]
theorem round_12_21 : poseidonFullRound s_12_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_12_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_21
def s_12_22 : Fin 16 → Scalar := ![564131182,491368834,1119480286,899728785,653007168,726573737,390661829,742482404,593933884,1900759250,958869280,1396031441,53010859,1153228975,1125454997,464682089]
theorem round_12_22 : poseidonFullRound s_12_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_12_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_22
def s_12_23 : Fin 16 → Scalar := ![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184,260494225,993221130,911405434,1914555187,1421815938,208147779,2097140781,1339389206]
theorem round_12_23 : poseidonFullRound s_12_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_12_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_12_23
theorem permutation_12 : poseidonPermutation s_12_0 = s_12_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_12_1,round_12_2,round_12_3,round_12_4,round_12_5,round_12_6,round_12_7,round_12_8,round_12_9,round_12_10,round_12_11,round_12_12,round_12_13,round_12_14,round_12_15,round_12_16,round_12_17,round_12_18,round_12_19,round_12_20,round_12_21,round_12_22,round_12_23]
#print axioms permutation_12
theorem parent_12 : nodeCompress (![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] : Fin 8 → Scalar) ![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] = ![2118470693,1706590589,2128512933,167263577,409542414,1323179656,1880070613,2053396184] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_12_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_12]
  funext i
  fin_cases i <;> rfl
#print axioms parent_12
end R1Z.PV_RunJoin_RootModel
