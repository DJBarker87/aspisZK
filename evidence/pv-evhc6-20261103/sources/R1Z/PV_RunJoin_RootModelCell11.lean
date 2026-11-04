import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_11_0 : Fin 16 → Scalar := ![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893,418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,749307875]
def s_11_1 : Fin 16 → Scalar := ![106489414,1526628854,1512267452,1557963958,1216265258,1213870593,1887703125,1765324825,106489414,1526628854,1512267452,1557963958,164744240,162349575,880623718,1809766436]
theorem round_11_1 : poseidonExternalLinear s_11_0 = s_11_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_1
def s_11_2 : Fin 16 → Scalar := ![1264527285,1118422220,272547294,1861326050,361461562,8919759,30726589,164723165,1016429067,1685794949,1715201885,1773600756,824076582,778972905,1532528911,2117612711]
theorem round_11_2 : poseidonFullRound s_11_1 (poseidonExternalInitial 0) = s_11_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_2
def s_11_3 : Fin 16 → Scalar := ![1534306035,1209291637,1908513644,1956615700,697234721,1929426030,2086781099,623584089,1384228449,1755714453,1153782855,835252823,1852376489,626906410,1249251381,2076477686]
theorem round_11_3 : poseidonFullRound s_11_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_11_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_3
def s_11_4 : Fin 16 → Scalar := ![1397338524,96251779,1361957624,490150632,1314999115,829224708,495532974,1987482938,1680381822,1476823991,1371999853,110095051,1571574148,993525739,147354650,775919202]
theorem round_11_4 : poseidonFullRound s_11_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_11_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_4
def s_11_5 : Fin 16 → Scalar := ![2019847686,690670050,2067081690,1339203764,1214836144,229475507,964117841,1625426506,1469232704,61574156,524689466,1043209100,1214924082,23690059,1544990321,1520760589]
theorem round_11_5 : poseidonFullRound s_11_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_11_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_5
def s_11_6 : Fin 16 → Scalar := ![1052957919,640705031,1936714714,1011882743,1078789545,1474159446,737034835,898116309,1180743804,680633388,361136415,1589534698,1168894527,1540905177,1413379131,1947422062]
theorem round_11_6 : poseidonInternalRound s_11_5 (poseidonInternalConstants 0) = s_11_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_6
def s_11_7 : Fin 16 → Scalar := ![1884837531,1863716445,801473548,975575092,1263393186,1187242433,1185806017,720396721,2034363036,1518983335,1659513090,786716718,1177394625,1595677250,50561173,374641789]
theorem round_11_7 : poseidonInternalRound s_11_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_11_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_7
def s_11_8 : Fin 16 → Scalar := ![1871159074,23727935,1910442233,2062311858,1824706037,2123504889,1746065682,1315728694,860442458,472688790,989334520,1473701565,1175204460,417640559,1386120164,651242890]
theorem round_11_8 : poseidonInternalRound s_11_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_11_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_8
def s_11_9 : Fin 16 → Scalar := ![1204073361,1325641690,827830927,961226599,867176522,918253627,1341440757,1756687938,1916882382,2051159763,768180851,1006992278,1407660574,2041933069,260830010,2065952317]
theorem round_11_9 : poseidonInternalRound s_11_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_11_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_9
def s_11_10 : Fin 16 → Scalar := ![121345814,1585288838,1915309002,1957069897,754608383,2066803298,236078432,1018525536,807456286,1370536608,897823770,1731415596,1975368613,1790796678,152499768,2109201651]
theorem round_11_10 : poseidonInternalRound s_11_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_11_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_10
def s_11_11 : Fin 16 → Scalar := ![881446766,639217491,737063010,439757300,795828423,2058010363,165987536,1962537194,1476601852,2018949487,1449951864,2088691122,2131809851,545115691,1119363555,613422140]
theorem round_11_11 : poseidonInternalRound s_11_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_11_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_11
def s_11_12 : Fin 16 → Scalar := ![674449895,2089643002,777067884,1061971064,1374601954,18852967,319575722,351270754,1476901631,757935256,142450523,1154411575,1899707499,1241418982,1734704991,1789920711]
theorem round_11_12 : poseidonInternalRound s_11_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_11_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_12
def s_11_13 : Fin 16 → Scalar := ![298927601,1959329726,1423822492,1970087333,129084121,171334196,1506175240,876178510,2082018203,627584030,1857617927,1727990877,1607012370,460667075,938179369,2114152739]
theorem round_11_13 : poseidonInternalRound s_11_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_11_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_13
def s_11_14 : Fin 16 → Scalar := ![2132684678,74407818,962723076,1700460130,1295234707,856425228,1215529185,503411557,472919495,2010283541,1940291392,7093419,833140669,1574382981,1295718326,2026527697]
theorem round_11_14 : poseidonInternalRound s_11_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_11_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_14
def s_11_15 : Fin 16 → Scalar := ![1998428499,1548306703,1251861390,1833288464,1098358306,144317004,1716127159,1479983828,1878052129,710410101,1909910818,463772051,1859229167,591091825,1672820416,866900762]
theorem round_11_15 : poseidonInternalRound s_11_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_11_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_15
def s_11_16 : Fin 16 → Scalar := ![634628438,307832865,1263248942,1797712724,1103941669,1068598226,2135987722,1136694333,779513857,235885670,298085024,2141786757,1758321349,204222639,1366311622,287983209]
theorem round_11_16 : poseidonInternalRound s_11_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_11_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_16
def s_11_17 : Fin 16 → Scalar := ![1710622860,304692163,375873535,745259253,238458062,2062045385,1776473345,1878336259,990385232,254048702,293246000,284717975,992529877,201054648,557016338,1178154486]
theorem round_11_17 : poseidonInternalRound s_11_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_11_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_17
def s_11_18 : Fin 16 → Scalar := ![420211028,526743538,973798445,1055604740,2129715871,1002522830,1234623593,176487719,289825898,834009677,2005728442,343256654,653716217,61489709,1069899106,1127401633]
theorem round_11_18 : poseidonInternalRound s_11_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_11_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_18
def s_11_19 : Fin 16 → Scalar := ![1507861251,218726667,1639580019,1766918442,1697324568,699962880,545232459,249778910,282476074,597579388,563541205,1216932775,1258500822,2117028589,475351262,910528382]
theorem round_11_19 : poseidonInternalRound s_11_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_11_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_19
def s_11_20 : Fin 16 → Scalar := ![255899804,1338155474,169684064,1241016377,1125715910,1842819930,796768272,995221062,699243750,200849721,1369002921,1215299277,451407543,1554241235,1512149974,1597826841]
theorem round_11_20 : poseidonFullRound s_11_19 (poseidonExternalFinal 0) = s_11_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_20
def s_11_21 : Fin 16 → Scalar := ![252343539,1802051217,1572716659,1446251816,226899372,57292114,558523474,865123573,699949037,1680823319,1166432139,1023217119,80106795,932764940,1864026167,429319588]
theorem round_11_21 : poseidonFullRound s_11_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_11_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_21
def s_11_22 : Fin 16 → Scalar := ![1509289012,706532421,1965532522,71418952,1143383283,72795806,1947987051,1898967668,1001232327,678634672,1782394127,1204508755,1970711541,877271806,1442064671,2045428500]
theorem round_11_22 : poseidonFullRound s_11_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_11_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_22
def s_11_23 : Fin 16 → Scalar := ![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062,1767302682,1596513829,914146389,1609029218,546124812,996118558,721351986,155303873]
theorem round_11_23 : poseidonFullRound s_11_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_11_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_11_23
theorem permutation_11 : poseidonPermutation s_11_0 = s_11_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_11_1,round_11_2,round_11_3,round_11_4,round_11_5,round_11_6,round_11_7,round_11_8,round_11_9,round_11_10,round_11_11,round_11_12,round_11_13,round_11_14,round_11_15,round_11_16,round_11_17,round_11_18,round_11_19,round_11_20,round_11_21,round_11_22,round_11_23]
#print axioms permutation_11
theorem parent_11 : nodeCompress (![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] : Fin 8 → Scalar) ![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] = ![986339640,660349625,1012157959,454024326,987656904,622864739,1150440730,1280042062] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_11_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_11]
  funext i
  fin_cases i <;> rfl
#print axioms parent_11
end R1Z.PV_RunJoin_RootModel
