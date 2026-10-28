import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_20_0 : Fin 16 → Scalar := ![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443,19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,1761530072]
def s_20_1 : Fin 16 → Scalar := ![1909473011,767736449,1900694375,1090579689,1323682567,1672060784,584954186,1636656964,1909473011,767736449,1900694375,1090579689,272161549,620539766,1725358426,1681098575]
theorem round_20_1 : poseidonExternalLinear s_20_0 = s_20_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_1
def s_20_2 : Fin 16 → Scalar := ![145281165,525042681,630513376,1645715604,1596637376,207650206,1521958776,533648992,1939540689,1171068224,1291596990,2057600774,2048768871,1104488157,120081069,1489086820]
theorem round_20_2 : poseidonFullRound s_20_1 (poseidonExternalInitial 0) = s_20_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_2
def s_20_3 : Fin 16 → Scalar := ![1968662204,1379747744,92341296,1959271734,442810556,1887637537,940613103,1974815932,1210069471,1021739738,1334900648,1407145993,341203931,1747198198,1600557861,718574512]
theorem round_20_3 : poseidonFullRound s_20_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_20_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_3
def s_20_4 : Fin 16 → Scalar := ![87762724,461052534,26717533,1725428805,1416357249,1535528658,720306399,1499567172,637567218,1475550577,993867248,746933553,1051776989,447734528,780856092,1910804522]
theorem round_20_4 : poseidonFullRound s_20_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_20_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_4
def s_20_5 : Fin 16 → Scalar := ![1748175761,174171119,955635292,696563049,1562617716,1904956911,469039257,306672175,1006139126,1690427874,493509598,257703474,589817818,2128765406,350669887,433020629]
theorem round_20_5 : poseidonFullRound s_20_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_20_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_5
def s_20_6 : Fin 16 → Scalar := ![32785322,411000695,616513,875598125,2000353069,651369094,213700271,536495953,173618884,1342152273,932000883,1375788403,186188882,647330553,1950175342,1827860262]
theorem round_20_6 : poseidonInternalRound s_20_5 (poseidonInternalConstants 0) = s_20_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_6
def s_20_7 : Fin 16 → Scalar := ![652169990,237525345,1975241323,1181433503,796963673,1658495566,222482381,1950010937,574905332,1967606665,712689574,58733610,372456624,1416056116,501247527,1691341775]
theorem round_20_7 : poseidonInternalRound s_20_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_20_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_7
def s_20_8 : Fin 16 → Scalar := ![345560126,461574063,2027047717,654815436,157307161,990174010,901033969,470697160,797487216,1420181560,2021216161,278746814,1961933786,1621614721,1148081198,1630175213]
theorem round_20_8 : poseidonInternalRound s_20_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_20_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_8
def s_20_9 : Fin 16 → Scalar := ![579526749,753964979,51519056,764169013,1550848204,1102789547,1208190513,352238098,1439023155,934133933,1990987719,1725524503,686351680,160299096,998558834,291195481]
theorem round_20_9 : poseidonInternalRound s_20_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_20_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_9
def s_20_10 : Fin 16 → Scalar := ![657841177,198424013,1694980793,353651439,1113826431,2056706257,1599333451,512860836,1103312879,212061065,253902287,1971624692,2072717395,1559831264,1159485854,691814608]
theorem round_20_10 : poseidonInternalRound s_20_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_20_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_10
def s_20_11 : Fin 16 → Scalar := ![1099538868,2143180615,1039750894,1211878711,117949815,492318362,1583819506,408111754,1434884412,397814420,2095177203,1033498667,1492459613,1017303031,549054103,884667379]
theorem round_20_11 : poseidonInternalRound s_20_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_20_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_11
def s_20_12 : Fin 16 → Scalar := ![1593798883,140863997,77185170,697714579,1088765549,1579809880,1435267340,494515521,1274261770,1053927140,270459548,665438824,749914354,1017442566,2079503214,2090499114]
theorem round_20_12 : poseidonInternalRound s_20_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_20_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_12
def s_20_13 : Fin 16 → Scalar := ![1183165028,471548690,485055033,974059362,450874497,1985322656,1162082986,1914906979,227434081,1700576658,255871382,811359754,1825842241,1341618023,1835881735,266392138]
theorem round_20_13 : poseidonInternalRound s_20_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_20_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_13
def s_20_14 : Fin 16 → Scalar := ![1771997632,52432430,550993806,1329637541,1040396069,1281275178,260317293,1875846164,775158697,1136811494,1747657621,753234215,1804404304,1155445527,294172809,961473245]
theorem round_20_14 : poseidonInternalRound s_20_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_20_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_14
def s_20_15 : Fin 16 → Scalar := ![633513885,1540143920,442215455,363810713,1220945454,513277868,1227930278,1282781754,1923776944,453677962,87753796,801055391,2037827557,91393906,888225419,1133125536]
theorem round_20_15 : poseidonInternalRound s_20_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_20_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_15
def s_20_16 : Fin 16 → Scalar := ![69240335,1569500080,913787070,1484599012,1206985204,1799351107,668419410,523009830,1459669234,206797494,1842413737,1944708727,1522314973,631010105,554018161,559970196]
theorem round_20_16 : poseidonInternalRound s_20_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_20_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_16
def s_20_17 : Fin 16 → Scalar := ![665530756,317339652,575413712,391268326,1961270263,1767653520,809907869,8213987,901907882,148390508,2036347841,1405422288,1262043906,1378606881,135671129,754044692]
theorem round_20_17 : poseidonInternalRound s_20_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_20_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_17
def s_20_18 : Fin 16 → Scalar := ![26182713,80874440,914362212,1328608092,421311363,128703697,2058266479,289229956,1391110393,1244282837,1924586382,1117052476,440936082,1773157593,143940570,1090268583]
theorem round_20_18 : poseidonInternalRound s_20_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_20_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_18
def s_20_19 : Fin 16 → Scalar := ![970593846,2033859140,1634225477,824966127,1028508310,1864760205,1245518971,1136349061,1773972303,514327569,1339451922,1112274639,2033874190,60728149,576010001,571453557]
theorem round_20_19 : poseidonInternalRound s_20_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_20_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_19
def s_20_20 : Fin 16 → Scalar := ![476732007,516663268,476588846,938696859,921569121,1883026417,855114554,1701389294,2096507207,564374615,1312927672,907141454,1853671563,1914153053,1363862144,557069256]
theorem round_20_20 : poseidonFullRound s_20_19 (poseidonExternalFinal 0) = s_20_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_20
def s_20_21 : Fin 16 → Scalar := ![1980273964,306712572,598600599,2129045560,1877578113,1104451763,1986536328,289017713,2084118500,736436695,35546553,696847060,11817402,1783572131,687642011,1632391076]
theorem round_20_21 : poseidonFullRound s_20_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_20_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_21
def s_20_22 : Fin 16 → Scalar := ![2024014724,2140653237,705792481,1449448367,1998363057,456865669,71344270,759229891,1382571335,1985731344,218607655,1856455316,379028637,911109148,146749109,150410319]
theorem round_20_22 : poseidonFullRound s_20_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_20_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_22
def s_20_23 : Fin 16 → Scalar := ![1201428963,1296676114,441891487,1910121140,602621674,1294160489,1878016864,855887413,2003237147,937653028,699104113,1908338402,1737209887,1668348770,846406468,96331821]
theorem round_20_23 : poseidonFullRound s_20_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_20_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_20_23
theorem permutation_20 : poseidonPermutation s_20_0 = s_20_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_20_1,round_20_2,round_20_3,round_20_4,round_20_5,round_20_6,round_20_7,round_20_8,round_20_9,round_20_10,round_20_11,round_20_12,round_20_13,round_20_14,round_20_15,round_20_16,round_20_17,round_20_18,round_20_19,round_20_20,round_20_21,round_20_22,round_20_23]
#print axioms permutation_20
theorem parent_20 : nodeCompress (![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] : Fin 8 → Scalar) ![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] = ![1201428963,1296676114,441891487,1910121140,602621674,1294160489,1878016864,855887413] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![19381883,1308966873,251977766,474343397,2069732268,1863820229,152153379,665567443] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_20_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_20]
  funext i
  fin_cases i <;> rfl
#print axioms parent_20
end R1Z.PV_RunJoin_RootModel
