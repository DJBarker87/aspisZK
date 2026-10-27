import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_17_0 : Fin 16 → Scalar := ![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353,1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,1031854335]
def s_17_1 : Fin 16 → Scalar := ![1729087289,2028263865,2086453025,62650886,1622102076,1832560026,2010657391,876431576,1729087289,2028263865,2086453025,62650886,570581058,781039008,1003577984,920873187]
theorem round_17_1 : poseidonExternalLinear s_17_0 = s_17_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_1
def s_17_2 : Fin 16 → Scalar := ![438342425,1194559965,1367801716,658591158,1444428093,1375333105,1779766922,1213091938,581920200,195601401,411530993,2084838710,807738355,975224918,2048983488,1176255157]
theorem round_17_2 : poseidonFullRound s_17_1 (poseidonExternalInitial 0) = s_17_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_2
def s_17_3 : Fin 16 → Scalar := ![38237614,181286302,371360728,1569986986,1505663385,697573901,1026532293,414386774,1140439966,160506251,1210132276,471946150,263175756,1603279674,229115372,686002436]
theorem round_17_3 : poseidonFullRound s_17_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_17_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_3
def s_17_4 : Fin 16 → Scalar := ![1325489704,94763014,608683038,295449477,332408702,698129973,1398558809,1011725953,1851708715,1810659152,808494174,83679305,1034278005,885927531,173769903,196119260]
theorem round_17_4 : poseidonFullRound s_17_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_17_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_4
def s_17_5 : Fin 16 → Scalar := ![191804885,314507941,901801704,1697206463,980993830,1431444014,37986337,1472525616,1918047447,370850605,673875484,1236831678,1345310248,300452909,1622905714,8613770]
theorem round_17_5 : poseidonFullRound s_17_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_17_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_5
def s_17_6 : Fin 16 → Scalar := ![1098854126,2072557571,1414169391,2104424541,1016065682,1038833737,826128767,1510408586,307503441,59040395,316810912,1906679445,1653524842,198508115,847451674,1481881189]
theorem round_17_6 : poseidonInternalRound s_17_5 (poseidonInternalConstants 0) = s_17_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_6
def s_17_7 : Fin 16 → Scalar := ![1934686266,1433593176,41890740,1336282828,1047110120,949989868,27352385,1537904641,66770407,1590474843,1652862443,869501833,857179640,427750207,1693933527,273669628]
theorem round_17_7 : poseidonInternalRound s_17_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_17_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_7
def s_17_8 : Fin 16 → Scalar := ![1181495005,2094826979,745015283,1711397821,448180175,828686162,1536510123,302883065,617911311,1948384328,975261599,1612855045,405318993,1681485130,1465222530,90554667]
theorem round_17_8 : poseidonInternalRound s_17_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_17_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_8
def s_17_9 : Fin 16 → Scalar := ![1338145328,1473413368,868616955,1929210379,816544142,1900146746,1302270091,1583233373,1161822905,2096251900,1614051557,2120636184,1889542430,910732593,498553450,471926240]
theorem round_17_9 : poseidonInternalRound s_17_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_17_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_9
def s_17_10 : Fin 16 → Scalar := ![1617118888,328009813,591830355,128987020,1091982287,1339656970,1872533711,1397284555,1539040289,771654742,228466270,556537641,1071539076,1728504448,1693426963,1100660638]
theorem round_17_10 : poseidonInternalRound s_17_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_17_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_10
def s_17_11 : Fin 16 → Scalar := ![994933063,148535248,1004186145,336473515,2113932790,1927684132,1759545718,1199907428,1396670550,1943127510,1841752039,918553504,1102970738,770548478,1205294186,887878320]
theorem round_17_11 : poseidonInternalRound s_17_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_17_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_11
def s_17_12 : Fin 16 → Scalar := ![617863277,137570574,1997407616,1334929386,1868112117,767210380,459923480,1621183073,521723025,1360955429,452481196,2140321813,1061618093,1746421812,697170197,1913199381]
theorem round_17_12 : poseidonInternalRound s_17_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_17_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_12
def s_17_13 : Fin 16 → Scalar := ![1388662279,549625087,111902451,1456804763,324565920,1950002358,97220344,1088556129,620608656,924293523,2043815112,1141953507,2026185666,714909693,354033023,866473987]
theorem round_17_13 : poseidonInternalRound s_17_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_17_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_13
def s_17_14 : Fin 16 → Scalar := ![1952323586,1369398175,1043577990,204541199,1268816801,1955039758,1783340449,1767888640,800786117,1215713806,2037375598,1041954594,1431641297,1524372462,1067209658,148907499]
theorem round_17_14 : poseidonInternalRound s_17_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_17_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_14
def s_17_15 : Fin 16 → Scalar := ![1278558676,904745586,1622503391,353512207,1095947231,751212481,767666957,1011070727,1104238978,1520436579,601338526,331357846,132656168,1766433856,237713007,171509907]
theorem round_17_15 : poseidonInternalRound s_17_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_17_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_15
def s_17_16 : Fin 16 → Scalar := ![1249534193,777578170,970355719,1286881412,50475844,1154814045,815855091,156849702,1628984713,410056701,1463160166,2052388543,2112919105,1635502316,329458291,16689338]
theorem round_17_16 : poseidonInternalRound s_17_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_17_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_16
def s_17_17 : Fin 16 → Scalar := ![859066505,1725162566,740812187,1800142750,1351391148,97256293,1285143544,248547089,1151713901,695401149,280008774,132578519,1262697736,716582474,1236570415,1630863241]
theorem round_17_17 : poseidonInternalRound s_17_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_17_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_17
def s_17_18 : Fin 16 → Scalar := ![1149437428,1368181299,1124643107,401138792,1864213329,1199119421,2112906495,517646900,1033510065,1572053823,756678258,1518753513,1381628093,1984658247,860925857,1782753366]
theorem round_17_18 : poseidonInternalRound s_17_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_17_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_18
def s_17_19 : Fin 16 → Scalar := ![887838932,783257851,1664362766,1019631720,1443881302,1421118112,456091335,332223447,707862405,281413251,1159499824,1116824088,473594718,1005896173,888371736,91855693]
theorem round_17_19 : poseidonInternalRound s_17_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_17_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_19
def s_17_20 : Fin 16 → Scalar := ![1209605198,193543752,2140162667,1376354088,1194664132,675748361,1889937924,1621350460,2066086874,2097852063,1529291172,1583628455,931015980,19650706,1831945044,966037865]
theorem round_17_20 : poseidonFullRound s_17_19 (poseidonExternalFinal 0) = s_17_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_20
def s_17_21 : Fin 16 → Scalar := ![81206419,1627682472,324669969,257220879,852541448,1700114561,909867278,633137862,742216395,2005159925,494891363,2087567853,843013203,1475522482,290440240,530140493]
theorem round_17_21 : poseidonFullRound s_17_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_17_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_21
def s_17_22 : Fin 16 → Scalar := ![596721939,354232988,1496628398,60951958,2102643261,604335015,576931074,1996002699,359689657,1817512733,1486255727,1987462754,1835381913,484385698,498103750,932675518]
theorem round_17_22 : poseidonFullRound s_17_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_17_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_22
def s_17_23 : Fin 16 → Scalar := ![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413,940607860,1487999279,1516483323,36656590,377269885,2055582084,1089518766,364156294]
theorem round_17_23 : poseidonFullRound s_17_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_17_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_17_23
theorem permutation_17 : poseidonPermutation s_17_0 = s_17_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_17_1,round_17_2,round_17_3,round_17_4,round_17_5,round_17_6,round_17_7,round_17_8,round_17_9,round_17_10,round_17_11,round_17_12,round_17_13,round_17_14,round_17_15,round_17_16,round_17_17,round_17_18,round_17_19,round_17_20,round_17_21,round_17_22,round_17_23]
#print axioms permutation_17
theorem parent_17 : nodeCompress (![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] : Fin 8 → Scalar) ![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] = ![1321679286,782621548,1415820264,74436574,776350425,323154748,429051705,1299980413] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1127845264,662862400,84021756,995080286,1419670571,1966281459,837284626,2083375353] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_17_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_17]
  funext i
  fin_cases i <;> rfl
#print axioms parent_17
end R1Z.PV_RunJoin_RootModel
