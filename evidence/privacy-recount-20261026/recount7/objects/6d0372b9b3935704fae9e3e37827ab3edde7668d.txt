import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_0_3 : Fin 16 → Scalar := ![766202219,1081169595,1843633031,2048382017,654206071,1804362387,257782029,1832068769,141479547,1882254112,155897196,252399390,158580274,247688298,932959007,1468901607]
theorem round_0_3 : poseidonFullRound s_0_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_0_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_3
def s_0_4 : Fin 16 → Scalar := ![666925069,987260987,1637246404,614747765,692738572,1556102299,1520653625,124988329,1635620420,1617081311,1486641598,168843298,627518752,1403237301,632466905,1262750119]
theorem round_0_4 : poseidonFullRound s_0_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_0_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_4
def s_0_5 : Fin 16 → Scalar := ![885961593,453156181,1829377102,686396561,1004576258,597896903,998301172,549287367,299839417,759346042,1790826613,1468256415,1148501286,1154027811,1955760242,1390874036]
theorem round_0_5 : poseidonFullRound s_0_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_0_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_5
def s_0_6 : Fin 16 → Scalar := ![896782363,1664449572,575080301,1809395988,657968867,40225604,944676190,2005946527,936033121,182868266,1066710565,87873984,1607970796,209436980,208425826,1441236125]
theorem round_0_6 : poseidonInternalRound s_0_5 (poseidonInternalConstants 0) = s_0_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_6
def s_0_7 : Fin 16 → Scalar := ![2111753197,659490035,145201065,1937657121,2111307752,1786133774,1307391132,674083018,695679366,712159972,384966347,297109878,974594244,879136524,1841993018,1219966109]
theorem round_0_7 : poseidonInternalRound s_0_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_0_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_7
def s_0_8 : Fin 16 → Scalar := ![1251425744,597031943,227944038,1245719451,1795618395,598394881,971868839,129182120,937671229,1861868392,1153573835,1423857994,1616872857,537530695,1189373150,820283522]
theorem round_0_8 : poseidonInternalRound s_0_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_0_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_8
def s_0_9 : Fin 16 → Scalar := ![1978515731,914811483,773667616,1005690050,1797824818,1302163048,1352811330,2142984279,80612620,214718258,461380730,2022021359,61089388,390250073,1163932984,460541981]
theorem round_0_9 : poseidonInternalRound s_0_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_0_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_9
def s_0_10 : Fin 16 → Scalar := ![2146894872,1287112881,1919636630,100094304,1869998060,1879557343,712591018,84341846,2100782170,1653084271,379766578,1874845030,452878143,1170680311,818750390,1716393276]
theorem round_0_10 : poseidonInternalRound s_0_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_0_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_10
def s_0_11 : Fin 16 → Scalar := ![324429834,496485550,901162282,1757233532,1284455267,1365002746,537448775,312283519,1821518201,1492151233,1543292081,1320577524,482861756,459136736,1656433865,1713162392]
theorem round_0_11 : poseidonInternalRound s_0_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_0_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_11
def s_0_12 : Fin 16 → Scalar := ![614557056,1956084707,1114440074,2046082344,997823058,1824806623,1478090781,2118391550,538211362,1198225639,1242725909,1033830668,1398226535,1320666340,1835309552,530088815]
theorem round_0_12 : poseidonInternalRound s_0_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_0_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_12
def s_0_13 : Fin 16 → Scalar := ![1435677265,984226063,1257021504,770019791,568274879,307759913,1229889761,1461214442,1347202635,831227066,269153148,908289247,769626625,927712391,319490704,1233247324]
theorem round_0_13 : poseidonInternalRound s_0_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_0_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_13
def s_0_14 : Fin 16 → Scalar := ![270355765,1312777520,695110818,1261146974,579783195,957742771,1030318163,1504478924,971796977,521799300,1063468193,1239630565,97875865,79112135,417161004,1878122276]
theorem round_0_14 : poseidonInternalRound s_0_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_0_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_14
def s_0_15 : Fin 16 → Scalar := ![1018608862,1745014254,1822458370,1181857336,775535000,723735541,1190163245,82123755,268198264,868871420,649457337,1307689466,1219922483,1672817433,1230602651,2028488865]
theorem round_0_15 : poseidonInternalRound s_0_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_0_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_15
def s_0_16 : Fin 16 → Scalar := ![1926941293,1139689096,892107935,1974620539,1303987548,237025263,972676683,355627868,1511797929,634942721,866541007,2013995607,758246087,649194100,481903091,613247594]
theorem round_0_16 : poseidonInternalRound s_0_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_0_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_16
def s_0_17 : Fin 16 → Scalar := ![195069709,1838538112,335581239,7396584,393331165,196285930,1759731814,1984196098,935455698,35428420,1126093973,1540167161,1728086596,608479825,1252078513,336715795]
theorem round_0_17 : poseidonInternalRound s_0_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_0_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_17
def s_0_18 : Fin 16 → Scalar := ![557538377,1518846170,351470536,1857378041,679473731,673399291,157151284,2114806804,1307036817,160048990,1749301618,1045528275,2100985113,394671484,113946107,1292176253]
theorem round_0_18 : poseidonInternalRound s_0_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_0_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_18
def s_0_19 : Fin 16 → Scalar := ![993638361,1492877779,676972681,961092832,1114854163,11002030,707905403,30197304,1918503366,144383756,257526843,375453891,1310130247,198364348,1433487299,166812419]
theorem round_0_19 : poseidonInternalRound s_0_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_0_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_19
def s_0_20 : Fin 16 → Scalar := ![1073918736,2088267327,112220100,2029493901,1875531519,1622876291,837344668,26815995,338495996,1857834165,1926021000,2067852105,1552880848,1071569240,1427066814,1775824475]
theorem round_0_20 : poseidonFullRound s_0_19 (poseidonExternalFinal 0) = s_0_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_20
def s_0_21 : Fin 16 → Scalar := ![128564185,1889940543,985955432,207892749,98619379,1396065120,1274820848,1397324072,1064109717,280064952,877920100,1726986149,282763802,1936930308,1382777985,1447845885]
theorem round_0_21 : poseidonFullRound s_0_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_0_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_21
def s_0_22 : Fin 16 → Scalar := ![1476165313,563400266,1005787277,387127822,1596011738,653047749,945141618,1191536560,337548802,758168117,1199373023,1348772429,2008467229,868758893,1170276244,875913466]
theorem round_0_22 : poseidonFullRound s_0_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_0_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_22
def s_0_23 : Fin 16 → Scalar := ![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732,1152710031,569266410,368632835,1274898005,1168032720,2145939158,133089905,1183031990]
theorem round_0_23 : poseidonFullRound s_0_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_0_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_0_23
theorem permutation_0 : poseidonPermutation s_0_0 = s_0_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_0_1,round_0_2,round_0_3,round_0_4,round_0_5,round_0_6,round_0_7,round_0_8,round_0_9,round_0_10,round_0_11,round_0_12,round_0_13,round_0_14,round_0_15,round_0_16,round_0_17,round_0_18,round_0_19,round_0_20,round_0_21,round_0_22,round_0_23]
#print axioms permutation_0
theorem parent_0 : nodeCompress (![0,0,0,0,0,0,0,0] : Fin 8 → Scalar) ![0,0,0,0,0,0,0,0] = ![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![0,0,0,0,0,0,0,0] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![0,0,0,0,0,0,0,0] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![0,0,0,0,0,0,0,0] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_0_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_0]
  funext i
  fin_cases i <;> rfl
#print axioms parent_0
end R1Z.PV_RunJoin_RootModel
