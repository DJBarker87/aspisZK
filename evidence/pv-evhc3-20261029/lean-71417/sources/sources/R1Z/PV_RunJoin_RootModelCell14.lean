import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_14_0 : Fin 16 → Scalar := ![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542,260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,2054173171]
def s_14_1 : Fin 16 → Scalar := ![1588527388,539460996,46492311,1657280303,1768978572,658354508,1809718655,1584479657,1588527388,539460996,46492311,1657280303,717457554,1754317137,802639248,1628921268]
theorem round_14_1 : poseidonExternalLinear s_14_0 = s_14_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_1
def s_14_2 : Fin 16 → Scalar := ![688713879,610540972,860014350,851527525,1488646720,266926542,1427207477,1104892128,210839498,394997671,1531649834,257799174,481626886,719391106,1913419864,450458930]
theorem round_14_2 : poseidonFullRound s_14_1 (poseidonExternalInitial 0) = s_14_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_2
def s_14_3 : Fin 16 → Scalar := ![2009931017,175420184,1381387698,1932462373,686936826,1780654066,1112644644,2054202304,1915130919,1576660032,294511301,1757095870,392631525,228004788,58800387,36395847]
theorem round_14_3 : poseidonFullRound s_14_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_14_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_3
def s_14_4 : Fin 16 → Scalar := ![1479033962,1628641104,471716052,203762283,1132899260,429608124,1315374514,1287555520,983635878,1665205549,1495427634,630589487,1422132261,1954885402,1803002651,1068468825]
theorem round_14_4 : poseidonFullRound s_14_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_14_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_4
def s_14_5 : Fin 16 → Scalar := ![1484723558,1458339336,698540680,1613026699,535850289,721731869,185604409,1128484841,1853653197,1843279718,1091980934,1734702251,606167517,1681817610,1239284128,1104260489]
theorem round_14_5 : poseidonFullRound s_14_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_14_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_5
def s_14_6 : Fin 16 → Scalar := ![699656347,1392392571,1331134595,2091192737,2073371900,744344904,1578427029,1290122708,978461281,1514742350,1431033211,1398569055,676160635,471100818,2028078416,698040086]
theorem round_14_6 : poseidonInternalRound s_14_5 (poseidonInternalConstants 0) = s_14_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_6
def s_14_7 : Fin 16 → Scalar := ![1550356186,581675331,1851551950,1111602767,743872431,361382989,306823807,152757486,2025758849,416267900,2130927217,389245491,2084362714,1796341201,1381361833,247710462]
theorem round_14_7 : poseidonInternalRound s_14_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_14_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_7
def s_14_8 : Fin 16 → Scalar := ![606650514,1073538615,2047483537,643307058,391791,1979023814,1720290520,1678407800,2090958316,1829746981,717948140,1408528346,948739075,482718333,296095562,1615813243]
theorem round_14_8 : poseidonInternalRound s_14_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_14_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_8
def s_14_9 : Fin 16 → Scalar := ![550140529,1082158349,1956103161,434364319,11754062,1608229700,1370825199,52536584,1363311954,272411824,748107820,1199649108,335803641,1830999352,136878204,1526679412]
theorem round_14_9 : poseidonInternalRound s_14_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_14_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_9
def s_14_10 : Fin 16 → Scalar := ![1029550914,2142429049,677509728,650244329,1154303196,1022142136,1977004128,127644782,1618025405,2078220940,471016401,1380432732,1037145965,1954588925,191920789,111618155]
theorem round_14_10 : poseidonInternalRound s_14_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_14_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_10
def s_14_11 : Fin 16 → Scalar := ![31300860,939883157,152473564,1398431424,1589428735,119342755,1932044088,524269215,1893759483,393553939,81911804,872965476,1799375503,1653740891,1973233291,1623042153]
theorem round_14_11 : poseidonInternalRound s_14_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_14_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_11
def s_14_12 : Fin 16 → Scalar := ![136172008,338883753,1851431371,697758998,1377012241,1308484676,1094869296,739975651,1282045956,1364561218,1672309306,1652801684,1702851811,1636068188,1869836208,77020047]
theorem round_14_12 : poseidonInternalRound s_14_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_14_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_12
def s_14_13 : Fin 16 → Scalar := ![2006291223,1304674986,373686681,1609343578,1244470926,426709579,1641870353,1079592663,1858916429,253628580,1866053918,1973033553,674056033,1416101571,1902722420,1965020975]
theorem round_14_13 : poseidonInternalRound s_14_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_14_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_13
def s_14_14 : Fin 16 → Scalar := ![859594917,970138913,412837289,1807870945,1031296747,50366250,665707695,39917655,1383565669,169870997,1391713776,229933354,352029826,1807764650,180999136,1128221878]
theorem round_14_14 : poseidonInternalRound s_14_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_14_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_14
def s_14_15 : Fin 16 → Scalar := ![221603697,370684659,226220324,189578585,1208468781,206405746,1375839163,1955275666,403292324,2085331685,733794409,609726344,1305826064,1869595569,1177884827,687576144]
theorem round_14_15 : poseidonInternalRound s_14_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_14_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_15
def s_14_16 : Fin 16 → Scalar := ![548285793,716112035,797868024,1103741716,1423243036,1500435665,1422607652,929018474,427237320,1614394280,131625742,261050939,1056497957,92489064,551850981,686235559]
theorem round_14_16 : poseidonInternalRound s_14_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_14_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_16
def s_14_17 : Fin 16 → Scalar := ![1253101731,1269507075,1647441,673394610,1201921093,938045563,979683317,2028518907,1552680825,1521470496,46685087,371184978,1025561374,1918248481,1794032708,1084454190]
theorem round_14_17 : poseidonInternalRound s_14_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_14_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_17
def s_14_18 : Fin 16 → Scalar := ![1862937987,8386673,889658127,1432458038,1911797401,862706724,23974684,1862554473,2061013321,1688270114,1447252099,841611057,1329111989,1046302104,385302364,704861620]
theorem round_14_18 : poseidonInternalRound s_14_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_14_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_18
def s_14_19 : Fin 16 → Scalar := ![811809363,2122327828,1745773762,1401322366,228451187,884863210,733647396,1058343195,1783157662,519393645,188890454,494093545,309781106,1365659090,497960347,1404338858]
theorem round_14_19 : poseidonInternalRound s_14_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_14_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_19
def s_14_20 : Fin 16 → Scalar := ![1389796862,138631385,1292535919,548443527,1248747468,1423486552,469094253,987655658,770829828,753751445,386407563,849173562,432188614,1118884666,290001393,430367556]
theorem round_14_20 : poseidonFullRound s_14_19 (poseidonExternalFinal 0) = s_14_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_20
def s_14_21 : Fin 16 → Scalar := ![749669964,1737941286,1434265574,1522009473,197930648,236094865,206480739,2134249322,2036494666,1091697210,958611580,55248282,198274437,1124027003,1670690975,1163505393]
theorem round_14_21 : poseidonFullRound s_14_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_14_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_21
def s_14_22 : Fin 16 → Scalar := ![107689901,1948178487,1420599561,320959960,806800265,204979889,81780544,200899343,371173369,519323237,1780432811,1389167264,306780181,1439171784,1590442838,162939107]
theorem round_14_22 : poseidonFullRound s_14_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_14_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_22
def s_14_23 : Fin 16 → Scalar := ![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983,1163707329,860673780,809238374,362497474,215881670,846450144,1155460819,110771748]
theorem round_14_23 : poseidonFullRound s_14_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_14_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_14_23
theorem permutation_14 : poseidonPermutation s_14_0 = s_14_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_14_1,round_14_2,round_14_3,round_14_4,round_14_5,round_14_6,round_14_7,round_14_8,round_14_9,round_14_10,round_14_11,round_14_12,round_14_13,round_14_14,round_14_15,round_14_16,round_14_17,round_14_18,round_14_19,round_14_20,round_14_21,round_14_22,round_14_23]
#print axioms permutation_14
theorem parent_14 : nodeCompress (![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] : Fin 8 → Scalar) ![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] = ![1239966481,992485427,1397515674,466658549,2071909237,712995354,2047452742,1680224983] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![260546973,1375125357,1584234519,1097072342,1685367984,1070989054,2113798037,958210542] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_14_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_14]
  funext i
  fin_cases i <;> rfl
#print axioms parent_14
end R1Z.PV_RunJoin_RootModel
