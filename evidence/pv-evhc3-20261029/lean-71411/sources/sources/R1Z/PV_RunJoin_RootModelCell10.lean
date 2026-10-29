import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_10_0 : Fin 16 → Scalar := ![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885,1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,602005867]
def s_10_1 : Fin 16 → Scalar := ![903747434,340353022,845835829,597898017,1826772569,892162873,781308990,2091903213,903747434,340353022,845835829,597898017,775251551,1988125502,1921713230,2136344824]
theorem round_10_1 : poseidonExternalLinear s_10_0 = s_10_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_1
def s_10_2 : Fin 16 → Scalar := ![2099493825,299233703,749184267,453208885,52093435,374532031,116301475,1862867515,1776216198,830654040,257936156,1619566091,283813872,862537160,342765253,1261848172]
theorem round_10_2 : poseidonFullRound s_10_1 (poseidonExternalInitial 0) = s_10_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_2
def s_10_3 : Fin 16 → Scalar := ![1529807650,1105904788,363771608,555965292,1999782256,88135714,1036564469,1730114032,818072059,1903454923,46284999,1336807087,2048596651,942872670,2044559788,1009629225]
theorem round_10_3 : poseidonFullRound s_10_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_10_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_3
def s_10_4 : Fin 16 → Scalar := ![1103540591,505310261,1499914715,583071139,1661514224,1492530225,728315343,541454400,574333722,146818222,1847961045,598063744,729670271,2021450276,228547968,407396146]
theorem round_10_4 : poseidonFullRound s_10_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_10_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_4
def s_10_5 : Fin 16 → Scalar := ![861792774,1085700528,125853217,1005792593,1079229889,1236191702,1548488132,727280716,1316762764,985166782,802905133,1123307724,171827979,1466187471,2065215033,1996947873]
theorem round_10_5 : poseidonFullRound s_10_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_10_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_5
def s_10_6 : Fin 16 → Scalar := ![1644423387,702737508,2016227061,1492723705,1808425151,68751389,1924016970,1065846217,658946306,564146473,1453140018,775502610,630052163,2027970149,1078554060,1791910081]
theorem round_10_6 : poseidonInternalRound s_10_5 (poseidonInternalConstants 0) = s_10_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_6
def s_10_7 : Fin 16 → Scalar := ![2127502443,333396435,1515629402,1306586453,1213158253,730681151,1069659851,1272823758,223923862,170751666,1587353635,2108519221,614774482,26593759,551718328,1253974795]
theorem round_10_7 : poseidonInternalRound s_10_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_10_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_7
def s_10_8 : Fin 16 → Scalar := ![1411972168,1110710605,1661089327,1708692688,1892645606,1730794351,646691050,633656096,1522281095,1540067726,582315631,92815152,1160718499,550281285,1966145628,1365275894]
theorem round_10_8 : poseidonInternalRound s_10_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_10_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_8
def s_10_9 : Fin 16 → Scalar := ![632337443,299512429,363496831,1728605282,1445064790,1111707676,555562601,1088086322,767253754,456632279,627037749,1402542544,884640363,2008508805,1339330128,1151122400]
theorem round_10_9 : poseidonInternalRound s_10_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_10_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_9
def s_10_10 : Fin 16 → Scalar := ![1510589877,1329843047,1757324280,1502300805,1853430703,1637784258,1628464674,1948378522,454563368,1964077104,1019375141,1325835117,246875689,399185110,76671183,2034901555]
theorem round_10_10 : poseidonInternalRound s_10_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_10_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_10
def s_10_11 : Fin 16 → Scalar := ![1174099761,2006542399,2043864265,243451631,471759447,1111443716,1247961392,818873234,878751987,969264578,839791294,311195321,152748166,1837836477,482156906,1250529132]
theorem round_10_11 : poseidonInternalRound s_10_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_10_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_11
def s_10_12 : Fin 16 → Scalar := ![1629999432,1791595446,1725297930,758859571,1411644976,388283327,1065111945,653332495,596157739,956165610,737879303,983285192,1262546365,1029677628,65357876,43827338]
theorem round_10_12 : poseidonInternalRound s_10_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_10_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_12
def s_10_13 : Fin 16 → Scalar := ![440796528,371556989,2030557403,1615399827,1283186763,497527481,451289078,1738535577,1873708137,692705592,401607718,1731753497,1226023318,334171510,1333129899,1810232319]
theorem round_10_13 : poseidonInternalRound s_10_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_10_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_13
def s_10_14 : Fin 16 → Scalar := ![837252897,2104819603,1499410126,1752410981,1261338483,1103767722,1142127581,1330389898,1049735686,824751465,662705622,1857100285,1535266651,715982604,1621445772,1531925730]
theorem round_10_14 : poseidonInternalRound s_10_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_10_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_14
def s_10_15 : Fin 16 → Scalar := ![1369635802,2066834573,813351575,529207953,1462788246,442429346,2875563,1355106209,1184196664,644992604,2115223093,257704656,1202183130,1065318992,604161439,1386159000]
theorem round_10_15 : poseidonInternalRound s_10_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_10_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_15
def s_10_16 : Fin 16 → Scalar := ![1736860091,530269510,90138087,580266749,1575806317,1247337179,702936600,1438370080,1864236286,372784389,1935849640,1754718883,535114402,50200696,121210043,1073907190]
theorem round_10_16 : poseidonInternalRound s_10_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_10_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_16
def s_10_17 : Fin 16 → Scalar := ![2134970349,371787499,21794163,15101338,1710550290,471560030,860652719,1702889935,93077780,785041105,24143168,1689779895,484575646,1990968099,954943710,2089042345]
theorem round_10_17 : poseidonInternalRound s_10_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_10_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_17
def s_10_18 : Fin 16 → Scalar := ![1396877766,1884405060,1556205887,1573022913,164634352,467643453,1136217158,975907404,541671519,619677623,465417829,1511273200,459046290,1257353647,2123886404,466792290]
theorem round_10_18 : poseidonInternalRound s_10_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_10_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_18
def s_10_19 : Fin 16 → Scalar := ![865570689,1360373371,440896438,1473092669,793043127,515812618,1475179015,1804500051,90446039,1347133568,1469939220,603124857,1886793741,1294978735,1483106254,270934236]
theorem round_10_19 : poseidonInternalRound s_10_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_10_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_19
def s_10_20 : Fin 16 → Scalar := ![1336895488,1486572832,1582235080,614869653,104554619,1689361250,252839300,449567371,156808675,1562295011,1404832575,1664591538,1698922374,611760343,450404074,1401072937]
theorem round_10_20 : poseidonFullRound s_10_19 (poseidonExternalFinal 0) = s_10_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_20
def s_10_21 : Fin 16 → Scalar := ![1049118472,1694560882,1534939373,127490465,2038011366,1110007244,1105228491,2130322159,1123237954,565717303,1581744654,1270037770,617284261,1849660927,131488981,1139478408]
theorem round_10_21 : poseidonFullRound s_10_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_10_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_21
def s_10_22 : Fin 16 → Scalar := ![1186909424,1532808108,324362564,489687238,1171868342,423967985,1823517007,1144809756,538400262,207976767,455061992,472119423,1693843129,1968101912,940609793,1334258947]
theorem round_10_22 : poseidonFullRound s_10_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_10_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_22
def s_10_23 : Fin 16 → Scalar := ![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893,1923711662,1019313825,943839838,94009761,461843349,1438753389,2033324062,1977314929]
theorem round_10_23 : poseidonFullRound s_10_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_10_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_10_23
theorem permutation_10 : poseidonPermutation s_10_0 = s_10_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_10_1,round_10_2,round_10_3,round_10_4,round_10_5,round_10_6,round_10_7,round_10_8,round_10_9,round_10_10,round_10_11,round_10_12,round_10_13,round_10_14,round_10_15,round_10_16,round_10_17,round_10_18,round_10_19,round_10_20,round_10_21,round_10_22,round_10_23]
#print axioms permutation_10
theorem parent_10 : nodeCompress (![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] : Fin 8 → Scalar) ![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] = ![418360492,472096212,871749117,98906847,2026788776,1504737042,407274798,1800828893] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1972918328,1234090299,977162835,1704494754,1617603773,1819200880,906453206,1653526885] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_10_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_10]
  funext i
  fin_cases i <;> rfl
#print axioms parent_10
end R1Z.PV_RunJoin_RootModel
