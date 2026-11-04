import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_2_0 : Fin 16 → Scalar := ![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536,141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,2134309165]
def s_2_1 : Fin 16 → Scalar := ![262987472,1121802865,1963379150,205175330,359459393,852505493,522680038,676125417,262987472,1121802865,1963379150,205175330,1455422022,1948468122,1663084278,720567028]
theorem round_2_1 : poseidonExternalLinear s_2_0 = s_2_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_1
def s_2_2 : Fin 16 → Scalar := ![219601857,1135322859,634523587,338231333,1325613339,213817799,2065332287,2142293461,15256333,1418350613,149322921,675652386,174706843,1596403903,1990140744,1604120083]
theorem round_2_2 : poseidonFullRound s_2_1 (poseidonExternalInitial 0) = s_2_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_2
def s_2_3 : Fin 16 → Scalar := ![14564691,1166526941,1609813567,1069854367,218235484,217435839,944149429,1192523068,146621859,1779501200,151613527,682999850,1692702825,1836739031,488410425,1001963614]
theorem round_2_3 : poseidonFullRound s_2_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_2_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_3
def s_2_4 : Fin 16 → Scalar := ![1392001442,793201313,271252573,338202774,2136338207,392714129,1965980050,967902083,1387968297,370764368,493513863,146112916,1374107400,965120133,89054033,372117323]
theorem round_2_4 : poseidonFullRound s_2_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_2_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_4
def s_2_5 : Fin 16 → Scalar := ![2135219826,1005528263,966526465,402176799,393135272,438388217,755675443,1105631755,1106583539,1010228651,1918856280,2045842164,494337889,2063533839,2013782936,2094466808]
theorem round_2_5 : poseidonFullRound s_2_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_2_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_5
def s_2_6 : Fin 16 → Scalar := ![946405633,1328772918,108813938,1931951851,1320843184,895005186,882538714,216716624,232016945,1243741671,284538370,611557805,1932556748,1426608110,84986487,440224797]
theorem round_2_6 : poseidonInternalRound s_2_5 (poseidonInternalConstants 0) = s_2_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_6
def s_2_7 : Fin 16 → Scalar := ![654627915,786087935,1822426540,742671480,1434125901,892496111,1928750101,442277071,1238196566,27603037,914313552,432151895,1860232596,1940058956,1155714521,734297411]
theorem round_2_7 : poseidonInternalRound s_2_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_2_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_7
def s_2_8 : Fin 16 → Scalar := ![791623472,485017104,1196298602,522131442,434518142,1093965063,1289390285,87374302,1421783386,322855700,1800619972,266565961,180396489,719405026,1425722099,1800494489]
theorem round_2_8 : poseidonInternalRound s_2_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_2_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_8
def s_2_9 : Fin 16 → Scalar := ![1051182115,1904590996,1664687449,1360616013,600751734,1743145724,1877873719,569078279,871737305,318770859,565972447,204573825,1758862644,613781493,974573439,842453287]
theorem round_2_9 : poseidonInternalRound s_2_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_2_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_9
def s_2_10 : Fin 16 → Scalar := ![403216683,1032058034,309358289,274963796,1785997263,1247994858,1237367577,1188738542,1188176081,1275912003,1010151723,1690715555,262458963,805013096,868085300,489003147]
theorem round_2_10 : poseidonInternalRound s_2_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_2_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_10
def s_2_11 : Fin 16 → Scalar := ![1789781239,656977838,243636382,724774988,1027996026,265484709,565976622,542258847,1387602882,1988361875,1080649949,1308555156,57614053,1262408441,1623125689,36697415]
theorem round_2_11 : poseidonInternalRound s_2_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_2_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_11
def s_2_12 : Fin 16 → Scalar := ![1089517287,1489382178,1319677104,1584020645,466437960,785192390,1763787068,1177232196,204430535,899420001,1463873911,555140404,360324176,1717297427,687496243,652509140]
theorem round_2_12 : poseidonInternalRound s_2_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_2_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_12
def s_2_13 : Fin 16 → Scalar := ![1350244346,326809530,1476781560,878542638,421447385,663087357,1591522353,1165843898,1382215715,1455681026,1048210257,654823610,2118029813,855211973,1758344593,982047328]
theorem round_2_13 : poseidonInternalRound s_2_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_2_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_13
def s_2_14 : Fin 16 → Scalar := ![1767453801,2051782743,383569039,944176471,801584999,1596952690,1114080981,1177055040,407442032,717161291,1350452881,1675404670,957333549,1187142170,26863980,1093760431]
theorem round_2_14 : poseidonInternalRound s_2_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_2_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_14
def s_2_15 : Fin 16 → Scalar := ![90061855,718992117,1581831099,296431611,784922072,596132297,2105546061,984287936,1427665589,1871873522,698974497,2061969176,680847585,1192615422,625294391,641645824]
theorem round_2_15 : poseidonInternalRound s_2_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_2_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_15
def s_2_16 : Fin 16 → Scalar := ![1784073420,1408206037,1705392471,1874940364,526139555,1637396084,1494694815,1406616061,894299317,999982271,1327044397,461775165,1177598981,546583915,1194342181,1712643677]
theorem round_2_16 : poseidonInternalRound s_2_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_2_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_16
def s_2_17 : Fin 16 → Scalar := ![652343565,983951055,839046313,633055533,1637377811,4278598,161338864,1552343395,229424303,20652401,1259542642,1221211498,2117538693,1947284035,38349098,1158950435]
theorem round_2_17 : poseidonInternalRound s_2_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_2_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_17
def s_2_18 : Fin 16 → Scalar := ![936520373,1886316266,432974190,1287103696,1116485817,970822779,1770241565,1468094729,203904937,1894412573,36358772,1495247156,406437801,39451172,1247674980,1676446275]
theorem round_2_18 : poseidonInternalRound s_2_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_2_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_18
def s_2_19 : Fin 16 → Scalar := ![689024160,848982817,1976098578,1963597688,1452102146,1610929133,1923305456,578932386,1440178370,748464664,1834310727,1019139930,2048963140,1085574499,1130223252,1282364431]
theorem round_2_19 : poseidonInternalRound s_2_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_2_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_19
def s_2_20 : Fin 16 → Scalar := ![1608257694,819258716,1494817533,312535869,763951819,708980014,955834708,1366466595,581022373,2136411395,510106152,1581998746,439974822,464680200,1768499143,146704997]
theorem round_2_20 : poseidonFullRound s_2_19 (poseidonExternalFinal 0) = s_2_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_20
def s_2_21 : Fin 16 → Scalar := ![1064392375,538433448,754965281,525840345,1252124368,2049131581,1572151485,1066355404,512221836,994660944,239463691,150382469,694419195,56012503,701634978,2140222209]
theorem round_2_21 : poseidonFullRound s_2_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_2_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_21
def s_2_22 : Fin 16 → Scalar := ![1732982648,896412361,470783180,1208466183,1238244,563586761,679497292,133100382,1617776722,1254995993,300868020,2025169925,2010710122,1978274568,1139172779,276711796]
theorem round_2_22 : poseidonFullRound s_2_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_2_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_22
def s_2_23 : Fin 16 → Scalar := ![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146,1696418417,19162039,1247441292,637518785,1071507386,938633149,367187411,2144955043]
theorem round_2_23 : poseidonFullRound s_2_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_2_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_2_23
theorem permutation_2 : poseidonPermutation s_2_0 = s_2_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_2_1,round_2_2,round_2_3,round_2_4,round_2_5,round_2_6,round_2_7,round_2_8,round_2_9,round_2_10,round_2_11,round_2_12,round_2_13,round_2_14,round_2_15,round_2_16,round_2_17,round_2_18,round_2_19,round_2_20,round_2_21,round_2_22,round_2_23]
#print axioms permutation_2
theorem parent_2 : nodeCompress (![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] : Fin 8 → Scalar) ![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] = ![1119858538,128294437,939091034,659145897,1933666768,903679201,1182639487,1398246146] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_2_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_2]
  funext i
  fin_cases i <;> rfl
#print axioms parent_2
end R1Z.PV_RunJoin_RootModel
