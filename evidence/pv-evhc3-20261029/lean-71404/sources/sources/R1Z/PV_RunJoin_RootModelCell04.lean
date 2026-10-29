import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_4_0 : Fin 16 → Scalar := ![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573,1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,973366555]
def s_4_1 : Fin 16 → Scalar := ![1684056640,1492465813,1177175356,1482879218,604019821,748114897,1655896007,1066576059,1684056640,1492465813,1177175356,1482879218,1699982450,1844077526,648816600,1111017670]
theorem round_4_1 : poseidonExternalLinear s_4_0 = s_4_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_1
def s_4_2 : Fin 16 → Scalar := ![586455055,988372417,1339257771,1048988158,1289984190,908473740,355882115,1676972641,2048671137,359047305,1920383361,1837576768,8878744,152939619,2035930621,262905689]
theorem round_4_2 : poseidonFullRound s_4_1 (poseidonExternalInitial 0) = s_4_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_2
def s_4_3 : Fin 16 → Scalar := ![941273087,605592081,725891049,1363852861,732758306,651909316,1696302050,733062197,1103700069,1239130086,385621802,1626171087,293260376,1438549056,1476994317,232982215]
theorem round_4_3 : poseidonFullRound s_4_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_4_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_3
def s_4_4 : Fin 16 → Scalar := ![285923936,1432789047,1964140757,1811762190,2057537772,1358777549,1149747510,2016466663,1562181873,495327766,2053275662,495422493,622643962,1950033938,1069813819,1365156210]
theorem round_4_4 : poseidonFullRound s_4_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_4_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_4
def s_4_5 : Fin 16 → Scalar := ![1882346672,1742553443,59877379,1183378543,963208524,2090060459,344673322,1458916612,707586856,302725992,808649367,153002943,1513689598,10165453,1066478090,652016861]
theorem round_4_5 : poseidonFullRound s_4_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_4_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_5
def s_4_6 : Fin 16 → Scalar := ![1245933955,840782608,1365467570,1684259690,361446416,326941804,1537840881,127095512,1622517206,1434155472,373976878,880542416,1820321850,292770298,1598378301,1193107302]
theorem round_4_6 : poseidonInternalRound s_4_5 (poseidonInternalConstants 0) = s_4_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_6
def s_4_7 : Fin 16 → Scalar := ![926190339,769029619,511698504,222834830,672334692,864348581,1894514969,1619908838,1452019267,1999827853,628480917,1004939634,2025881090,1345825692,609747496,1528803613]
theorem round_4_7 : poseidonInternalRound s_4_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_4_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_7
def s_4_8 : Fin 16 → Scalar := ![1484565729,1372600375,1626967764,1494910076,1687280998,1548246170,1098507648,1198521332,1778443290,1458393138,2070419311,110160321,867836020,249621088,621667996,1427601539]
theorem round_4_8 : poseidonInternalRound s_4_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_4_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_8
def s_4_9 : Fin 16 → Scalar := ![473006964,1614725544,1348577050,1926798179,855471271,1391743772,1034631553,1785562772,249599707,2076097566,785140044,487234115,1383929439,1225167073,29142655,116536224]
theorem round_4_9 : poseidonInternalRound s_4_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_4_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_9
def s_4_10 : Fin 16 → Scalar := ![529669660,1493515107,428460016,1143531338,280108790,671853445,774744554,338173680,1762781001,931305650,703310641,577416540,462581338,486465086,1342569335,744916895]
theorem round_4_10 : poseidonInternalRound s_4_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_4_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_10
def s_4_11 : Fin 16 → Scalar := ![57470409,2097191413,1460596338,882834364,697062979,615913191,1773181917,771955356,753861499,647237889,1386750945,1322328799,1908843894,1535831313,565653144,731559775]
theorem round_4_11 : poseidonInternalRound s_4_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_4_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_11
def s_4_12 : Fin 16 → Scalar := ![902353850,1136704843,1960706106,423367239,321049968,304189898,2094243599,1200015980,1044504834,1523655842,1733274090,1492000047,460259271,33853723,1577862412,2115992202]
theorem round_4_12 : poseidonInternalRound s_4_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_4_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_12
def s_4_13 : Fin 16 → Scalar := ![1647253120,2120557126,610297201,529837592,1404768380,1555923357,1427654394,475463711,1536484921,197724081,2035028021,477585433,446516183,1592468989,1563083527,892297530]
theorem round_4_13 : poseidonInternalRound s_4_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_4_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_13
def s_4_14 : Fin 16 → Scalar := ![1974727036,1664956277,764993553,1663749519,45127956,816852746,132183172,2056789244,793457162,769640006,353955065,1524213949,240319446,777487524,1180430937,1175617421]
theorem round_4_14 : poseidonInternalRound s_4_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_4_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_14
def s_4_15 : Fin 16 → Scalar := ![1952114958,1862585509,1727616338,410176367,558652880,382371286,132523442,835638381,828414559,1804458891,1870363096,643002507,1799510212,1827712091,83123084,190128469]
theorem round_4_15 : poseidonInternalRound s_4_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_4_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_15
def s_4_16 : Fin 16 → Scalar := ![1752709803,2105142519,1550306039,1883262478,416812756,2065530292,188339860,36322219,1052921859,475049001,2086437837,1165874460,1502460706,965482186,1010509126,801781500]
theorem round_4_16 : poseidonInternalRound s_4_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_4_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_16
def s_4_17 : Fin 16 → Scalar := ![1486175997,871693846,1867163405,2004633945,2101053375,1750264941,498459553,1091173343,396563165,120011351,680151297,332192206,1843357569,1009626596,1226722649,1836544178]
theorem round_4_17 : poseidonInternalRound s_4_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_4_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_17
def s_4_18 : Fin 16 → Scalar := ![1701433183,69745149,784894466,774136142,974092774,1432486595,116371470,313668551,566012542,2003669748,2035761450,500178528,1025734494,1001150973,1994392836,1088820949]
theorem round_4_18 : poseidonInternalRound s_4_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_4_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_18
def s_4_19 : Fin 16 → Scalar := ![1373112255,141578817,1641622600,1020894589,1422124919,1516782718,1648237061,819268109,1654478693,1910181170,1632420878,103685118,1932781452,449279514,113938212,454924816]
theorem round_4_19 : poseidonInternalRound s_4_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_4_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_19
def s_4_20 : Fin 16 → Scalar := ![1376325600,2043490100,473450059,1644159782,1737084772,1282670557,1529318062,363610417,1971727949,1841851789,261821532,909854345,2108406282,270088606,1539568510,1341308610]
theorem round_4_20 : poseidonFullRound s_4_19 (poseidonExternalFinal 0) = s_4_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_20
def s_4_21 : Fin 16 → Scalar := ![224192048,2129107432,1846255808,1769538697,8594414,791323310,1734725562,502582920,871869808,1919710279,548648040,997489938,1367508824,671130213,877364425,1488566803]
theorem round_4_21 : poseidonFullRound s_4_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_4_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_21
def s_4_22 : Fin 16 → Scalar := ![1103392417,122543124,1723074316,1981626349,1652327550,2023101537,2084029021,43502641,1446090723,1148489799,843723110,690870757,1754805092,1245552741,1769341865,2026330327]
theorem round_4_22 : poseidonFullRound s_4_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_4_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_22
def s_4_23 : Fin 16 → Scalar := ![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616,174792497,871199681,387673671,1483296908,1993172408,1148251752,1808503319,150795947]
theorem round_4_23 : poseidonFullRound s_4_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_4_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_4_23
theorem permutation_4 : poseidonPermutation s_4_0 = s_4_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_4_1,round_4_2,round_4_3,round_4_4,round_4_5,round_4_6,round_4_7,round_4_8,round_4_9,round_4_10,round_4_11,round_4_12,round_4_13,round_4_14,round_4_15,round_4_16,round_4_17,round_4_18,round_4_19,round_4_20,round_4_21,round_4_22,round_4_23]
#print axioms permutation_4
theorem parent_4 : nodeCompress (![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] : Fin 8 → Scalar) ![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] = ![1410054462,673771449,940847521,274330358,1719505495,1690439941,203201419,1855504616] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1057897051,1132946363,794377079,1971564389,1255722275,926653737,2031728153,2024887573] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_4_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_4]
  funext i
  fin_cases i <;> rfl
#print axioms parent_4
end R1Z.PV_RunJoin_RootModel
