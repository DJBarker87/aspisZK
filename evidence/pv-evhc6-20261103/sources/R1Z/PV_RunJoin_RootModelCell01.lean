import R1Z.PV_RunJoin_RootModelPreflight
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RootModel
open R0P
def s_1_0 : Fin 16 → Scalar := ![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732,1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,103505714]
def s_1_1 : Fin 16 → Scalar := ![455633231,1551915261,1303572548,490017943,1384821621,857859271,750321645,47696023,455633231,1551915261,1303572548,490017943,333300603,1953821900,1890725885,92137634]
theorem round_1_1 : poseidonExternalLinear s_1_0 = s_1_1 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_1
def s_1_2 : Fin 16 → Scalar := ![4570430,354622795,997969610,1603133783,521035137,30536372,678427406,680451328,1493513446,1477954254,1590607919,588036253,1377976754,395277051,2068885707,892504697]
theorem round_1_2 : poseidonFullRound s_1_1 (poseidonExternalInitial 0) = s_1_2 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_2
def s_1_3 : Fin 16 → Scalar := ![856178624,853847812,2139060015,1966158088,785650988,721735586,1352001516,1210414032,818237258,2048845465,1676260794,2050643896,1752624753,1028146275,701881412,1887286536]
theorem round_1_3 : poseidonFullRound s_1_2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s_1_3 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_3
def s_1_4 : Fin 16 → Scalar := ![1959693658,1660725834,389741303,1090194166,108753851,1866084385,271979654,1648971539,1596696466,1764015524,741057812,2074510262,2065062042,1232027636,469188987,1476595638]
theorem round_1_4 : poseidonFullRound s_1_3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_1_4 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_4
def s_1_5 : Fin 16 → Scalar := ![321483267,1972998281,1358649122,273639635,1751264706,286566563,974363164,256482220,2105399261,1546217401,1307055725,1782174493,1638435689,1973781450,75172247,962076220]
theorem round_1_5 : poseidonFullRound s_1_4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_1_5 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_5
def s_1_6 : Fin 16 → Scalar := ![764118789,1230209847,1974509810,351770106,382427332,1694792927,372061756,639688117,312861099,2099358821,1947445532,1894502388,1697065751,883731840,1485141800,1911973213]
theorem round_1_6 : poseidonInternalRound s_1_5 (poseidonInternalConstants 0) = s_1_6 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_6
def s_1_7 : Fin 16 → Scalar := ![1359808927,1118259599,1689585725,1295130176,799984761,1234932820,1056607709,25899947,1279564778,452996178,1207450104,911414389,1589034913,615768238,887627485,1588701764]
theorem round_1_7 : poseidonInternalRound s_1_6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s_1_7 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_7
def s_1_8 : Fin 16 → Scalar := ![185033534,226888532,340316736,2141665990,1213539727,1687684877,707820916,766225541,1831646992,1259017210,734438404,2082871438,584251762,1124750366,1515026092,1965260583]
theorem round_1_8 : poseidonInternalRound s_1_7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s_1_8 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_8
def s_1_9 : Fin 16 → Scalar := ![1172692316,1057268196,1511013136,807109036,1948762892,2063533932,2005812506,476690407,1205477117,1016238374,1276028910,319260181,279764805,1183201301,1825894621,816218327]
theorem round_1_9 : poseidonInternalRound s_1_8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s_1_9 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_9
def s_1_10 : Fin 16 → Scalar := ![1480102371,801974955,619249384,825659256,302424366,548994966,1653681188,188121749,1574438798,56209216,728253223,1764350759,212937970,2127424521,1765242267,1906305555]
theorem round_1_10 : poseidonInternalRound s_1_9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s_1_10 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_10
def s_1_11 : Fin 16 → Scalar := ![186509686,701230557,1137754370,1054408979,171166883,93240470,1277446090,1201629303,1711442575,1403913016,453730445,397492311,530384478,1963016856,885828713,1678943857]
theorem round_1_11 : poseidonInternalRound s_1_10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s_1_11 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_11
def s_1_12 : Fin 16 → Scalar := ![388711543,1718489409,1145283945,939927474,239110269,361622725,1093344439,612122952,1038576458,1789221899,1780766780,1353160282,1567484747,222846437,316069937,1662249865]
theorem round_1_12 : poseidonInternalRound s_1_11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s_1_12 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_12
def s_1_13 : Fin 16 → Scalar := ![682359652,504430288,1076508769,398167128,698823031,276937185,1560708222,1454587808,727225036,1560213859,1224990943,822646691,1963746537,1327248434,599490661,590132150]
theorem round_1_13 : poseidonInternalRound s_1_12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s_1_13 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_13
def s_1_14 : Fin 16 → Scalar := ![1214611917,944244444,445348047,2032482668,1735431110,575841822,990353379,1191637047,1182821943,422603718,700089940,598818349,651445583,658747290,1516874695,1307397733]
theorem round_1_14 : poseidonInternalRound s_1_13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s_1_14 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_14
def s_1_15 : Fin 16 → Scalar := ![1204227316,1731005253,1677456903,326756893,1785307807,1410295373,265814232,1889604172,1864114223,1599130267,419321271,1120393439,932113950,449550347,80273107,2102042691]
theorem round_1_15 : poseidonInternalRound s_1_14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s_1_15 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_15
def s_1_16 : Fin 16 → Scalar := ![1088197073,1589429684,1065854590,1165452003,1255985005,948313929,1922028914,534007207,94360158,1213879853,1894160182,1964880583,1431537746,1569884116,1727610679,399750404]
theorem round_1_16 : poseidonInternalRound s_1_15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s_1_16 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_16
def s_1_17 : Fin 16 → Scalar := ![503034771,2133443020,528238869,910854054,2001958788,684650671,1919396468,360736232,1884695325,2059610536,986306463,2073655995,293032301,1113729761,1074324241,1433480127]
theorem round_1_17 : poseidonInternalRound s_1_16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s_1_17 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_17
def s_1_18 : Fin 16 → Scalar := ![161740151,85739278,1156257643,1595712474,1083064680,316772406,1390924765,1712062283,822613041,1226583606,760283927,496911540,1881155998,279635570,2004567369,833761315]
theorem round_1_18 : poseidonInternalRound s_1_17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s_1_18 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_18
def s_1_19 : Fin 16 → Scalar := ![549658092,763401918,842694279,618061595,752245492,1451053842,90098533,727982755,745433185,1150453314,1819323674,212833124,764947384,1644222469,1258899243,1485288212]
theorem round_1_19 : poseidonInternalRound s_1_18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s_1_19 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_19
def s_1_20 : Fin 16 → Scalar := ![933147035,1078435162,1373646479,1455942207,1768053696,1913001935,1811686983,1321789387,351953416,1783900512,1885089425,1379207684,1497175985,174692267,934432714,132182935]
theorem round_1_20 : poseidonFullRound s_1_19 (poseidonExternalFinal 0) = s_1_20 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_20
def s_1_21 : Fin 16 → Scalar := ![144986582,1573051722,1995194950,1917319422,762118607,21836791,1480914566,1764801278,1045233420,115591153,989460370,1734523450,643642933,421322836,717680167,1930194842]
theorem round_1_21 : poseidonFullRound s_1_20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s_1_21 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_21
def s_1_22 : Fin 16 → Scalar := ![1161744697,120567736,267352927,962996494,1158169343,918621340,1141066418,982524175,1402968818,1258260697,644040189,1847335913,1385203626,1518583204,459109002,545385497]
theorem round_1_22 : poseidonFullRound s_1_21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s_1_22 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_22
def s_1_23 : Fin 16 → Scalar := ![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536,1744406230,507427987,1522520675,4203131,2091267476,483181084,97461750,1846239352]
theorem round_1_23 : poseidonFullRound s_1_22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s_1_23 := by
  funext i
  fin_cases i <;> rfl
#print axioms round_1_23
theorem permutation_1 : poseidonPermutation s_1_0 = s_1_23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [round_1_1,round_1_2,round_1_3,round_1_4,round_1_5,round_1_6,round_1_7,round_1_8,round_1_9,round_1_10,round_1_11,round_1_12,round_1_13,round_1_14,round_1_15,round_1_16,round_1_17,round_1_18,round_1_19,round_1_20,round_1_21,round_1_22,round_1_23]
#print axioms permutation_1
theorem parent_1 : nodeCompress (![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] : Fin 8 → Scalar) ![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] = ![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536] := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then (![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then (![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else (![1438900896,782233260,1544844157,891350894,986827501,300047813,266092546,1155026732] : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_1_0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation_1]
  funext i
  fin_cases i <;> rfl
#print axioms parent_1
end R1Z.PV_RunJoin_RootModel
