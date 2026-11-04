import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node02
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![248012357,194341198,430781749,501414171,630694870,1921243919,1220508734,1000843895,141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,2134309165]
def s1 : Fin 16 → M := ![736630921,16514867,190372656,1245008654,1529409878,279162560,1082733738,1613578053,1526679999,1993914986,1559061552,864270650,571630902,673096596,1258766680,1379662348]
def s2 : Fin 16 → M := ![2001478530,2073390795,2010865338,2092999487,1383660293,78183509,1225650726,29602599,1969315917,699785407,689431236,782964772,701485382,483269857,945700464,1459568767]
def s3 : Fin 16 → M := ![2138465536,1928366810,2024973680,30634544,1957569491,579259297,1018248244,1117646672,1713904720,329636199,1155940906,103552579,400435807,1990157797,1760480188,161275671]
def s4 : Fin 16 → M := ![479896943,2010761527,743349212,1937280579,1950561029,398637568,725477782,1034854233,1180926376,1353222387,870554477,2018664951,1808079158,147732416,933292011,1033871868]
def s5 : Fin 16 → M := ![1648140533,1826653627,81405138,2092692628,624205593,1159202332,507756095,1276818665,1211541379,1111707142,2111261047,1290001803,684865244,70363026,657770284,371426279]
def s6 : Fin 16 → M := ![1355066429,562156704,1045797000,663822648,1581664174,102871213,2098796235,995002698,1341460652,2012173672,298266323,1920600192,2071779608,512086269,406287897,948468523]
def s7 : Fin 16 → M := ![152491854,1319877761,701831410,1265528002,526132567,256176818,1347207520,13384319,665992753,478105809,1239757935,1303508528,1213007552,560543524,1748402200,676681970]
def s8 : Fin 16 → M := ![1694650840,487700493,571485552,2082451093,1229399621,1119168173,1476274079,24419148,663032883,1303825604,1664596442,1841890625,1866337694,472845376,242377666,660098102]
def s9 : Fin 16 → M := ![752124773,1082609764,1737880375,334779055,1840171651,1321730863,591039565,10251096,1711256062,1514298610,39650161,868857360,1697215526,1720034926,1431742153,1873536775]
def s10 : Fin 16 → M := ![1440304455,832674841,1078342180,1089181297,1586536403,1570406062,1483461981,406135221,1894992666,863452777,1697124295,209408558,530523391,1521876727,1149182219,1478634252]
def s11 : Fin 16 → M := ![1977865817,1426420059,602945931,655503112,401134560,2097922093,819888376,816595598,487154355,446840489,1134752875,1485223633,134462762,589415069,870947265,1315997062]
def s12 : Fin 16 → M := ![1668656379,558366394,337838197,1753958783,193539168,486445118,1746054250,2001940726,1358161659,1853961875,1477720955,934258799,1139265375,1021959919,421740872,1372138047]
def s13 : Fin 16 → M := ![97174828,1563637135,1680947135,1578654932,406100438,198458041,1044431919,280458385,903787686,1025624754,215557526,913452491,903292879,866587978,1552895992,1714084455]
def s14 : Fin 16 → M := ![1711286374,1631006842,1281780330,2087022141,1168689564,1095214716,1276936410,836837171,1935560224,634301797,1754944337,652259769,1761470560,1230410942,738219898,1584121664]
def s15 : Fin 16 → M := ![1149912365,1163941561,2096495379,1438572342,292516643,2023984646,1740194193,1550906135,324023986,852921226,1299606915,1866775322,557138046,156814058,266752575,728359702]
def s16 : Fin 16 → M := ![1289069946,380622368,1262187918,676002881,1556813951,1535664085,1215803808,1837909332,2037045369,668666316,721784274,486616399,2036287411,67765267,2054098764,879089210]
def s17 : Fin 16 → M := ![1788786352,1212296017,1208565838,1388201526,401283375,1779978892,1082689859,346270312,1727959594,211558785,1204395657,1147619537,445174665,848762678,960024480,130858493]
def s18 : Fin 16 → M := ![1986587576,1647184093,704536105,1692726886,1497671429,997262937,721225212,1121351574,422900467,906845861,1080427466,242808345,878511150,1605990103,29103813,1474882853]
def s19 : Fin 16 → M := ![701006256,928263367,690151484,1757019524,525032471,204900737,885449588,180619659,1872731522,1652869461,1832209900,1686615480,1974202624,853283782,1619568037,1112265659]
def s20 : Fin 16 → M := ![829980231,90133113,1139625145,10090565,238362794,670292065,2110306669,78026704,1148171226,1067812722,1715687134,1241721113,908569410,1977621889,213983671,1398994431]
def s21 : Fin 16 → M := ![1383319493,366232519,1038902309,1220864116,155262236,1044654750,1050378758,517318501,256189004,1031430745,737589859,720499394,1124378486,1109752169,1754275753,930336588]
def s22 : Fin 16 → M := ![434809966,688056960,1107836473,1927087292,1637591595,414518642,1893960068,1301798101,1576326453,1683377507,721035580,638592262,2085474768,1319980289,1297444451,1228038575]
def s23 : Fin 16 → M := ![419899633,1577591246,694069026,1900771153,373160155,13932930,808890691,1709528413,2008132044,287246220,1427003586,275658147,32153006,1069666529,1303940977,360670645]
theorem r1 : poseidonExternalLinear s0 = s1 := by
  funext i
  fin_cases i <;> rfl
#print axioms r1
theorem r2 : poseidonFullRound s1 (poseidonExternalInitial 0) = s2 := by
  funext i
  fin_cases i <;> rfl
#print axioms r2
theorem r3 : poseidonFullRound s2 (poseidonExternalInitial (Fin.succ ((0 : Fin 3)))) = s3 := by
  funext i
  fin_cases i <;> rfl
#print axioms r3
theorem r4 : poseidonFullRound s3 (poseidonExternalInitial (Fin.succ (Fin.succ ((0 : Fin 2))))) = s4 := by
  funext i
  fin_cases i <;> rfl
#print axioms r4
theorem r5 : poseidonFullRound s4 (poseidonExternalInitial (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s5 := by
  funext i
  fin_cases i <;> rfl
#print axioms r5
theorem r6 : poseidonInternalRound s5 (poseidonInternalConstants 0) = s6 := by
  funext i
  fin_cases i <;> rfl
#print axioms r6
theorem r7 : poseidonInternalRound s6 (poseidonInternalConstants (Fin.succ ((0 : Fin 13)))) = s7 := by
  funext i
  fin_cases i <;> rfl
#print axioms r7
theorem r8 : poseidonInternalRound s7 (poseidonInternalConstants (Fin.succ (Fin.succ ((0 : Fin 12))))) = s8 := by
  funext i
  fin_cases i <;> rfl
#print axioms r8
theorem r9 : poseidonInternalRound s8 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 11)))))) = s9 := by
  funext i
  fin_cases i <;> rfl
#print axioms r9
theorem r10 : poseidonInternalRound s9 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 10))))))) = s10 := by
  funext i
  fin_cases i <;> rfl
#print axioms r10
theorem r11 : poseidonInternalRound s10 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 9)))))))) = s11 := by
  funext i
  fin_cases i <;> rfl
#print axioms r11
theorem r12 : poseidonInternalRound s11 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 8))))))))) = s12 := by
  funext i
  fin_cases i <;> rfl
#print axioms r12
theorem r13 : poseidonInternalRound s12 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 7)))))))))) = s13 := by
  funext i
  fin_cases i <;> rfl
#print axioms r13
theorem r14 : poseidonInternalRound s13 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 6))))))))))) = s14 := by
  funext i
  fin_cases i <;> rfl
#print axioms r14
theorem r15 : poseidonInternalRound s14 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 5)))))))))))) = s15 := by
  funext i
  fin_cases i <;> rfl
#print axioms r15
theorem r16 : poseidonInternalRound s15 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 4))))))))))))) = s16 := by
  funext i
  fin_cases i <;> rfl
#print axioms r16
theorem r17 : poseidonInternalRound s16 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 3)))))))))))))) = s17 := by
  funext i
  fin_cases i <;> rfl
#print axioms r17
theorem r18 : poseidonInternalRound s17 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 2))))))))))))))) = s18 := by
  funext i
  fin_cases i <;> rfl
#print axioms r18
theorem r19 : poseidonInternalRound s18 (poseidonInternalConstants (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))))))))))))) = s19 := by
  funext i
  fin_cases i <;> rfl
#print axioms r19
theorem r20 : poseidonFullRound s19 (poseidonExternalFinal 0) = s20 := by
  funext i
  fin_cases i <;> rfl
#print axioms r20
theorem r21 : poseidonFullRound s20 (poseidonExternalFinal (Fin.succ ((0 : Fin 3)))) = s21 := by
  funext i
  fin_cases i <;> rfl
#print axioms r21
theorem r22 : poseidonFullRound s21 (poseidonExternalFinal (Fin.succ (Fin.succ ((0 : Fin 2))))) = s22 := by
  funext i
  fin_cases i <;> rfl
#print axioms r22
theorem r23 : poseidonFullRound s22 (poseidonExternalFinal (Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))))) = s23 := by
  funext i
  fin_cases i <;> rfl
#print axioms r23
theorem permutation : poseidonPermutation s0 = s23 := by
  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]
  rw [r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23]
#print axioms permutation
def left : Fin 8 → M := ![248012357,194341198,430781749,501414171,630694870,1921243919,1220508734,1000843895]
def right : Fin 8 → M := ![141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536]
def output : Fin 8 → M := ![419899633,1577591246,694069026,1900771153,373160155,13932930,808890691,1709528413]
theorem source : nodeCompress left right = output := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then left ⟨l.val,h⟩
    else if l.val = 15 then right 7 - (1051521018 : M)
    else right ⟨l.val-8,by omega⟩) = s0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation]
  funext i
  fin_cases i <;> rfl
#print axioms source
end AspisR1.PV_2TNV_Node02
