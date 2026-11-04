import PV_2TNV_PublicEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_Node16
open R0P
abbrev M := PV_2TNV_PublicEncoding.M
def s0 : Fin 16 → M := ![1905130866,103172962,879709043,1820432331,505138134,43749841,2088595767,1314077240,1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,163202459]
def s1 : Fin 16 → M := ![1141679,17824498,1854909582,2025060508,2020385779,1619290605,1294201904,109319380,1210907115,1726822796,1617974354,1125329880,1328369508,377225340,1312040475,267053034]
def s2 : Fin 16 → M := ![886871883,1824798221,1583661822,1995159143,579365271,44208391,747133694,2081850733,1726014560,740875029,213726219,859911248,1069541096,1169780915,1291969043,1783583805]
def s3 : Fin 16 → M := ![1250183633,939145421,1600501128,1197947896,1934921204,757213014,1838512589,1045085973,1472348849,144561902,527491607,1077235192,397145387,1396193881,109671150,1213588379]
def s4 : Fin 16 → M := ![420920960,807173070,392021230,1964308964,115078721,1644290650,892379521,1615838998,1746168936,1356448944,111588740,1466333217,1689167822,735883631,1626419333,1657604424]
def s5 : Fin 16 → M := ![1285769703,533672278,1832472874,353807173,1137080190,1713226804,395737834,542460659,1136742270,202705414,1007076670,1095963383,220102438,1356015614,969953006,1922955424]
def s6 : Fin 16 → M := ![766205477,690123452,1673913275,1571679866,663158106,1798276274,2082643627,514194998,1778057385,509429630,610810694,981645712,1496843437,1397942735,818576182,32777890]
def s7 : Fin 16 → M := ![1562465184,155550089,665769540,1457178807,475724191,320559610,1685513291,161651804,1570988982,1030393097,17836016,196875805,1622721818,446101622,499007383,113578677]
def s8 : Fin 16 → M := ![1570489682,96609048,1272598039,1474806893,1599368840,775045425,190393096,1696839827,1311669484,1728686857,1025270167,1037988614,354417085,983183066,474496845,254914329]
def s9 : Fin 16 → M := ![37947802,693949065,995052448,54116648,507388855,113164935,247468148,1820906595,987309503,759544127,354487642,181081901,584209593,793857214,1128352697,1387515348]
def s10 : Fin 16 → M := ![1568796742,1014608938,163281122,537126465,84803419,2131298833,1797189668,894565015,2142224731,1490428155,391268938,1150268154,1572080213,1716287817,955884770,1626441480]
def s11 : Fin 16 → M := ![1548339836,442046186,1901483139,1575943108,105864600,1315963871,1102931802,845023386,901779647,872439409,654871418,1494158161,1596594732,2083640805,810589113,1692935330]
def s12 : Fin 16 → M := ![1380596384,1641724511,707677309,1060999816,2046595125,780263791,2133757637,1594083854,663356203,1205867741,1773112493,943111831,180828992,1023091086,358503366,1814326597]
def s13 : Fin 16 → M := ![552026700,437076516,210706623,891867622,135727476,542154426,503603332,2032470899,2100567403,407332180,1986346769,605814475,530221686,9840194,1645583650,628645901]
def s14 : Fin 16 → M := ![1565013541,585661162,569997892,1568571487,1234404454,233120874,1231505741,1377703362,585756355,1346407670,500662393,1221061961,1512702124,309049617,1466735323,1760068534]
def s15 : Fin 16 → M := ![2735901,1524972101,2079306723,771145946,77128336,374277629,1692789005,1065496580,754196734,2022290939,369009738,919689332,2014467557,641796241,90871496,1001623852]
def s16 : Fin 16 → M := ![1949692089,308633372,794791070,1868245055,1548171606,477136041,1413301903,403449334,831562755,1094066375,839994758,1292331952,37544667,2040821750,48507457,1219271741]
def s17 : Fin 16 → M := ![2029818240,944671040,78136161,1666566947,136508634,1827763383,764541977,686991280,1849371605,1544155558,1797211060,480523205,1111788211,1139205878,990489864,1109834621]
def s18 : Fin 16 → M := ![523244312,464690871,1823775800,1891320325,612088903,846946548,363042978,537788811,16384101,1834335278,1618143439,648046859,1958381063,488748906,971526272,518101444]
def s19 : Fin 16 → M := ![1721790101,12256555,1047633637,670396043,149309614,213808570,427522745,1753794883,1644730612,985961806,816555383,1805196103,902390690,1390605572,222863452,2127340598]
def s20 : Fin 16 → M := ![32677614,473900280,526519361,683720001,1477289422,2032325979,308254886,1491267850,1116400774,1850681240,1223529842,160341313,1795194273,1069572596,1172462929,516046578]
def s21 : Fin 16 → M := ![1201028352,2058175719,847288992,2064523059,818095542,594650159,656790384,895468303,2065321482,1380289891,587786757,1659276617,1020789066,350991164,1487485336,1793191960]
def s22 : Fin 16 → M := ![1337801817,4127724,341444639,2034989211,783170411,1431929338,1058153433,16736725,133854926,117794812,612870467,121350497,1275226265,2018536249,1837473061,1822485553]
def s23 : Fin 16 → M := ![1557358515,718034323,1313248758,1367913086,936067934,1596966802,2009926348,554911201,1206212233,1772510057,987284501,346945232,415073331,383078500,1606939760,644358342]
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
def left : Fin 8 → M := ![1905130866,103172962,879709043,1820432331,505138134,43749841,2088595767,1314077240]
def right : Fin 8 → M := ![1796237568,1862343136,1954463912,1190686266,364700025,46960257,671215600,1214723477]
def output : Fin 8 → M := ![1557358515,718034323,1313248758,1367913086,936067934,1596966802,2009926348,554911201]
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
end AspisR1.PV_2TNV_Node16
