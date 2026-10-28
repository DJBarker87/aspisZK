import NDO_JGn_CopyData
import RPv_FJk_CopyFullFold
import NDO_JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyRows
open Aeneas Aeneas.Std FIq_Native
open FIv_NativeValue (K)
open FIw_ArrayValue (decoded)
def step := FJk_CopyStep.step (FIw_CopyEndpoint.modelSelectors JGl_NumericData.selectors)
  (decoded JGn_CopyData.patterns) JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index.val
  R0P.Variant.privateTransfer
def pv000 : Array field.QM31 2#usize := ⟨[⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩],by rfl⟩
def pw000 : Array field.QM31 2#usize := ⟨[⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩],by rfl⟩
def cv000 : Array field.QM31 2#usize := ⟨[⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩],by rfl⟩
def cw000 : Array field.QM31 2#usize := ⟨[⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩],by rfl⟩
def row000 : R0P.CopyRowExtension K := FJk_CopyStep.row pv000 pw000 cv000 cw000
def pv008 : Array field.QM31 2#usize := ⟨[⟨⟨806916458#u32,67193345#u32⟩,⟨43939466#u32,726788583#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩],by rfl⟩
def pw008 : Array field.QM31 2#usize := ⟨[⟨⟨685357659#u32,798252192#u32⟩,⟨1744183019#u32,210605895#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩],by rfl⟩
def cv008 : Array field.QM31 2#usize := ⟨[⟨⟨493730962#u32,680995473#u32⟩,⟨94512748#u32,1883690129#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩],by rfl⟩
def cw008 : Array field.QM31 2#usize := ⟨[⟨⟨1750885043#u32,777283524#u32⟩,⟨673359633#u32,208217971#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩],by rfl⟩
def row008 : R0P.CopyRowExtension K := FJk_CopyStep.row pv008 pw008 cv008 cw008
def pv016 : Array field.QM31 2#usize := ⟨[⟨⟨688780253#u32,843008551#u32⟩,⟨2050462662#u32,1524087124#u32⟩⟩,⟨⟨897478177#u32,237466021#u32⟩,⟨832464487#u32,1872393598#u32⟩⟩],by rfl⟩
def pw016 : Array field.QM31 2#usize := ⟨[⟨⟨438358452#u32,1339178862#u32⟩,⟨1879347841#u32,1140481623#u32⟩⟩,⟨⟨1913634793#u32,821913560#u32⟩,⟨1385486159#u32,1409632738#u32⟩⟩],by rfl⟩
def cv016 : Array field.QM31 2#usize := ⟨[⟨⟨1192440714#u32,1995516833#u32⟩,⟨1747366042#u32,728679358#u32⟩⟩,⟨⟨232375789#u32,1045513385#u32⟩,⟨350276088#u32,1708670973#u32⟩⟩],by rfl⟩
def cw016 : Array field.QM31 2#usize := ⟨[⟨⟨2111984495#u32,1291226159#u32⟩,⟨260792701#u32,1167963768#u32⟩⟩,⟨⟨1343450128#u32,1444678829#u32⟩,⟨299578147#u32,1163966459#u32⟩⟩],by rfl⟩
def row016 : R0P.CopyRowExtension K := FJk_CopyStep.row pv016 pw016 cv016 cw016
def pv024 : Array field.QM31 2#usize := ⟨[⟨⟨1015558892#u32,1200462769#u32⟩,⟨1679352276#u32,776169526#u32⟩⟩,⟨⟨680661593#u32,422776194#u32⟩,⟨1263454904#u32,2145593299#u32⟩⟩],by rfl⟩
def pw024 : Array field.QM31 2#usize := ⟨[⟨⟨1597799239#u32,2100555291#u32⟩,⟨1610000447#u32,2024200372#u32⟩⟩,⟨⟨1913634793#u32,821913560#u32⟩,⟨1385486159#u32,1409632738#u32⟩⟩],by rfl⟩
def cv024 : Array field.QM31 2#usize := ⟨[⟨⟨811343565#u32,123290747#u32⟩,⟨160728518#u32,165054229#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw024 : Array field.QM31 2#usize := ⟨[⟨⟨922803018#u32,419007031#u32⟩,⟨183721251#u32,1874441400#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row024 : R0P.CopyRowExtension K := FJk_CopyStep.row pv024 pw024 cv024 cw024
def pv032 : Array field.QM31 2#usize := ⟨[⟨⟨1501812711#u32,1020796879#u32⟩,⟨757992464#u32,807038315#u32⟩⟩,⟨⟨433113833#u32,955632975#u32⟩,⟨1669032826#u32,1798416241#u32⟩⟩],by rfl⟩
def pw032 : Array field.QM31 2#usize := ⟨[⟨⟨384202726#u32,307091812#u32⟩,⟨197613554#u32,991590332#u32⟩⟩,⟨⟨245946080#u32,1180416063#u32⟩,⟨1977327139#u32,2064196931#u32⟩⟩],by rfl⟩
def cv032 : Array field.QM31 2#usize := ⟨[⟨⟨1266692879#u32,1930967569#u32⟩,⟨651713301#u32,684995766#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw032 : Array field.QM31 2#usize := ⟨[⟨⟨1056835058#u32,1036226194#u32⟩,⟨1321974267#u32,1872559261#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row032 : R0P.CopyRowExtension K := FJk_CopyStep.row pv032 pw032 cv032 cw032
def pv040 : Array field.QM31 2#usize := ⟨[⟨⟨2071574801#u32,2605506#u32⟩,⟨804187155#u32,2072453696#u32⟩⟩,⟨⟨1938443220#u32,899979951#u32⟩,⟨1738133776#u32,2145358871#u32⟩⟩],by rfl⟩
def pw040 : Array field.QM31 2#usize := ⟨[⟨⟨1319770023#u32,1269630161#u32⟩,⟨220519813#u32,73117581#u32⟩⟩,⟨⟨245946080#u32,1180416063#u32⟩,⟨1977327139#u32,2064196931#u32⟩⟩],by rfl⟩
def cv040 : Array field.QM31 2#usize := ⟨[⟨⟨1506712153#u32,1260271548#u32⟩,⟨53533151#u32,915368461#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw040 : Array field.QM31 2#usize := ⟨[⟨⟨319239722#u32,1286723291#u32⟩,⟨1685827314#u32,847637868#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row040 : R0P.CopyRowExtension K := FJk_CopyStep.row pv040 pw040 cv040 cw040
def pv048 : Array field.QM31 2#usize := ⟨[⟨⟨1294497261#u32,467944061#u32⟩,⟨1421638016#u32,1335097934#u32⟩⟩,⟨⟨2085687237#u32,322386767#u32⟩,⟨467752476#u32,990173857#u32⟩⟩],by rfl⟩
def pw048 : Array field.QM31 2#usize := ⟨[⟨⟨96607933#u32,226698422#u32⟩,⟨480171299#u32,1802771976#u32⟩⟩,⟨⟨245946080#u32,1180416063#u32⟩,⟨1977327139#u32,2064196931#u32⟩⟩],by rfl⟩
def cv048 : Array field.QM31 2#usize := ⟨[⟨⟨871666366#u32,1182635336#u32⟩,⟨865021187#u32,1787247400#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw048 : Array field.QM31 2#usize := ⟨[⟨⟨958205050#u32,163357605#u32⟩,⟨1028719293#u32,781513016#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row048 : R0P.CopyRowExtension K := FJk_CopyStep.row pv048 pw048 cv048 cw048
def pv056 : Array field.QM31 2#usize := ⟨[⟨⟨1275389852#u32,1643891405#u32⟩,⟨916094972#u32,1571319210#u32⟩⟩,⟨⟨1951326649#u32,482908747#u32⟩,⟨217004794#u32,258629789#u32⟩⟩],by rfl⟩
def pw056 : Array field.QM31 2#usize := ⟨[⟨⟨2128838401#u32,1358756705#u32⟩,⟨734966661#u32,835006632#u32⟩⟩,⟨⟨245946080#u32,1180416063#u32⟩,⟨1977327139#u32,2064196931#u32⟩⟩],by rfl⟩
def cv056 : Array field.QM31 2#usize := ⟨[⟨⟨119651345#u32,412395141#u32⟩,⟨925142650#u32,1454207779#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw056 : Array field.QM31 2#usize := ⟨[⟨⟨1275365512#u32,1539533780#u32⟩,⟨1434365535#u32,1555770460#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row056 : R0P.CopyRowExtension K := FJk_CopyStep.row pv056 pw056 cv056 cw056
def pv064 : Array field.QM31 2#usize := ⟨[⟨⟨212664519#u32,572992211#u32⟩,⟨1020490940#u32,1973366414#u32⟩⟩,⟨⟨514781294#u32,503583741#u32⟩,⟨578587868#u32,1976630950#u32⟩⟩],by rfl⟩
def pw064 : Array field.QM31 2#usize := ⟨[⟨⟨1755018379#u32,302847246#u32⟩,⟨992153767#u32,3476942#u32⟩⟩,⟨⟨245946080#u32,1180416063#u32⟩,⟨1977327139#u32,2064196931#u32⟩⟩],by rfl⟩
def cv064 : Array field.QM31 2#usize := ⟨[⟨⟨1422877639#u32,550204727#u32⟩,⟨800230989#u32,538397974#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw064 : Array field.QM31 2#usize := ⟨[⟨⟨1979115910#u32,1780275472#u32⟩,⟨793310723#u32,181889600#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row064 : R0P.CopyRowExtension K := FJk_CopyStep.row pv064 pw064 cv064 cw064
def pv072 : Array field.QM31 2#usize := ⟨[⟨⟨812674065#u32,1772543764#u32⟩,⟨1121428632#u32,233557402#u32⟩⟩,⟨⟨1052994013#u32,2045806901#u32⟩,⟨1636098306#u32,1745048896#u32⟩⟩],by rfl⟩
def pw072 : Array field.QM31 2#usize := ⟨[⟨⟨660724393#u32,298040926#u32⟩,⟨375635598#u32,671505345#u32⟩⟩,⟨⟨1830906096#u32,1354372063#u32⟩,⟨1079194062#u32,1303797251#u32⟩⟩],by rfl⟩
def cv072 : Array field.QM31 2#usize := ⟨[⟨⟨485913639#u32,1069576259#u32⟩,⟨1537896858#u32,319479088#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw072 : Array field.QM31 2#usize := ⟨[⟨⟨106338769#u32,689448204#u32⟩,⟨985943023#u32,1382021190#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row072 : R0P.CopyRowExtension K := FJk_CopyStep.row pv072 pw072 cv072 cw072
def pv080 : Array field.QM31 2#usize := ⟨[⟨⟨1059582705#u32,511845831#u32⟩,⟨692414644#u32,1213896135#u32⟩⟩,⟨⟨440762006#u32,954438723#u32⟩,⟨1191998359#u32,420313980#u32⟩⟩],by rfl⟩
def pw080 : Array field.QM31 2#usize := ⟨[⟨⟨152006236#u32,2129381433#u32⟩,⟨1662671538#u32,113152722#u32⟩⟩,⟨⟨1018460226#u32,966980586#u32⟩,⟨1869097787#u32,914294677#u32⟩⟩],by rfl⟩
def cv080 : Array field.QM31 2#usize := ⟨[⟨⟨1705300969#u32,87762945#u32⟩,⟨1498948059#u32,405548215#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw080 : Array field.QM31 2#usize := ⟨[⟨⟨2119553657#u32,1602882722#u32⟩,⟨844319592#u32,284440614#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row080 : R0P.CopyRowExtension K := FJk_CopyStep.row pv080 pw080 cv080 cw080
def pv088 : Array field.QM31 2#usize := ⟨[⟨⟨1921519018#u32,1612190005#u32⟩,⟨394306738#u32,1704929520#u32⟩⟩,⟨⟨156063652#u32,1369671777#u32⟩,⟨658008454#u32,789007806#u32⟩⟩],by rfl⟩
def pw088 : Array field.QM31 2#usize := ⟨[⟨⟨1957734933#u32,1560040677#u32⟩,⟨2133753786#u32,66357581#u32⟩⟩,⟨⟨1895442820#u32,1685246808#u32⟩,⟨2085760361#u32,510613062#u32⟩⟩],by rfl⟩
def cv088 : Array field.QM31 2#usize := ⟨[⟨⟨982698229#u32,1291400055#u32⟩,⟨302925834#u32,1114247182#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw088 : Array field.QM31 2#usize := ⟨[⟨⟨109287299#u32,2064962161#u32⟩,⟨1925211840#u32,1389522729#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row088 : R0P.CopyRowExtension K := FJk_CopyStep.row pv088 pw088 cv088 cw088
def pv096 : Array field.QM31 2#usize := ⟨[⟨⟨1616738812#u32,256175462#u32⟩,⟨453548351#u32,394180423#u32⟩⟩,⟨⟨957956481#u32,744440975#u32⟩,⟨1879572189#u32,560355810#u32⟩⟩],by rfl⟩
def pw096 : Array field.QM31 2#usize := ⟨[⟨⟨311840324#u32,1778919700#u32⟩,⟨43814328#u32,1127564382#u32⟩⟩,⟨⟨272392291#u32,1070755965#u32⟩,⟨1138994552#u32,140723222#u32⟩⟩],by rfl⟩
def cv096 : Array field.QM31 2#usize := ⟨[⟨⟨1315624711#u32,533077659#u32⟩,⟨76667636#u32,1743258032#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw096 : Array field.QM31 2#usize := ⟨[⟨⟨1827519924#u32,95347853#u32⟩,⟨1149928303#u32,719848548#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row096 : R0P.CopyRowExtension K := FJk_CopyStep.row pv096 pw096 cv096 cw096
def pv104 : Array field.QM31 2#usize := ⟨[⟨⟨1529592199#u32,939512102#u32⟩,⟨1892813288#u32,713926480#u32⟩⟩,⟨⟨1087439393#u32,418345866#u32⟩,⟨908823101#u32,1158127742#u32⟩⟩],by rfl⟩
def pw104 : Array field.QM31 2#usize := ⟨[⟨⟨2028592456#u32,1779702570#u32⟩,⟨1109692392#u32,115341833#u32⟩⟩,⟨⟨1632680025#u32,2076586574#u32⟩,⟨1230149388#u32,1330989904#u32⟩⟩],by rfl⟩
def cv104 : Array field.QM31 2#usize := ⟨[⟨⟨1250456655#u32,1516462296#u32⟩,⟨946237315#u32,290058242#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw104 : Array field.QM31 2#usize := ⟨[⟨⟨1004214114#u32,839247922#u32⟩,⟨537510115#u32,1414073497#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row104 : R0P.CopyRowExtension K := FJk_CopyStep.row pv104 pw104 cv104 cw104
def pv112 : Array field.QM31 2#usize := ⟨[⟨⟨157482942#u32,8807770#u32⟩,⟨289518694#u32,649612576#u32⟩⟩,⟨⟨1288924795#u32,1611927735#u32⟩,⟨174857482#u32,1814613508#u32⟩⟩],by rfl⟩
def pw112 : Array field.QM31 2#usize := ⟨[⟨⟨1279425883#u32,1322483871#u32⟩,⟨319092200#u32,1817277966#u32⟩⟩,⟨⟨189048173#u32,1514558906#u32⟩,⟨241285199#u32,588943302#u32⟩⟩],by rfl⟩
def cv112 : Array field.QM31 2#usize := ⟨[⟨⟨248659141#u32,1617560971#u32⟩,⟨333741060#u32,753615668#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw112 : Array field.QM31 2#usize := ⟨[⟨⟨666916189#u32,1199793991#u32⟩,⟨655467100#u32,525988369#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row112 : R0P.CopyRowExtension K := FJk_CopyStep.row pv112 pw112 cv112 cw112
def pv120 : Array field.QM31 2#usize := ⟨[⟨⟨1144733525#u32,2045498820#u32⟩,⟨726806580#u32,540347613#u32⟩⟩,⟨⟨515063573#u32,831417828#u32⟩,⟨408423875#u32,606063872#u32⟩⟩],by rfl⟩
def pw120 : Array field.QM31 2#usize := ⟨[⟨⟨507711536#u32,476259600#u32⟩,⟨1705247907#u32,1819499955#u32⟩⟩,⟨⟨587524920#u32,1063126833#u32⟩,⟨2050605501#u32,984970252#u32⟩⟩],by rfl⟩
def cv120 : Array field.QM31 2#usize := ⟨[⟨⟨947464706#u32,708875014#u32⟩,⟨1462455208#u32,1996948004#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw120 : Array field.QM31 2#usize := ⟨[⟨⟨234569169#u32,1388947572#u32⟩,⟨1114860797#u32,1103084561#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row120 : R0P.CopyRowExtension K := FJk_CopyStep.row pv120 pw120 cv120 cw120
def pv128 : Array field.QM31 2#usize := ⟨[⟨⟨474335870#u32,845123310#u32⟩,⟨1950629542#u32,988706615#u32⟩⟩,⟨⟨62110038#u32,1706454654#u32⟩,⟨1343031492#u32,872514658#u32⟩⟩],by rfl⟩
def pw128 : Array field.QM31 2#usize := ⟨[⟨⟨1048491692#u32,1874708803#u32⟩,⟨158381647#u32,684004677#u32⟩⟩,⟨⟨1632323091#u32,208472837#u32⟩,⟨393389122#u32,544885223#u32⟩⟩],by rfl⟩
def cv128 : Array field.QM31 2#usize := ⟨[⟨⟨1864332295#u32,1480856428#u32⟩,⟨1036737367#u32,131690713#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw128 : Array field.QM31 2#usize := ⟨[⟨⟨1575741125#u32,1708828095#u32⟩,⟨1999418912#u32,796495586#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row128 : R0P.CopyRowExtension K := FJk_CopyStep.row pv128 pw128 cv128 cw128
def pv136 : Array field.QM31 2#usize := ⟨[⟨⟨1628676053#u32,1215855421#u32⟩,⟨153871862#u32,803848263#u32⟩⟩,⟨⟨795930914#u32,1547406766#u32⟩,⟨158692259#u32,343738065#u32⟩⟩],by rfl⟩
def pw136 : Array field.QM31 2#usize := ⟨[⟨⟨1732723654#u32,1908661058#u32⟩,⟨615348906#u32,599770358#u32⟩⟩,⟨⟨1363704694#u32,936190941#u32⟩,⟨1949940567#u32,681585516#u32⟩⟩],by rfl⟩
def cv136 : Array field.QM31 2#usize := ⟨[⟨⟨1876269239#u32,1976840566#u32⟩,⟨926390041#u32,781343148#u32⟩⟩,⟨⟨1845786995#u32,1690483693#u32⟩,⟨393221370#u32,1334730373#u32⟩⟩],by rfl⟩
def cw136 : Array field.QM31 2#usize := ⟨[⟨⟨541146588#u32,1450476062#u32⟩,⟨935826902#u32,109221595#u32⟩⟩,⟨⟨1491117275#u32,1711861258#u32⟩,⟨908277363#u32,105086100#u32⟩⟩],by rfl⟩
def row136 : R0P.CopyRowExtension K := FJk_CopyStep.row pv136 pw136 cv136 cw136
def block00 : List R0P.CopyLink := (R0P.copyLinks.drop 0).take 8
def block01 : List R0P.CopyLink := (R0P.copyLinks.drop 8).take 8
def block02 : List R0P.CopyLink := (R0P.copyLinks.drop 16).take 8
def block03 : List R0P.CopyLink := (R0P.copyLinks.drop 24).take 8
def block04 : List R0P.CopyLink := (R0P.copyLinks.drop 32).take 8
def block05 : List R0P.CopyLink := (R0P.copyLinks.drop 40).take 8
def block06 : List R0P.CopyLink := (R0P.copyLinks.drop 48).take 8
def block07 : List R0P.CopyLink := (R0P.copyLinks.drop 56).take 8
def block08 : List R0P.CopyLink := (R0P.copyLinks.drop 64).take 8
def block09 : List R0P.CopyLink := (R0P.copyLinks.drop 72).take 8
def block10 : List R0P.CopyLink := (R0P.copyLinks.drop 80).take 8
def block11 : List R0P.CopyLink := (R0P.copyLinks.drop 88).take 8
def block12 : List R0P.CopyLink := (R0P.copyLinks.drop 96).take 8
def block13 : List R0P.CopyLink := (R0P.copyLinks.drop 104).take 8
def block14 : List R0P.CopyLink := (R0P.copyLinks.drop 112).take 8
def block15 : List R0P.CopyLink := (R0P.copyLinks.drop 120).take 8
def block16 : List R0P.CopyLink := (R0P.copyLinks.drop 128).take 8
theorem ext (x y : R0P.CopyRowExtension K)
    (hp : x.producerValues=y.producerValues) (hw : x.producerWeights=y.producerWeights)
    (hc : x.consumerValues=y.consumerValues) (hd : x.consumerWeights=y.consumerWeights) : x=y := by
  cases x
  cases y
  cases hp
  cases hw
  cases hc
  cases hd
  rfl
#print axioms ext
end AspisR1.JGn_CopyRows
end
