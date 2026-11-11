import NDO_JFu_Q25InputBase
import NDO_JFu_FlatWindow
import NDO_JFr_EncodedCell
import NDO_JFu_DecodeAt
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
def chunks : List (List U8) := [p00,p01,p02,p03,p04,p05,p06,p07,p08,p09,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21,p22,p23,p24,p25,p26,p27,p28,p29,p30,p31,p32,p33,p34,p35,p36,p37,p38,p39,p40,p41,p42,p43,p44,p45,p46,p47,p48,p49,p50,p51,p52,p53,p54,p55,p56,p57,p58,p59,p60,p61,p62,p63,p64,p65,p66,p67,p68,p69,p70,p71,p72,p73,p74,p75,p76,p77,p78,p79,p80,p81,p82,p83,p84,p85,p86,p87,p88,p89,p90,p91,p92,p93,p94,p95,p96,p97,p98,p99,p100,p101,p102,p103,p104,p105,p106,p107,p108,p109,p110,p111,p112,p113,p114,p115]
theorem lengths : ∀ c ∈ chunks,c.length=32 := by
  intro c hc
  simp only [chunks,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58|h59|h60|h61|h62|h63|h64|h65|h66|h67|h68|h69|h70|h71|h72|h73|h74|h75|h76|h77|h78|h79|h80|h81|h82|h83|h84|h85|h86|h87|h88|h89|h90|h91|h92|h93|h94|h95|h96|h97|h98|h99|h100|h101|h102|h103|h104|h105|h106|h107|h108|h109|h110|h111|h112|h113|h114|h115
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
#print axioms lengths
def q000 : aspis_core.field.QM31 := ⟨⟨895840419#u32,1743872265#u32⟩,⟨1526120590#u32,1740529654#u32⟩⟩
def q001 : aspis_core.field.QM31 := ⟨⟨411163290#u32,1228838864#u32⟩,⟨737737725#u32,1890800270#u32⟩⟩
def q002 : aspis_core.field.QM31 := ⟨⟨1720806990#u32,153453703#u32⟩,⟨1189446421#u32,1273113942#u32⟩⟩
def q003 : aspis_core.field.QM31 := ⟨⟨2016242433#u32,304235430#u32⟩,⟨23947119#u32,1370335083#u32⟩⟩
def q004 : aspis_core.field.QM31 := ⟨⟨1711691533#u32,2021326282#u32⟩,⟨1084550569#u32,127393187#u32⟩⟩
def q005 : aspis_core.field.QM31 := ⟨⟨942867677#u32,1498249371#u32⟩,⟨1225079568#u32,297276283#u32⟩⟩
def q006 : aspis_core.field.QM31 := ⟨⟨1473140560#u32,769915656#u32⟩,⟨1408962939#u32,1473228395#u32⟩⟩
def q007 : aspis_core.field.QM31 := ⟨⟨1040147431#u32,1377995740#u32⟩,⟨2082867445#u32,1768050451#u32⟩⟩
def q008 : aspis_core.field.QM31 := ⟨⟨917772608#u32,368757995#u32⟩,⟨161265716#u32,974021803#u32⟩⟩
def q009 : aspis_core.field.QM31 := ⟨⟨1193339236#u32,304810453#u32⟩,⟨1614109814#u32,995173725#u32⟩⟩
def q010 : aspis_core.field.QM31 := ⟨⟨1472072814#u32,1318444254#u32⟩,⟨509283412#u32,815376212#u32⟩⟩
def q011 : aspis_core.field.QM31 := ⟨⟨242230642#u32,1039194959#u32⟩,⟨1378190672#u32,1394930988#u32⟩⟩
def q012 : aspis_core.field.QM31 := ⟨⟨1184698583#u32,2001007128#u32⟩,⟨1675877739#u32,1932030996#u32⟩⟩
def q013 : aspis_core.field.QM31 := ⟨⟨2133223835#u32,1223920141#u32⟩,⟨1328205682#u32,106060940#u32⟩⟩
def q014 : aspis_core.field.QM31 := ⟨⟨1487603159#u32,164220437#u32⟩,⟨557631820#u32,201034697#u32⟩⟩
def q015 : aspis_core.field.QM31 := ⟨⟨307586032#u32,12172507#u32⟩,⟨299357599#u32,1180899211#u32⟩⟩
def q016 : aspis_core.field.QM31 := ⟨⟨777430110#u32,1200214211#u32⟩,⟨1406033507#u32,1158665849#u32⟩⟩
def q017 : aspis_core.field.QM31 := ⟨⟨1763086781#u32,1383601703#u32⟩,⟨1872838129#u32,688630383#u32⟩⟩
def q018 : aspis_core.field.QM31 := ⟨⟨904729708#u32,334308431#u32⟩,⟨2062890506#u32,1137320935#u32⟩⟩
def q019 : aspis_core.field.QM31 := ⟨⟨558034002#u32,1614406535#u32⟩,⟨2012485711#u32,996744770#u32⟩⟩
def q020 : aspis_core.field.QM31 := ⟨⟨641445097#u32,1008312219#u32⟩,⟨1434961672#u32,1222904335#u32⟩⟩
def q021 : aspis_core.field.QM31 := ⟨⟨2048860391#u32,1129803582#u32⟩,⟨542715458#u32,911373527#u32⟩⟩
def q022 : aspis_core.field.QM31 := ⟨⟨1337113852#u32,1125877988#u32⟩,⟨1727680716#u32,1798058125#u32⟩⟩
def q023 : aspis_core.field.QM31 := ⟨⟨771312530#u32,508397176#u32⟩,⟨1735965987#u32,1761927343#u32⟩⟩
def q024 : aspis_core.field.QM31 := ⟨⟨1914354884#u32,1318016785#u32⟩,⟨123528860#u32,1320243372#u32⟩⟩
def q025 : aspis_core.field.QM31 := ⟨⟨716947928#u32,1582242406#u32⟩,⟨1422667174#u32,1320016847#u32⟩⟩
def q026 : aspis_core.field.QM31 := ⟨⟨45908713#u32,568527425#u32⟩,⟨312784901#u32,132689328#u32⟩⟩
def q027 : aspis_core.field.QM31 := ⟨⟨597243082#u32,1854646086#u32⟩,⟨15560709#u32,24648990#u32⟩⟩
def q028 : aspis_core.field.QM31 := ⟨⟨1244987732#u32,1745681871#u32⟩,⟨1859417396#u32,45129235#u32⟩⟩
def q029 : aspis_core.field.QM31 := ⟨⟨1432598223#u32,745421881#u32⟩,⟨1140322637#u32,1471902095#u32⟩⟩
def q030 : aspis_core.field.QM31 := ⟨⟨1990931194#u32,1546558306#u32⟩,⟨278742470#u32,637050875#u32⟩⟩
def q031 : aspis_core.field.QM31 := ⟨⟨1528325264#u32,828818603#u32⟩,⟨1914646583#u32,1066511680#u32⟩⟩
def q032 : aspis_core.field.QM31 := ⟨⟨60204167#u32,398073086#u32⟩,⟨1521287092#u32,1777863693#u32⟩⟩
def q033 : aspis_core.field.QM31 := ⟨⟨533381627#u32,565777841#u32⟩,⟨778831583#u32,627124531#u32⟩⟩
def q034 : aspis_core.field.QM31 := ⟨⟨1637743706#u32,1857801312#u32⟩,⟨1493832046#u32,1611275617#u32⟩⟩
def q035 : aspis_core.field.QM31 := ⟨⟨1193564563#u32,1939605589#u32⟩,⟨651842249#u32,778239663#u32⟩⟩
def q036 : aspis_core.field.QM31 := ⟨⟨784876307#u32,878521957#u32⟩,⟨426347277#u32,1735240767#u32⟩⟩
def q037 : aspis_core.field.QM31 := ⟨⟨535705404#u32,1694443561#u32⟩,⟨371351490#u32,1603519108#u32⟩⟩
def q038 : aspis_core.field.QM31 := ⟨⟨1775631064#u32,371035090#u32⟩,⟨1870483878#u32,1017426431#u32⟩⟩
def q039 : aspis_core.field.QM31 := ⟨⟨1690300196#u32,407931285#u32⟩,⟨1225658534#u32,1903481654#u32⟩⟩
def q040 : aspis_core.field.QM31 := ⟨⟨392540597#u32,995017038#u32⟩,⟨1354967605#u32,1366225676#u32⟩⟩
def q041 : aspis_core.field.QM31 := ⟨⟨1632526252#u32,1269689629#u32⟩,⟨1090592280#u32,419712420#u32⟩⟩
def q042 : aspis_core.field.QM31 := ⟨⟨489383738#u32,464942166#u32⟩,⟨1280325266#u32,1810587088#u32⟩⟩
def q043 : aspis_core.field.QM31 := ⟨⟨385263138#u32,86719098#u32⟩,⟨493573875#u32,143150622#u32⟩⟩
def q044 : aspis_core.field.QM31 := ⟨⟨428062536#u32,939595594#u32⟩,⟨920072514#u32,649028873#u32⟩⟩
def q045 : aspis_core.field.QM31 := ⟨⟨1303641095#u32,1139775942#u32⟩,⟨864837936#u32,2048561767#u32⟩⟩
def q046 : aspis_core.field.QM31 := ⟨⟨793059060#u32,690771535#u32⟩,⟨1157366659#u32,586449080#u32⟩⟩
def q047 : aspis_core.field.QM31 := ⟨⟨1346359144#u32,1792273344#u32⟩,⟨1428821998#u32,337067283#u32⟩⟩
def q048 : aspis_core.field.QM31 := ⟨⟨1250234932#u32,349771901#u32⟩,⟨127675431#u32,1243693311#u32⟩⟩
def q049 : aspis_core.field.QM31 := ⟨⟨1259199971#u32,277916594#u32⟩,⟨658444469#u32,411784885#u32⟩⟩
def q050 : aspis_core.field.QM31 := ⟨⟨1624446077#u32,1861455402#u32⟩,⟨1873485467#u32,239655088#u32⟩⟩
def q051 : aspis_core.field.QM31 := ⟨⟨1326916475#u32,1797374536#u32⟩,⟨1881454716#u32,1960755144#u32⟩⟩
def q052 : aspis_core.field.QM31 := ⟨⟨506500631#u32,1255564298#u32⟩,⟨1934738953#u32,1409188068#u32⟩⟩
def q053 : aspis_core.field.QM31 := ⟨⟨971619853#u32,1268289577#u32⟩,⟨137760591#u32,707954802#u32⟩⟩
def q054 : aspis_core.field.QM31 := ⟨⟨535047991#u32,1295723902#u32⟩,⟨1455604958#u32,1771566530#u32⟩⟩
def q055 : aspis_core.field.QM31 := ⟨⟨191316229#u32,1484974523#u32⟩,⟨1010895800#u32,2099702710#u32⟩⟩
def q056 : aspis_core.field.QM31 := ⟨⟨1319734996#u32,1341353101#u32⟩,⟨557628492#u32,2011496108#u32⟩⟩
def q057 : aspis_core.field.QM31 := ⟨⟨2125594827#u32,1014435860#u32⟩,⟨407354425#u32,1661187187#u32⟩⟩
def q058 : aspis_core.field.QM31 := ⟨⟨75412604#u32,1715744439#u32⟩,⟨785846381#u32,1828497843#u32⟩⟩
def q059 : aspis_core.field.QM31 := ⟨⟨1249415208#u32,1315138952#u32⟩,⟨2143447507#u32,2045257038#u32⟩⟩
def q060 : aspis_core.field.QM31 := ⟨⟨1487872547#u32,1866497312#u32⟩,⟨1752013472#u32,1034272649#u32⟩⟩
def q061 : aspis_core.field.QM31 := ⟨⟨187021288#u32,1146093002#u32⟩,⟨2072298071#u32,449705109#u32⟩⟩
def q062 : aspis_core.field.QM31 := ⟨⟨31738678#u32,788884924#u32⟩,⟨120594647#u32,1250853884#u32⟩⟩
def q063 : aspis_core.field.QM31 := ⟨⟨1681766977#u32,1275228902#u32⟩,⟨354977376#u32,836108887#u32⟩⟩
def q064 : aspis_core.field.QM31 := ⟨⟨1333993764#u32,1659471999#u32⟩,⟨1585324601#u32,328582706#u32⟩⟩
def q065 : aspis_core.field.QM31 := ⟨⟨540230699#u32,1578135531#u32⟩,⟨2050747800#u32,564544670#u32⟩⟩
def q066 : aspis_core.field.QM31 := ⟨⟨367839275#u32,1018589093#u32⟩,⟨1026725693#u32,1439130447#u32⟩⟩
def q067 : aspis_core.field.QM31 := ⟨⟨343159267#u32,1258471129#u32⟩,⟨684291023#u32,347777375#u32⟩⟩
def q068 : aspis_core.field.QM31 := ⟨⟨1649081545#u32,1636205145#u32⟩,⟨802848518#u32,1911155209#u32⟩⟩
def q069 : aspis_core.field.QM31 := ⟨⟨1907129452#u32,1588943284#u32⟩,⟨1992633096#u32,1377648539#u32⟩⟩
def q070 : aspis_core.field.QM31 := ⟨⟨688326283#u32,427788954#u32⟩,⟨871723233#u32,293714383#u32⟩⟩
def q071 : aspis_core.field.QM31 := ⟨⟨251756188#u32,1383769139#u32⟩,⟨570727415#u32,1355721239#u32⟩⟩
def q072 : aspis_core.field.QM31 := ⟨⟨1303077176#u32,1384193908#u32⟩,⟨1365944013#u32,943527902#u32⟩⟩
def q073 : aspis_core.field.QM31 := ⟨⟨1835324278#u32,1675384494#u32⟩,⟨1900037518#u32,585067253#u32⟩⟩
def q074 : aspis_core.field.QM31 := ⟨⟨243461483#u32,104342301#u32⟩,⟨1094733627#u32,2021295803#u32⟩⟩
def q075 : aspis_core.field.QM31 := ⟨⟨333230641#u32,914913933#u32⟩,⟨2090426540#u32,1383044945#u32⟩⟩
def q076 : aspis_core.field.QM31 := ⟨⟨1665327798#u32,117692881#u32⟩,⟨407318215#u32,1320397883#u32⟩⟩
def q077 : aspis_core.field.QM31 := ⟨⟨717285309#u32,102421007#u32⟩,⟨2047106705#u32,2064916164#u32⟩⟩
def q078 : aspis_core.field.QM31 := ⟨⟨1028410864#u32,1669488000#u32⟩,⟨422640695#u32,1157857866#u32⟩⟩
def q079 : aspis_core.field.QM31 := ⟨⟨1352933961#u32,1890232075#u32⟩,⟨1735304749#u32,612527630#u32⟩⟩
def q080 : aspis_core.field.QM31 := ⟨⟨748470159#u32,856214076#u32⟩,⟨900199640#u32,523049696#u32⟩⟩
def q081 : aspis_core.field.QM31 := ⟨⟨842870410#u32,208426141#u32⟩,⟨1131532451#u32,881687262#u32⟩⟩
def q082 : aspis_core.field.QM31 := ⟨⟨721794136#u32,887339066#u32⟩,⟨571582431#u32,1556468480#u32⟩⟩
def q083 : aspis_core.field.QM31 := ⟨⟨155886864#u32,2069372766#u32⟩,⟨1840000253#u32,1115764109#u32⟩⟩
def q084 : aspis_core.field.QM31 := ⟨⟨710741989#u32,1711076177#u32⟩,⟨1143404576#u32,842449791#u32⟩⟩
def q085 : aspis_core.field.QM31 := ⟨⟨1928616425#u32,427703115#u32⟩,⟨1834628179#u32,1731302430#u32⟩⟩
def q086 : aspis_core.field.QM31 := ⟨⟨1406202439#u32,1445676843#u32⟩,⟨2079381110#u32,214436913#u32⟩⟩
def q087 : aspis_core.field.QM31 := ⟨⟨541882953#u32,1714294222#u32⟩,⟨1093764463#u32,943394672#u32⟩⟩
def q088 : aspis_core.field.QM31 := ⟨⟨1014150042#u32,651453034#u32⟩,⟨2071778460#u32,2055240441#u32⟩⟩
def q089 : aspis_core.field.QM31 := ⟨⟨167402634#u32,359394276#u32⟩,⟨452573933#u32,2124747794#u32⟩⟩
def q090 : aspis_core.field.QM31 := ⟨⟨2051428579#u32,257640434#u32⟩,⟨1765683211#u32,1725992266#u32⟩⟩
def q091 : aspis_core.field.QM31 := ⟨⟨2141033239#u32,1698475133#u32⟩,⟨968041499#u32,1905592117#u32⟩⟩
def q092 : aspis_core.field.QM31 := ⟨⟨2137054534#u32,1479018300#u32⟩,⟨866915547#u32,538675723#u32⟩⟩
def q093 : aspis_core.field.QM31 := ⟨⟨1830488581#u32,1700832879#u32⟩,⟨852037407#u32,1643462843#u32⟩⟩
def q094 : aspis_core.field.QM31 := ⟨⟨1762288774#u32,200753349#u32⟩,⟨2067515889#u32,1571101725#u32⟩⟩
def q095 : aspis_core.field.QM31 := ⟨⟨1610096916#u32,688246391#u32⟩,⟨2097095278#u32,1793916946#u32⟩⟩
def q096 : aspis_core.field.QM31 := ⟨⟨953884882#u32,439314282#u32⟩,⟨1748163613#u32,475943774#u32⟩⟩
def q097 : aspis_core.field.QM31 := ⟨⟨821780999#u32,112978469#u32⟩,⟨1564529359#u32,636790122#u32⟩⟩
def q098 : aspis_core.field.QM31 := ⟨⟨1704079489#u32,808993607#u32⟩,⟨1222555150#u32,224129915#u32⟩⟩
def q099 : aspis_core.field.QM31 := ⟨⟨492462609#u32,868495389#u32⟩,⟨918891111#u32,1882666640#u32⟩⟩
def q100 : aspis_core.field.QM31 := ⟨⟨1765991481#u32,238378020#u32⟩,⟨767171733#u32,1674880684#u32⟩⟩
def q101 : aspis_core.field.QM31 := ⟨⟨1219629111#u32,890438173#u32⟩,⟨1167316788#u32,1276443835#u32⟩⟩
def q102 : aspis_core.field.QM31 := ⟨⟨1079479290#u32,2140776234#u32⟩,⟨407387051#u32,693395276#u32⟩⟩
def q103 : aspis_core.field.QM31 := ⟨⟨782648654#u32,1671940894#u32⟩,⟨679717521#u32,1638039155#u32⟩⟩
def q104 : aspis_core.field.QM31 := ⟨⟨123307147#u32,926741693#u32⟩,⟨510013614#u32,1292317050#u32⟩⟩
def q105 : aspis_core.field.QM31 := ⟨⟨323861066#u32,1228532067#u32⟩,⟨1954688486#u32,1093269780#u32⟩⟩
def q106 : aspis_core.field.QM31 := ⟨⟨1869402348#u32,1260290307#u32⟩,⟨1319578856#u32,371498722#u32⟩⟩
def q107 : aspis_core.field.QM31 := ⟨⟨1409799320#u32,1407480725#u32⟩,⟨274854004#u32,1006279694#u32⟩⟩
def q108 : aspis_core.field.QM31 := ⟨⟨648658425#u32,1529907857#u32⟩,⟨881248310#u32,186476071#u32⟩⟩
def q109 : aspis_core.field.QM31 := ⟨⟨2111129101#u32,1384678060#u32⟩,⟨1780633621#u32,697580186#u32⟩⟩
def q110 : aspis_core.field.QM31 := ⟨⟨340777829#u32,1157619152#u32⟩,⟨1918302603#u32,2091788871#u32⟩⟩
def q111 : aspis_core.field.QM31 := ⟨⟨235809539#u32,491848512#u32⟩,⟨297471099#u32,1557049411#u32⟩⟩
def q112 : aspis_core.field.QM31 := ⟨⟨1839437198#u32,1981008225#u32⟩,⟨644939808#u32,1901897072#u32⟩⟩
def q113 : aspis_core.field.QM31 := ⟨⟨188295548#u32,1669737704#u32⟩,⟨2047846072#u32,1681524573#u32⟩⟩
def q114 : aspis_core.field.QM31 := ⟨⟨921097879#u32,1532734766#u32⟩,⟨1347616134#u32,1297812131#u32⟩⟩
def q115 : aspis_core.field.QM31 := ⟨⟨2044434832#u32,962345221#u32⟩,⟨696906885#u32,1425710698#u32⟩⟩
def a0 : Array aspis_core.field.QM31 29#usize := ⟨[q000,q001,q002,q003,q004,q005,q006,q007,q008,q009,q010,q011,q012,q013,q014,q015,q016,q017,q018,q019,q020,q021,q022,q023,q024,q025,q026,q027,q028],by rfl⟩
def a1 : Array aspis_core.field.QM31 29#usize := ⟨[q029,q030,q031,q032,q033,q034,q035,q036,q037,q038,q039,q040,q041,q042,q043,q044,q045,q046,q047,q048,q049,q050,q051,q052,q053,q054,q055,q056,q057],by rfl⟩
def a2 : Array aspis_core.field.QM31 29#usize := ⟨[q058,q059,q060,q061,q062,q063,q064,q065,q066,q067,q068,q069,q070,q071,q072,q073,q074,q075,q076,q077,q078,q079,q080,q081,q082,q083,q084,q085,q086],by rfl⟩
def a3 : Array aspis_core.field.QM31 29#usize := ⟨[q087,q088,q089,q090,q091,q092,q093,q094,q095,q096,q097,q098,q099,q100,q101,q102,q103,q104,q105,q106,q107,q108,q109,q110,q111,q112,q113,q114,q115],by rfl⟩
def claims : ClaimsUnrolledFinish.MainClaims := ⟨[a0,a1,a2],by rfl⟩
end AspisR1.JFu_ClaimsData
