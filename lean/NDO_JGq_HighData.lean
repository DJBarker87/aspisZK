import NDO_JGq_SharedPartials
import NDO_JGq_Scale0
import NDO_JGq_Scale1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_High
open Aeneas Aeneas.Std Result ControlFlow
def row0 := FIn_WeightsInstall.mapArray FIo_Install.toQ JGo_TX2_WeightData.f04
def d0_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨Array.make 4#usize [0#u64,0#u64,0#u64,0#u64]⟩,⟨Array.make 4#usize [0#u64,0#u64,0#u64,0#u64]⟩,0#usize⟩
def c0_0 : FIo_Install.NQ := ⟨⟨743720934#u32,1544417890#u32⟩,⟨1464892848#u32,691478626#u32⟩⟩
def d0_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨Array.make 4#usize [1793133229#u64,1384419801#u64,3177356320#u64,3641592195#u64]⟩,⟨Array.make 4#usize [4124566208#u64,1434217076#u64,4937861329#u64,2608245257#u64]⟩,1#usize⟩
def c0_1 : FIo_Install.NQ := ⟨⟨2140563136#u32,227469088#u32⟩,⟨1856812576#u32,1333918312#u32⟩⟩
def d0_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨Array.make 4#usize [5877018712#u64,3619767704#u64,9605950301#u64,7498052907#u64]⟩,⟨Array.make 4#usize [8593147219#u64,3323134416#u64,10162061962#u64,5649012494#u64]⟩,2#usize⟩
def c0_2 : FIo_Install.NQ := ⟨⟨1527381945#u32,1767468172#u32⟩,⟨494709614#u32,117617008#u32⟩⟩
def d0_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨Array.make 4#usize [9073745041#u64,6997571242#u64,17126195228#u64,11166413294#u64]⟩,⟨Array.make 4#usize [11634359984#u64,5764120637#u64,17010486870#u64,7689431861#u64]⟩,3#usize⟩
def c0_3 : FIo_Install.NQ := ⟨⟨2030784927#u32,755612144#u32⟩,⟨478552256#u32,4469701#u32⟩⟩
def d0_4 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨Array.make 4#usize [13263307287#u64,10585959222#u64,23107971818#u64,13460492333#u64]⟩,⟨Array.make 4#usize [15368103437#u64,8069512823#u64,23795571832#u64,10386177843#u64]⟩,4#usize⟩
def high0 : FIo_Install.NE := ⟨⟨⟨378405405#u32,1996024634#u32⟩,⟨1633135348#u32,575590451#u32⟩⟩,⟨⟨335717908#u32,1627061882#u32⟩,⟨173251715#u32,1796243255#u32⟩⟩⟩
def row2 := FIn_WeightsInstall.mapArray FIo_Install.toQ JGo_TX2_WeightData.f24
def d2_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨Array.make 4#usize [0#u64,0#u64,0#u64,0#u64]⟩,⟨Array.make 4#usize [0#u64,0#u64,0#u64,0#u64]⟩,0#usize⟩
def c2_0 : FIo_Install.NQ := ⟨⟨2030784927#u32,755612144#u32⟩,⟨478552256#u32,4469701#u32⟩⟩
def d2_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨Array.make 4#usize [2147111233#u64,1190453426#u64,5988387821#u64,2555067660#u64]⟩,⟨Array.make 4#usize [4001825247#u64,1061028343#u64,5340582496#u64,3724522008#u64]⟩,1#usize⟩
def c2_1 : FIo_Install.NQ := ⟨⟨1527381945#u32,1767468172#u32⟩,⟨494709614#u32,117617008#u32⟩⟩
def d2_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨Array.make 4#usize [4943278829#u64,5085372382#u64,12692789357#u64,4139018142#u64]⟩,⟨Array.make 4#usize [7936755444#u64,4035412347#u64,10792134507#u64,6350640923#u64]⟩,2#usize⟩
def c2_2 : FIo_Install.NQ := ⟨⟨2140563136#u32,227469088#u32⟩,⟨1856812576#u32,1333918312#u32⟩⟩
def d2_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨Array.make 4#usize [9750237316#u64,7965645420#u64,19347916084#u64,6613793934#u64]⟩,⟨Array.make 4#usize [12678483203#u64,6133515459#u64,17704323719#u64,8273029379#u64]⟩,3#usize⟩
def c2_3 : FIo_Install.NQ := ⟨⟨743720934#u32,1544417890#u32⟩,⟨1464892848#u32,691478626#u32⟩⟩
def d2_4 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨Array.make 4#usize [12509247473#u64,10510451710#u64,26010360790#u64,9343789557#u64]⟩,⟨Array.make 4#usize [16490252496#u64,7674903138#u64,23760836081#u64,11931399147#u64]⟩,4#usize⟩
def high2 : FIo_Install.NE := ⟨⟨⟨1771829238#u32,1920517122#u32⟩,⟨240557026#u32,753854969#u32⟩⟩,⟨⟨1457866967#u32,1232452197#u32⟩,⟨138515964#u32,1193980912#u32⟩⟩⟩
def scale : FIo_Install.NE := ⟨⟨⟨1909620449#u32,1071256392#u32⟩,⟨680319314#u32,625761817#u32⟩⟩,⟨⟨1260323604#u32,480533211#u32⟩,⟨1358158431#u32,1333393448#u32⟩⟩⟩
def value0 : FIo_Install.NE := ⟨⟨⟨1828596887#u32,1448284290#u32⟩,⟨1797610665#u32,822447794#u32⟩⟩,⟨⟨1532748302#u32,2051626710#u32⟩,⟨404454155#u32,1390107907#u32⟩⟩⟩
def value2 : FIo_Install.NE := ⟨⟨⟨720061919#u32,797282784#u32⟩,⟨215960079#u32,1779137459#u32⟩⟩,⟨⟨788362159#u32,1899245347#u32⟩,⟨1207483836#u32,659524539#u32⟩⟩⟩
end AspisR1.JGq_High
end
