import NDO_JGo_TX2_WeightData
import JGo_TX2_Range
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Common
open Aeneas Aeneas.Std Result ControlFlow
abbrev Q := FIo_Install.NQ
def w := FIo_Install.toWeights JGo_TX2_WeightData.value
def c0 : Q := ⟨⟨380881637#u32,145563202#u32⟩,⟨2011695329#u32,742695209#u32⟩⟩
def c1 : Q := ⟨⟨194077276#u32,1148957520#u32⟩,⟨1035208204#u32,1811440404#u32⟩⟩
def c2 : Q := ⟨⟨718205332#u32,782514565#u32⟩,⟨1152266664#u32,1393435499#u32⟩⟩
def c3 : Q := ⟨⟨810434499#u32,1655301527#u32⟩,⟨155372855#u32,453222201#u32⟩⟩
def c4 : Q := ⟨⟨753885871#u32,525997631#u32⟩,⟨1801443545#u32,653604672#u32⟩⟩
def c5 : Q := ⟨⟨1541513226#u32,599475538#u32⟩,⟨2010446897#u32,1402840225#u32⟩⟩
def c6 : Q := ⟨⟨389918185#u32,574083392#u32⟩,⟨1002695834#u32,876758374#u32⟩⟩
def c7 : Q := ⟨⟨1199135935#u32,506063940#u32⟩,⟨1707689654#u32,3257774#u32⟩⟩
def c8 : Q := ⟨⟨843717662#u32,1385126792#u32⟩,⟨512838471#u32,1539443311#u32⟩⟩
def c9 : Q := ⟨⟨1311375113#u32,1601412301#u32⟩,⟨396333221#u32,23917413#u32⟩⟩
def c10 : Q := ⟨⟨997342743#u32,1238035817#u32⟩,⟨839343206#u32,1566121058#u32⟩⟩
def c11 : Q := ⟨⟨1303673184#u32,1370095683#u32⟩,⟨584840852#u32,996902858#u32⟩⟩
def c12 : Q := ⟨⟨1375680242#u32,646285125#u32⟩,⟨1357901755#u32,1834842386#u32⟩⟩
def c13 : Q := ⟨⟨1082378868#u32,46823097#u32⟩,⟨574664235#u32,276075281#u32⟩⟩
def c14 : Q := ⟨⟨172000223#u32,2135947181#u32⟩,⟨1290422964#u32,1111958823#u32⟩⟩
def c15 : Q := ⟨⟨1958165534#u32,670702218#u32⟩,⟨746705490#u32,345870041#u32⟩⟩
def a0 : Array Q 16#usize := Array.make 16#usize [FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a1 : Array Q 16#usize := Array.make 16#usize [c0,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a2 : Array Q 16#usize := Array.make 16#usize [c0,c1,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a3 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a4 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a5 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a6 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a7 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,c6,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a8 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,c6,c7,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a9 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,c6,c7,c8,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a10 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a11 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a12 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a13 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a14 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,FIo_Native.aspis_core.field.QM31.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
def a15 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,FIo_Native.aspis_core.field.QM31.ZERO]
def a16 : Array Q 16#usize := Array.make 16#usize [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15]
end AspisR1.JGq_Common
end
