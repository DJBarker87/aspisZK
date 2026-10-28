import JGo_TX2_LoopChain
import JGo_TX2_Range
import RPz7_FIo_Install
import RPt_JFq_Alpha0
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Powers0
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
abbrev S := Array E 4#usize × E × Usize
def x : E := FIo_Install.toE JFq_Alpha0.scalar
def p0 : E := FIo_Native.aspis_core.field.wide_exact.WideExact.ONE
def p1 : E := ⟨⟨⟨492967452#u32,709301790#u32⟩,⟨1617612614#u32,599334322#u32⟩⟩,⟨⟨1668486716#u32,1253062525#u32⟩,⟨341779229#u32,880523595#u32⟩⟩⟩
def p2 : E := ⟨⟨⟨657610837#u32,2127412646#u32⟩,⟨1649786800#u32,1006155519#u32⟩⟩,⟨⟨648141272#u32,968125172#u32⟩,⟨1639389454#u32,1975567393#u32⟩⟩⟩
def p3 : E := ⟨⟨⟨2080180520#u32,531029346#u32⟩,⟨345389240#u32,34874221#u32⟩⟩,⟨⟨912529348#u32,470194998#u32⟩,⟨1054942646#u32,199322625#u32⟩⟩⟩
def a0 : Array E 4#usize := Array.repeat 4#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
def a1 : Array E 4#usize := Array.make 4#usize [p0,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a2 : Array E 4#usize := Array.make 4#usize [p0,p1,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a3 : Array E 4#usize := Array.make 4#usize [p0,p1,p2,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a4 : Array E 4#usize := Array.make 4#usize [p0,p1,p2,p3]
end AspisR1.JGq_Powers0
end
