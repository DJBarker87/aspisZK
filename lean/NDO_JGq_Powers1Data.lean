import JGo_TX2_LoopChain
import JGo_TX2_Range
import RPz7_FIo_Install
import RPt_JFq_Alpha1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Powers1
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
abbrev S := Array E 4#usize × E × Usize
def x : E := FIo_Install.toE JFq_Alpha1.scalar
def p0 : E := FIo_Native.aspis_core.field.wide_exact.WideExact.ONE
def p1 : E := ⟨⟨⟨1923325677#u32,606708475#u32⟩,⟨390399940#u32,1424274113#u32⟩⟩,⟨⟨1600018693#u32,561365806#u32⟩,⟨1230057896#u32,509172918#u32⟩⟩⟩
def p2 : E := ⟨⟨⟨1514419440#u32,1736564810#u32⟩,⟨181080628#u32,286345715#u32⟩⟩,⟨⟨930336347#u32,1557920881#u32⟩,⟨1112027447#u32,1119882148#u32⟩⟩⟩
def p3 : E := ⟨⟨⟨2044702224#u32,2094227646#u32⟩,⟨1624815700#u32,1337450109#u32⟩⟩,⟨⟨201511810#u32,1222633759#u32⟩,⟨2011973780#u32,470984380#u32⟩⟩⟩
def a0 : Array E 4#usize := Array.repeat 4#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
def a1 : Array E 4#usize := Array.make 4#usize [p0,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a2 : Array E 4#usize := Array.make 4#usize [p0,p1,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a3 : Array E 4#usize := Array.make 4#usize [p0,p1,p2,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a4 : Array E 4#usize := Array.make 4#usize [p0,p1,p2,p3]
end AspisR1.JGq_Powers1
end
