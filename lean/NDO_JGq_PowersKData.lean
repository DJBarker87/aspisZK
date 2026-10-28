import JGo_TX2_LoopChain
import JGo_TX2_Range
import RPz7_FIo_Install
import RPt_JFq_Kappa
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PowersK
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
abbrev S := Array E 7#usize × E × Usize
def x : E := FIo_Install.toE JFq_Kappa.scalar
def p0 : E := FIo_Native.aspis_core.field.wide_exact.WideExact.ONE
def p1 : E := ⟨⟨⟨1116662073#u32,1579954339#u32⟩,⟨1176243488#u32,728698552#u32⟩⟩,⟨⟨640606056#u32,1197281433#u32⟩,⟨2141139535#u32,1224613133#u32⟩⟩⟩
def p2 : E := ⟨⟨⟨194086607#u32,1888419081#u32⟩,⟨1301861674#u32,1187144623#u32⟩⟩,⟨⟨855257644#u32,590989944#u32⟩,⟨1958695353#u32,1064062444#u32⟩⟩⟩
def p3 : E := ⟨⟨⟨1266306440#u32,1524792638#u32⟩,⟨36588852#u32,1044096672#u32⟩⟩,⟨⟨2018106446#u32,381171209#u32⟩,⟨1489892152#u32,1479239577#u32⟩⟩⟩
def p4 : E := ⟨⟨⟨2006370403#u32,841359646#u32⟩,⟨376899686#u32,2013808952#u32⟩⟩,⟨⟨1241193111#u32,1543519322#u32⟩,⟨400137173#u32,1242945666#u32⟩⟩⟩
def p5 : E := ⟨⟨⟨1376226683#u32,1712321640#u32⟩,⟨190663200#u32,1810133619#u32⟩⟩,⟨⟨1051832243#u32,1950132196#u32⟩,⟨483065632#u32,20684665#u32⟩⟩⟩
def p6 : E := ⟨⟨⟨1669677601#u32,1938847927#u32⟩,⟨2006801723#u32,1268458862#u32⟩⟩,⟨⟨480042823#u32,1027734773#u32⟩,⟨1137142088#u32,282041615#u32⟩⟩⟩
def a0 : Array E 7#usize := Array.repeat 7#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
def a1 : Array E 7#usize := Array.make 7#usize [p0,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a2 : Array E 7#usize := Array.make 7#usize [p0,p1,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a3 : Array E 7#usize := Array.make 7#usize [p0,p1,p2,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a4 : Array E 7#usize := Array.make 7#usize [p0,p1,p2,p3,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a5 : Array E 7#usize := Array.make 7#usize [p0,p1,p2,p3,p4,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a6 : Array E 7#usize := Array.make 7#usize [p0,p1,p2,p3,p4,p5,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a7 : Array E 7#usize := Array.make 7#usize [p0,p1,p2,p3,p4,p5,p6]
end AspisR1.JGq_PowersK
end
