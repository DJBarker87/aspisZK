import NDO_JGs_LibraScale0
import NDO_JGs_LibraScale1
import NDO_JGs_LibraTerms0
import NDO_JGs_LibraTerms1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraEnd
open Aeneas Aeneas.Std Result ControlFlow
def a : FIo_Install.NE := ⟨⟨⟨2054192100#u32,1021028348#u32⟩,⟨669841454#u32,979138077#u32⟩⟩,⟨⟨564962388#u32,70044644#u32⟩,⟨172057055#u32,786021676#u32⟩⟩⟩
theorem call_a : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGs_LibraScale0.value JGs_Libra.sum0_4=ok a := by with_unfolding_all rfl
#print axioms call_a
def b : FIo_Install.NE := ⟨⟨⟨1561428821#u32,1570105545#u32⟩,⟨873028388#u32,1326391841#u32⟩⟩,⟨⟨196137616#u32,975329534#u32⟩,⟨1897313711#u32,1188399164#u32⟩⟩⟩
theorem call_b : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGs_LibraScale0.value JGs_Libra.sum0_3=ok b := by with_unfolding_all rfl
#print axioms call_b
def c : FIo_Install.NE := ⟨⟨⟨1110200538#u32,1201855747#u32⟩,⟨951354503#u32,80925383#u32⟩⟩,⟨⟨2007515281#u32,982110712#u32⟩,⟨1649156486#u32,1315539773#u32⟩⟩⟩
theorem call_c : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 b JGs_Libra.q0_16=ok c := by with_unfolding_all rfl
#print axioms call_c
def d : FIo_Install.NE := ⟨⟨⟨1017702331#u32,1762289854#u32⟩,⟨97599985#u32,892939440#u32⟩⟩,⟨⟨936875585#u32,1214083275#u32⟩,⟨307514474#u32,1201035053#u32⟩⟩⟩
theorem call_d : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 JGq_Powers1.p1 FIo_Native.weights.QUARTER=ok d := by with_unfolding_all rfl
#print axioms call_d
def e : FIo_Install.NE := ⟨⟨⟨1143992295#u32,2008619328#u32⟩,⟨1241790070#u32,835896512#u32⟩⟩,⟨⟨1064311272#u32,353419686#u32⟩,⟨1103161248#u32,1512419874#u32⟩⟩⟩
theorem call_e : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGs_LibraScale1.value d=ok e := by with_unfolding_all rfl
#print axioms call_e
def f : FIo_Install.NE := ⟨⟨⟨106709186#u32,1062991428#u32⟩,⟨45660926#u32,916821895#u32⟩⟩,⟨⟨924342906#u32,1335530398#u32⟩,⟨604834087#u32,680476000#u32⟩⟩⟩
theorem call_f : FIo_Native.aspis_core.field.wide_exact.WideExact.add c e=ok f := by with_unfolding_all rfl
#print axioms call_f
def g : FIo_Install.NE := ⟨⟨⟨1890313852#u32,1611396561#u32⟩,⟨212138231#u32,1748995126#u32⟩⟩,⟨⟨2086614525#u32,1154372826#u32⟩,⟨1988543754#u32,2111714127#u32⟩⟩⟩
theorem call_g : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGs_LibraScale1.value JGs_Libra.sum1_4=ok g := by with_unfolding_all rfl
#print axioms call_g
def h : FIo_Install.NE := ⟨⟨⟨1178173105#u32,1814960182#u32⟩,⟨1456449853#u32,467780806#u32⟩⟩,⟨⟨1559072057#u32,1867903388#u32⟩,⟨1947740298#u32,245229283#u32⟩⟩⟩
theorem call_h : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 g JGs_Libra.q1_4=ok h := by with_unfolding_all rfl
#print axioms call_h
def i : FIo_Install.NE := ⟨⟨⟨207259757#u32,1869442170#u32⟩,⟨1636625871#u32,1340059992#u32⟩⟩,⟨⟨2107754883#u32,1542477030#u32⟩,⟨154872052#u32,446550592#u32⟩⟩⟩
theorem call_i : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGs_LibraScale1.value JGs_Libra.sum1_2=ok i := by with_unfolding_all rfl
#print axioms call_i
def j : FIo_Install.NE := ⟨⟨⟨711724695#u32,1817522054#u32⟩,⟨2067999657#u32,1869282493#u32⟩⟩,⟨⟨25875475#u32,1321321765#u32⟩,⟨1272631644#u32,1763726670#u32⟩⟩⟩
theorem call_j : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 i JGs_Libra.q1_20=ok j := by with_unfolding_all rfl
#print axioms call_j
def initial : Array FIo_Install.NE 4#usize := Array.repeat 4#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
def middle : Array FIo_Install.NE 4#usize := Array.make 4#usize [a,c,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def value : Array FIo_Install.NE 4#usize := Array.make 4#usize [a,f,h,j]
end AspisR1.JGs_LibraEnd
end
