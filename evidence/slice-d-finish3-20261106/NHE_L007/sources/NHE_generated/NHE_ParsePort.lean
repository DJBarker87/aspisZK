import NHE_WidePort
set_option autoImplicit false
namespace NHE_ParsePort
open Aeneas Aeneas.Std Result AspisR1
abbrev NE := FIo_Install.NE
abbrev RE := AspisR1RecordParser.field.wide_exact.WideExact

def record (x : NE) : RE := ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem limbs (w : Array U32 8#usize) :
 FIo_FieldBridge.map (Option.map record) (FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs w)=
 AspisR1RecordParser.field.wide_exact.WideExact.from_limbs w := by
 unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs AspisR1RecordParser.field.wide_exact.WideExact.from_limbs
 simp only [FIo_FieldBridge.map_bind,FIo_Native.aspis_core.field.P,AspisR1RecordParser.field.P]
 repeat' first | rfl | (progress simp only [FIo_FieldBridge.map_bind]) | (congr 1; funext x) | split

#print axioms limbs
end NHE_ParsePort
