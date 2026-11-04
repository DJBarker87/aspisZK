import NFQ_COMBINED_IMPORT
set_option autoImplicit false
namespace NFQ_WideGetters
abbrev NQ := FIo_Native.aspis_core.field.QM31
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact
abbrev CQ := AspisR1CurrentWide.field.QM31
abbrev CE := AspisR1CurrentWide.field.wide_exact.WideExact

def toQ (x : NQ) : CQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toE (x : NE) : CE := ⟨toQ x.c0,toQ x.c1⟩
def fromQ (x : CQ) : NQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromE (x : CE) : NE := ⟨fromQ x.c0,fromQ x.c1⟩

theorem native_roundtrip (x : NE) : fromE (toE x)=x := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  rfl

theorem model_roundtrip (x : CE) : toE (fromE x)=x := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  rfl

/-- Concrete existing CurrentWide projections, preserving the full returned QM31. -/
theorem c0 (x : NE) : (toE x).c0=toQ x.c0 := rfl
theorem c1 (x : NE) : (toE x).c1=toQ x.c1 := rfl
#print axioms native_roundtrip
#print axioms model_roundtrip
#print axioms c0
#print axioms c1
end NFQ_WideGetters
