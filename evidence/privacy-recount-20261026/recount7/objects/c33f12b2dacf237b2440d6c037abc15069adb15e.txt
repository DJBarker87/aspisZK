import R1Z.ProverRwP6PowersGammaValues
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6WideDecode
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersNativeStep
open ProverCommitWideOps48
def raw (x : W) : Raw :=
  (⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩)
def decode (x : W) : Exact := value (raw x)
def canonical (x : W) : Prop := ProverCommitWideOps48.canonical (raw x)
theorem raw_source (x : Raw) : raw (fromW (source x)) = x := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  rfl
theorem value_source (x : Raw) : decode (fromW (source x)) = value x :=
  congrArg value (raw_source x)
theorem canonical_source (x : Raw) (hx : ProverCommitWideOps48.canonical x) :
    canonical (fromW (source x)) := by
  unfold canonical
  rw [raw_source]
  exact hx
#print axioms raw_source
#print axioms value_source
#print axioms canonical_source
end R1Z.ProverRwP6WideDecode
