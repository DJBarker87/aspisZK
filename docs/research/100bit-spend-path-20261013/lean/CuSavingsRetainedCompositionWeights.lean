import CuSavingsS2Candidate3
import CuSavingsLibraSourceOrigins
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedCompositionWeights
open Aeneas Aeneas.Std Result
open CuSavingsLibraConcrete CuSavingsLibraOrigins
attribute [local instance] CuSavingsLibraConcrete.shared
abbrev E := AspisR1Libra.field.wide_exact.WideExact
abbrev Low := Array E 16#usize
abbrev Extra := Array AspisR1Libra.field.QM31 2#usize
abbrev Parts := Array E 4#usize
abbrev GroupE := AspisR1S2Groups.field.wide_exact.WideExact

def toGroup (x : E) : GroupE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def lowToGroup (low : Low) : Array GroupE 16#usize :=
  ⟨low.val.map toGroup,by simpa only [List.length_map] using low.property⟩

variable [AspisR1S2Groups.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime]

/-- The two replacements share the actual source low16 producer. Both exact
inactive-group kernels and both exact Libra kernels are composed into that
same source caller context, preserving failures/divergence and the suffix.
Source origins establish the Libra inputs, rather than a kernel-law premise. -/
theorem caller_equivalence {Output : Type} (weights : AspisR1S2Groups.Weights)
    (bytes : Slice U8) (alpha0 alpha1 : E) (extra : Extra)
    (ha0 : Alpha alpha0) (ha1 : Alpha alpha1)
    (hextra : ∀ i,i < 2 → CuSavingsLibraOrigins.Extra
      (CuSavingsLibraSourceControl.lookup extra AspisR1Libra.field.QM31.ONE i))
    (after : Low → GroupE → Parts → Result Output) :
    (do
      let ap0 ← CuSavingsLibraCaller.powersCaller alpha0
      let ap1 ← CuSavingsLibraCaller.powersCaller alpha1
      let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
      let inactive ← AspisR1S2Groups.new.grouped_inactive_pair weights bytes (lowToGroup low)
      let libra ← AspisR1Libra.new.factored_s2_libra_weights ap0 ap1 extra
      after low inactive libra) =
    (do
      let ap0 ← CuSavingsLibraCaller.powersCaller alpha0
      let ap1 ← CuSavingsLibraCaller.powersCaller alpha1
      let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
      let inactive ← AspisR1S2Groups.old.grouped_inactive_pair weights bytes (lowToGroup low)
      let libra ← AspisR1Libra.old.twofold_libra_weights low extra
      after low inactive libra) := by
  have result := CuSavingsLibraSourceOrigins.source_caller_context alpha0 alpha1 extra ha0 ha1 hextra
    (fun low => AspisR1S2Groups.old.grouped_inactive_pair weights bytes (lowToGroup low)) after
  simpa only [CuSavingsS2Candidate3.helper_equivalence] using result

/-- The exact intervening source computations retain their order between the
inactive-row result and Libra row. This includes other functional pairings. -/
theorem full_caller_equivalence {State Output : Type} (weights : AspisR1S2Groups.Weights)
    (bytes : Slice U8) (alpha0 alpha1 : E) (extra : Extra)
    (ha0 : Alpha alpha0) (ha1 : Alpha alpha1)
    (hextra : ∀ i,i < 2 → CuSavingsLibraOrigins.Extra
      (CuSavingsLibraSourceControl.lookup extra AspisR1Libra.field.QM31.ONE i))
    (between : Low → GroupE → Result State)
    (after : Low → GroupE → State → Parts → Result Output) :
    (do
      let ap0 ← CuSavingsLibraCaller.powersCaller alpha0
      let ap1 ← CuSavingsLibraCaller.powersCaller alpha1
      let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
      let inactive ← AspisR1S2Groups.new.grouped_inactive_pair weights bytes (lowToGroup low)
      let state ← between low inactive
      let libra ← AspisR1Libra.new.factored_s2_libra_weights ap0 ap1 extra
      after low inactive state libra) =
    (do
      let ap0 ← CuSavingsLibraCaller.powersCaller alpha0
      let ap1 ← CuSavingsLibraCaller.powersCaller alpha1
      let low ← CuSavingsLibraCaller.lowCaller ap0 ap1
      let inactive ← AspisR1S2Groups.old.grouped_inactive_pair weights bytes (lowToGroup low)
      let state ← between low inactive
      let libra ← AspisR1Libra.old.twofold_libra_weights low extra
      after low inactive state libra) := by
  have result := CuSavingsLibraSourceOrigins.source_caller_context alpha0 alpha1 extra ha0 ha1 hextra
    (fun low => do
      let inactive ← AspisR1S2Groups.old.grouped_inactive_pair weights bytes (lowToGroup low)
      let state ← between low inactive
      .ok (inactive,state))
    (fun low pair libra => after low pair.1 pair.2 libra)
  simpa only [CuSavingsS2Candidate3.helper_equivalence,bind_assoc_eq,bind_tc_ok] using result

#print axioms toGroup
#print axioms lowToGroup
#print axioms caller_equivalence
#print axioms full_caller_equivalence
end AspisR1.CuSavingsRetainedCompositionWeights
