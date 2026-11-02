import NEO_ComplexTotal
set_option autoImplicit false
namespace NEO_QuadraticCuts
open Aeneas Aeneas.Std Result
attribute [local irreducible] AspisR1CandidateParser.field.CM31.from_le_bytes

def observe (q : AspisR1CandidateParser.field.QM31) : Array U32 4#usize :=
 Array.make 4#usize [q.c0.a,q.c0.b,q.c1.a,q.c1.b]
def cohort (bytes : Slice U8) : Result (Option (Array U32 4#usize)) := do
 let q ← AspisR1CandidateParser.field.QM31.from_le_bytes bytes
 ok (q.map observe)

theorem result (bytes : Slice U8) (lo hi : Array U8 8#usize)
 (first : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
 bytes {start:=0#usize,«end»:=8#usize}=ok lo.to_slice)
 (second : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
 bytes {start:=8#usize,«end»:=16#usize}=ok hi.to_slice) :
 NEO_WindowV2.quadratic bytes=cohort bytes := by
 simp only [NEO_WindowV2.quadratic,first,second,bind_tc_ok,NEO_ComplexTotal.fixed,
  NEO_ComplexReference.cohort,cohort,AspisR1CandidateParser.field.QM31.from_le_bytes]
 cases h0 : AspisR1CandidateParser.field.CM31.from_le_bytes lo.to_slice <;>
  try simp only [bind_tc_ok]
 all_goals try rfl
 all_goals rename_i o
 all_goals cases o <;> simp only [Option.map,bind_tc_ok,
  AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
  NEO_ByteCuts.residual]
 all_goals try rfl
 all_goals cases h1 : AspisR1CandidateParser.field.CM31.from_le_bytes hi.to_slice <;>
  try simp only [bind_tc_ok]
 all_goals try rfl
 all_goals rename_i o
 all_goals cases o <;> simp [Option.map,bind_tc_ok,
  AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
  NEO_ByteCuts.residual,NEO_ComplexReference.observe,observe,Array.index_usize,Array.make]

#print axioms result
end NEO_QuadraticCuts
