import R1Z.PV_RunJoin_FourReader73
import R1Z.PV_RunJoin_WideLimbsParse72
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FactoredParser73
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FourReader73 (read)

def parse (s : Slice U8) : Result (Option aspis_core.field.wide_exact.WideExact) := do
  if Slice.len s != 32#usize then ok none else
    let w0 ← read s 0#usize 1#usize 2#usize 3#usize
    let w1 ← read s 4#usize 5#usize 6#usize 7#usize
    let w2 ← read s 8#usize 9#usize 10#usize 11#usize
    let w3 ← read s 12#usize 13#usize 14#usize 15#usize
    let w4 ← read s 16#usize 17#usize 18#usize 19#usize
    let w5 ← read s 20#usize 21#usize 22#usize 23#usize
    let w6 ← read s 24#usize 25#usize 26#usize 27#usize
    let w7 ← read s 28#usize 29#usize 30#usize 31#usize
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [w0, w1, w2, w3, w4, w5, w6, w7])

/-- Factor only abstract source reads; no concrete full wire is expanded. -/
theorem source (s : Slice U8) :
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_le_bytes s = parse s := by
  unfold parse ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_le_bytes
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.BYTE_LEN
  dsimp only []
  by_cases h : (Slice.len s != 32#usize)=true
  · simp only [h,if_true]
  · simp only [h,if_false]
    unfold PV_RunJoin_FourReader73.read
    simp only [bind_assoc_eq,bind_tc_ok,lift]

attribute [irreducible] parse
#print axioms parse
#print axioms source
end R1Z.PV_RunJoin_FactoredParser73
