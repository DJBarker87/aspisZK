import NKY_LevelCarrier
import CurrentCallerUsizeArithmeticV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_LevelsLiteral
open Aeneas Aeneas.Std Result ControlFlow
open NJX_AppendDomains (Frontier High)
open NJX_DigestCohort (O D)
open FIv_NativeArithmetic (NQ)
open NKY_LevelCarrier (Pair pair state)
/-- Literal retained emitted body; the sole child slot is explicit for (y)(3).
See NKY_LITERAL_INPUT.json for immutable source/hash and exact original text.
Field/carrier names are transported to the coherent FIq owners. -/
def body (child : U64 → Usize → NJX_DigestCohort.D → NJX_DigestCohort.O → FIv_NativeArithmetic.NQ → Result NKY_LevelCarrier.Pair)
  (next_pair_index : Std.U64)
  (frontier : Array (Array U32 8#usize) 20#usize)
  (opened : Array FIq_Native.field.QM31 16#usize)
  (selector_high : Array FIq_Native.field.QM31 64#usize)
  (local0 : Array FIq_Native.field.QM31 2#usize)
  (local12 : Array FIq_Native.field.QM31 2#usize) (level : Std.Usize) :
  Result (ControlFlow ((Array FIq_Native.field.QM31 2#usize) × (Array
    FIq_Native.field.QM31 2#usize) × Std.Usize) ((Array FIq_Native.field.QM31
    2#usize) × (Array FIq_Native.field.QM31 2#usize)))
  := do
  if level < 20#usize
  then
    let a ← Array.index_usize frontier level
    let i ← 34#usize + level
    let q ← Array.index_usize selector_high i
    let (level0, level12) ←
      child
        next_pair_index level a opened q
    let q1 ← Array.index_usize local0 0#usize
    let q2 ← Array.index_usize level0 0#usize
    let q3 ← FIq_Native.field.QM31.add q1 q2
    let local01 ← Array.update local0 0#usize q3
    let q4 ← Array.index_usize local01 1#usize
    let q5 ← Array.index_usize level0 1#usize
    let q6 ← FIq_Native.field.QM31.add q4 q5
    let a1 ← Array.update local01 1#usize q6
    let q7 ← Array.index_usize local12 0#usize
    let q8 ← Array.index_usize level12 0#usize
    let q9 ← FIq_Native.field.QM31.add q7 q8
    let local121 ← Array.update local12 0#usize q9
    let q10 ← Array.index_usize local121 1#usize
    let q11 ← Array.index_usize level12 1#usize
    let q12 ← FIq_Native.field.QM31.add q10 q11
    let a2 ← Array.update local121 1#usize q12
    let level1 ← level + 1#usize
    ok (cont (a1, a2, level1))
  else ok (done (local0, local12))


abbrev Child := U64 → Usize → D → O → NQ → Result Pair
/-- Current-library form of the emitted Result/ControlFlow loop combinator. -/
def loop (child : Child) (index : U64) (f : Frontier) (o : O) (s : High)
 (a b : Array NQ 2#usize) (level : Usize) : Result Pair := do
 let flow ← body child index f o s a b level
 match flow with
 | .done p => ok p
 | .cont (a,b,level) => loop child index f o s a b level
partial_fixpoint

def append_levels_packed_selector_tensor (child : Child) (index : U64)
 (f : Frontier) (o : O) (s : High) : Result Pair :=
 loop child index f o s (Array.repeat 2#usize FIq_Native.field.QM31.ZERO)
  (Array.repeat 2#usize FIq_Native.field.QM31.ZERO) 0#usize

def child : Child := fun index level frontier o high => do
 let out ← NKI_AppendPacket.cohort index level frontier o high
 ok (pair out)

theorem done (c : Child) (index : U64) (f : Frontier) (o : O) (s : High)
 (a b : Array NQ 2#usize) (level : Usize) (h : ¬level<20#usize) :
 body c index f o s a b level=ok (.done (a,b)) := by
 simp only [body,if_neg h]
#print axioms done
end AspisR1.NKY_LevelsLiteral
end
