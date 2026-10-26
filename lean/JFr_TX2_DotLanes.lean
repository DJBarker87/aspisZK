import JFr_TX2_DotStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_DotLanes
open Aeneas Aeneas.Std Result

/-- One exact native multiply/add/write lane, retaining checked U64 operations. -/
def lane (coefficient : Array U32 8#usize) (scalar : U32)
    (sums : Array U64 8#usize) (j : Usize) : Result (Array U64 8#usize) := do
  let word ← Array.index_usize coefficient j
  let a ← lift (core.convert.num.FromU64U32.from word)
  let b ← lift (core.convert.num.FromU64U32.from scalar)
  let product ← a*b
  let before ← Array.index_usize sums j
  let after ← before+product
  Array.update sums j after

def eight (coefficient : Array U32 8#usize) (scalar : U32)
    (sums : Array U64 8#usize) : Result (Array U64 8#usize) := do
  let s1 ← lane coefficient scalar sums 0#usize
  let s2 ← lane coefficient scalar s1 1#usize
  let s3 ← lane coefficient scalar s2 2#usize
  let s4 ← lane coefficient scalar s3 3#usize
  let s5 ← lane coefficient scalar s4 4#usize
  let s6 ← lane coefficient scalar s5 5#usize
  let s7 ← lane coefficient scalar s6 6#usize
  let s8 ← lane coefficient scalar s7 7#usize
  ok s8

/-- Symbolic association exposes the eight actual lane calls. -/
theorem update (g : Array FIo_Install.NE 29#usize) (term : Usize)
    (scalar : U32) (sums : Array U64 8#usize) :
    JFr_TX2_DotStep.update g term scalar sums=
      (do let wide ← Array.index_usize g term
          let coefficient ← FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs wide
          eight coefficient scalar sums) := by
  simp only [JFr_TX2_DotStep.update,eight,lane,bind_assoc_eq,bind_tc_ok]

#print axioms update
end AspisR1.JFr_TX2_DotLanes
end
