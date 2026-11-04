import NEV_BasisOuterRaw
import NBF_BasisDomain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NEV_BasisProducer
open Aeneas Aeneas.Std Result

def source (node : U32) : Result (Array U32 256#usize) := do
 let initial ← Array.update (Array.repeat 256#usize 0#u32) 0#usize 1#u32
 NEV_AccumulateRaw.accumulate_batched_with_node_loop0 1#u32 node 64#usize initial 1#usize
/-- The actual width64 initialization and six-level loop reach exactly the
retained basis producer, for every raw input node. -/
theorem association (ops : AspisR1.Port3_NativeQueryBody.Ops) (node : U32) :
    source node=NBF_BasisDomain.source ops node := by
  have continuations :
      (fun initial : Array U32 256#usize =>
        NEV_AccumulateRaw.accumulate_batched_with_node_loop0 1#u32 node 64#usize initial 1#usize) =
      (fun initial : Array U32 256#usize =>
        AspisR1.Port3_NativeQueryBody.verifier.accumulate_batched_with_node_loop0
          (NBF_BasisInstall.install ops) 1#u32 node 64#usize initial 1#usize) := by
    funext initial
    exact NEV_BasisOuterRaw.levels_eq ops 6 initial node 1#usize 64#usize
      (by decide) (by decide) (by decide)
  exact congrArg (fun next : Array U32 256#usize → Result (Array U32 256#usize) =>
    do let initial ← Array.update (Array.repeat 256#usize 0#u32) 0#usize 1#u32
       next initial) continuations

theorem total (ops : AspisR1.Port3_NativeQueryBody.Ops) (node : U32) :
    ∃ basis,source node=ok basis ∧ AspisR1.S7JoinBasisCanonical.Canonical basis := by
  rw [association ops node]
  exact NBF_BasisDomain.total ops node
/-- Caller domain is derived from the SAME actual returned basis and read. -/
theorem read_canonical (ops : AspisR1.Port3_NativeQueryBody.Ops) (node : U32)
    (basis : Array U32 256#usize) (run : source node=ok basis)
    (index : Usize) (inside : index.val<256) (word : U32)
    (read : NEV_AccumulateRaw.basis_at basis index=ok word) : word.val<2147483647 := by
  rw [association ops node] at run
  exact NBF_BasisDomain.read_canonical ops node basis run index inside word read
#print axioms association
#print axioms total
#print axioms read_canonical
end NEV_BasisProducer
end
