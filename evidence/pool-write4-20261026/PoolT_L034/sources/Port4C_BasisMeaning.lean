import Port4C_BasisOuter

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_BasisMeaning
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
abbrev Basis := Array U32 256#usize

def source (ops : Ops) (node : U32) : Result Basis := do
  let zero ← ops.op4
  let one ← ops.op5
  let basis ← Array.update (Array.repeat 256#usize zero) 0#usize one
  verifier.accumulate_batched_with_node_loop0 ops one node 64#usize basis 1#usize

/-- CURRENT native basis initialization, six outer levels, every inner write,
canonicality and mathematical meaning. No successful basis call is assumed. -/
theorem total (ops : Ops) (backend : Port4C_BasisOuter.SessionABasis ops) (node : U32) :
    ∃ basis, source ops node=ok basis ∧ S7JoinBasisCanonical.Canonical basis ∧
      ∀ i : Fin 64, S7JoinBasisMachine.decode (S7JoinBasisBlock.cell basis i.val)=
        AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode node) i.val := by
  obtain ⟨basis,run,canonical,meaning⟩ := S7JoinBasisCanonical.total_exact node
  unfold S7JoinProductionBasis.basis_owned at run
  obtain ⟨initial,hinit,run⟩ := bind_success _ _ _ run
  rw [S7Kani3BasisOuter.outer_composition initial node 64#usize 1#usize 6
    (by decide) (by decide) (by decide)] at run
  have native := Port4C_BasisOuter.from_levels ops backend initial basis node 1#usize 6
    (by decide) (by decide) run
  refine ⟨basis,?_,canonical,meaning⟩
  simp only [source,backend.zero,backend.one,hinit,bind_tc_ok]
  exact native

/-- Factor only the native accumulation's basis prefix; the native row/rhs/
power/counter instructions remain verbatim. -/
theorem factor (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
    (node : U32) (value : Stage2E) (b : verifier.BatchedWeights)
    (size : a.weights.val.length=64) :
    verifier.accumulate_batched_with_node ops p a node value b =
      (do let basis ← source ops node
          let b1 ← verifier.accumulate_batched_with_node_loop1 ops
            {start:=0#usize,«end»:=64#usize} a.weights a.power a.next b 64#usize basis
          let terms ← lift (Usize.wrapping_add b1.terms 1#usize)
          let product ← ops.op3 value a.power
          let rhs ← ops.op2 a.rhs product
          ops.op15 11#u16 a.next rhs
          let power ← ops.op9 a.power p.rho
          let next ← lift (Usize.wrapping_add a.next 1#usize)
          ok ({a with rhs,power,next},{b1 with terms})) := by
  have width : alloc.vec.Vec.len a.weights=64#usize := UScalar.eq_of_val_eq size
  unfold verifier.accumulate_batched_with_node source
  rw [width]
  simp only [bind_assoc_eq]

#print axioms total
#print axioms factor
end AspisR1.Port4C_BasisMeaning
end
