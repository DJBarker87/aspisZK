import NEB_GeometryGatherDomains
import NEV_PrefixCapacity
set_option autoImplicit false
noncomputable section
namespace NEV_PrefixCallerDomain
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

/-- The adopted gather already proves its exact five-word growth on the SAME
accepted loop. Reuse its induction rather than reproving it. This theorem is
model-side; native gather association is independently required. -/
theorem gathered {C : Type} (ops : Ops C) (error : C)
    (start : Usize) (iter : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32)
    (out : verifier.QueryGeometry) (fuel : Nat)
    (remaining : iter.i+fuel=iter.slice.val.length)
    (empty : flat.val=[])
    (run : verifier.QueryGeometry.for_range_loop0
      (Port4C_GeometryStd.install (NEB_GeometryIndices.install ops error))
      iter start zs flat=ok (.Ok out)) :
    ∃ zsFinal flatFinal terminal,
      verifier.QueryGeometry.for_range_loop0.body
        (Port4C_GeometryStd.install (NEB_GeometryIndices.install ops error))
        start terminal zsFinal flatFinal=ok (done (.Ok out)) ∧
      flatFinal.val.length=5*fuel := by
  obtain ⟨zsFinal,flatFinal,terminal,_,_,body,_,_,len⟩ :=
    NEB_GeometryGatherDomains.traversal ops error start iter zs flat out fuel remaining
      (by simp only [empty,List.not_mem_nil,false_implies,implies_true])
      (by simp only [empty,List.not_mem_nil,false_implies,implies_true]) run
  exact ⟨zsFinal,flatFinal,terminal,body,by simpa only [empty,List.length_nil,Nat.zero_add] using len⟩

/-- Every nonempty actual gather cardinality is in the enumerated native
capacity family. Zero reaches no prefix call in the frozen source. -/
theorem capacities (queries capacity : Nat) (bound : queries≤22)
    (length : capacity=5*queries) :
    capacity≤110 ∧ capacity%5=0 ∧ (capacity=0 ∨ 5≤capacity) := by omega

#print axioms gathered
#print axioms capacities
end NEV_PrefixCallerDomain
end
