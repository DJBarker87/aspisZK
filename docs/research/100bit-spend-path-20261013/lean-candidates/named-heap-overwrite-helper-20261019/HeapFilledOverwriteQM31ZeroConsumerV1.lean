import AspisR1HeapFilledOverwrite.Funs
import AspisR1BatchedWeightsExtraction.Types
import HeapFilledOverwriteCandidateSuccessV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace HeapFilledOverwriteQM31ZeroConsumerV1

abbrev QM31 := AspisR1BatchedWeightsExtraction.aspis_core.field.QM31

def sourceQM31Clone (x : QM31) : Result QM31 := ok x

def sourceQM31CloneInst : core.clone.Clone QM31 := { clone := sourceQM31Clone }

def sourceQM31CopyInst : core.marker.Copy QM31 := { cloneInst := sourceQM31CloneInst }

def sourceQM31Zero : QM31 :=
  ⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩

theorem filled_overwrite_qm31_zero_success
    (copyInst : core.marker.Copy QM31) (n : Std.Usize)
    (out : alloc.vec.Vec QM31)
    (h : AspisR1HeapFilledOverwrite.aspis_core.r0.heap.filled_overwrite
      copyInst n sourceQM31Zero = .ok (.Ok out)) :
    out.length = n.val ∧
      ∀ i : Std.Usize, i.val < n.val →
        Slice.index_usize (out : Slice QM31) i = .ok sourceQM31Zero := by
  exact HeapFilledOverwriteSuccessV1.filled_success_contents copyInst n
    sourceQM31Zero out h

theorem candidateAccumulatorZeroBuffer
    (n : Std.Usize) (out : alloc.vec.Vec QM31)
    (h : AspisR1HeapFilledOverwrite.aspis_core.r0.heap.filled_overwrite
      sourceQM31CopyInst n sourceQM31Zero = .ok (.Ok out)) :
    out.length = n.val ∧
      ∀ i : Std.Usize, i.val < n.val →
        Slice.index_usize (out : Slice QM31) i = .ok sourceQM31Zero := by
  exact filled_overwrite_qm31_zero_success sourceQM31CopyInst n out h

#print axioms filled_overwrite_qm31_zero_success
#print axioms candidateAccumulatorZeroBuffer
end HeapFilledOverwriteQM31ZeroConsumerV1
