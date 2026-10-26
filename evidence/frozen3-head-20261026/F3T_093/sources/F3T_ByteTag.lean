import F3T_ByteCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_ByteTag
open F3T_ByteCarrier

theorem public_tag (b : AspisV8R19.DuplexFrames.Bytes) : (publicOf b).tag=2 := by
  unfold publicOf
  split <;> rfl

theorem semantic_tag {F C : Type} (c : DrvC_Installation.Configuration F C) (s : Submission) :
    (input c s).semantic.value.tag=2 := by
  change (semantic c s).tag=2
  unfold semantic
  split
  · exact public_tag _
  · split
    · split <;> exact public_tag _
    · exact public_tag _

#print axioms public_tag
#print axioms semantic_tag
end AspisR1.F3T_ByteTag
end
