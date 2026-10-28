import NDO_JGv_DotProducts3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotStep3
open Aeneas Aeneas.Std
open JGv_DotData
attribute [local irreducible] JGv_DotData.state JGv_DotData.term CheckpointBytes5Output.ofE

theorem source (n : Nat) (lo : 48≤n) (hi : n<64) :
    CheckpointBytes5Output.ofE (state (n+1))=CheckpointBytes5Output.ofE (state n)+term ⟨n%64,Nat.mod_lt _ (by omega)⟩ := by
  interval_cases n
  · exact JGv_DotProducts3.step48
  · exact JGv_DotProducts3.step49
  · exact JGv_DotProducts3.step50
  · exact JGv_DotProducts3.step51
  · exact JGv_DotProducts3.step52
  · exact JGv_DotProducts3.step53
  · exact JGv_DotProducts3.step54
  · exact JGv_DotProducts3.step55
  · exact JGv_DotProducts3.step56
  · exact JGv_DotProducts3.step57
  · exact JGv_DotProducts3.step58
  · exact JGv_DotProducts3.step59
  · exact JGv_DotProducts3.step60
  · exact JGv_DotProducts3.step61
  · exact JGv_DotProducts3.step62
  · exact JGv_DotProducts3.step63
#print axioms source
end AspisR1.JGv_DotStep3
end
