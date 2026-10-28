import NDO_JGv_DotProducts2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotStep2
open Aeneas Aeneas.Std
open JGv_DotData
attribute [local irreducible] JGv_DotData.state JGv_DotData.term CheckpointBytes5Output.ofE

theorem source (n : Nat) (lo : 32≤n) (hi : n<48) :
    CheckpointBytes5Output.ofE (state (n+1))=CheckpointBytes5Output.ofE (state n)+term ⟨n%64,Nat.mod_lt _ (by omega)⟩ := by
  interval_cases n
  · exact JGv_DotProducts2.step32
  · exact JGv_DotProducts2.step33
  · exact JGv_DotProducts2.step34
  · exact JGv_DotProducts2.step35
  · exact JGv_DotProducts2.step36
  · exact JGv_DotProducts2.step37
  · exact JGv_DotProducts2.step38
  · exact JGv_DotProducts2.step39
  · exact JGv_DotProducts2.step40
  · exact JGv_DotProducts2.step41
  · exact JGv_DotProducts2.step42
  · exact JGv_DotProducts2.step43
  · exact JGv_DotProducts2.step44
  · exact JGv_DotProducts2.step45
  · exact JGv_DotProducts2.step46
  · exact JGv_DotProducts2.step47
#print axioms source
end AspisR1.JGv_DotStep2
end
