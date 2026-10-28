import NDO_JGv_DotProducts1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotStep1
open Aeneas Aeneas.Std
open JGv_DotData
attribute [local irreducible] JGv_DotData.state JGv_DotData.term CheckpointBytes5Output.ofE

theorem source (n : Nat) (lo : 16≤n) (hi : n<32) :
    CheckpointBytes5Output.ofE (state (n+1))=CheckpointBytes5Output.ofE (state n)+term ⟨n%64,Nat.mod_lt _ (by omega)⟩ := by
  interval_cases n
  · exact JGv_DotProducts1.step16
  · exact JGv_DotProducts1.step17
  · exact JGv_DotProducts1.step18
  · exact JGv_DotProducts1.step19
  · exact JGv_DotProducts1.step20
  · exact JGv_DotProducts1.step21
  · exact JGv_DotProducts1.step22
  · exact JGv_DotProducts1.step23
  · exact JGv_DotProducts1.step24
  · exact JGv_DotProducts1.step25
  · exact JGv_DotProducts1.step26
  · exact JGv_DotProducts1.step27
  · exact JGv_DotProducts1.step28
  · exact JGv_DotProducts1.step29
  · exact JGv_DotProducts1.step30
  · exact JGv_DotProducts1.step31
#print axioms source
end AspisR1.JGv_DotStep1
end
