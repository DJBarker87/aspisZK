import NDO_JGv_DotProducts0
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_DotStep0
open Aeneas Aeneas.Std
open JGv_DotData
attribute [local irreducible] JGv_DotData.state JGv_DotData.term CheckpointBytes5Output.ofE

theorem source (n : Nat) (lo : 0≤n) (hi : n<16) :
    CheckpointBytes5Output.ofE (state (n+1))=CheckpointBytes5Output.ofE (state n)+term ⟨n%64,Nat.mod_lt _ (by omega)⟩ := by
  interval_cases n
  · exact JGv_DotProducts0.step00
  · exact JGv_DotProducts0.step01
  · exact JGv_DotProducts0.step02
  · exact JGv_DotProducts0.step03
  · exact JGv_DotProducts0.step04
  · exact JGv_DotProducts0.step05
  · exact JGv_DotProducts0.step06
  · exact JGv_DotProducts0.step07
  · exact JGv_DotProducts0.step08
  · exact JGv_DotProducts0.step09
  · exact JGv_DotProducts0.step10
  · exact JGv_DotProducts0.step11
  · exact JGv_DotProducts0.step12
  · exact JGv_DotProducts0.step13
  · exact JGv_DotProducts0.step14
  · exact JGv_DotProducts0.step15
#print axioms source
end AspisR1.JGv_DotStep0
end
