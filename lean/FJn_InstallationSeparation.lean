import FJn_InstallationBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_InstallationSeparation
open Aeneas Aeneas.Std Result DrvC_Installation
abbrev MQ:=FIp_SemanticArithmetic.MQ
/-- Only the two tiny literal carrier values are inspected. -/
theorem zero_ne_one : AspisR1PublicPreparation.aspis_core.field.QM31.ZERO≠
    AspisR1PublicPreparation.aspis_core.field.QM31.ONE := by
  intro same
  have h:=congrArg (fun q : MQ=>q.c0.a.val) same
  change 0=1 at h
  omega
/-- An arbitrary Configuration does not imply fixed-terminal installation.
This says nothing about the existence of an accepted forged source run. -/
theorem not_uniform {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (pub : FIq_Carriers.Public)
    (claims : Array (Array MQ 29#usize) 3#usize) (alpha : Array MQ 10#usize)
    (challenges : AspisR1PublicPreparation.r1_wire.Challenges) :
    ∃ chosen : Configuration FIo_Install.W C,
      (FIp_Install.configuration err chosen r).boundaries.terminal≠FIq_Terminal.terminal := by
  let z:=AspisR1PublicPreparation.aspis_core.field.QM31.ZERO
  let o:=AspisR1PublicPreparation.aspis_core.field.QM31.ONE
  by_cases hz : FIq_Terminal.terminal pub claims alpha challenges=ok (.Ok z)
  · refine ⟨{c with boundaries:={c.boundaries with terminal:=fun _ _ _ _=>ok (.Ok o)}},?_⟩
    intro same
    have output:=congrArg (fun f=>f pub claims alpha challenges) same
    change ok (.Ok o)=FIq_Terminal.terminal pub claims alpha challenges at output
    rw [hz] at output
    exact zero_ne_one (core.result.Result.Ok.inj (Result.ok.inj output)).symm
  · refine ⟨{c with boundaries:={c.boundaries with terminal:=fun _ _ _ _=>ok (.Ok z)}},?_⟩
    intro same
    have output:=congrArg (fun f=>f pub claims alpha challenges) same
    exact hz output.symm
#print axioms zero_ne_one
#print axioms not_uniform
end AspisR1.FJn_InstallationSeparation
end
