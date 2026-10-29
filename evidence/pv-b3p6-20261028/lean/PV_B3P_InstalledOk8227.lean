import PV_B3P_InstalledPublic8227
import PV_B3P_TerminalOk8227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
noncomputable section
attribute [local irreducible] PV_B3P_Install227.actual PV_B3P_Install227.selected
  PV_B3P_Install227.Types PV_B3P_Carrier227.Types PV_B3P_Carrier227.semantic
  PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.challenges
  PV_B3P_Carrier227.toQ PV_B3P_Carrier227.fromQ
  reference_terminal.reference227 valid_public transfer_seed8 installed_public8

theorem installed_success8 (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_B3P_Install227.Types base))
    (p : reference_terminal.SemanticPublic) (recipient : Array U32 8#usize)
    (claims : Array (Array ProverRwFull.aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array ProverRwFull.aspis_core.field.QM31 10#usize)
    (c : ProverRwFull.aspis_core.state_only_prefix.r0.Challenges) :
    RustOk (@ProverRwFull.ExternalFuns.op227 (PV_B3P_Install227.Types base)
      (PV_B3P_Install227.actual base ops) (installed_public8 base p recipient) claims point c) := by
  rw [PV_B3P_Install227.actual_source,installed_public_semantic8]
  obtain ⟨value,hvalue⟩ := reference_success8 (transfer_seed8 p recipient)
    (PV_B3P_Carrier227.mapArray (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ) claims)
    (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ point)
    (PV_B3P_Carrier227.challenges c)
  rw [hvalue]
  exact ⟨PV_B3P_Carrier227.fromQ value,rfl⟩

theorem installed_nonvacuity8 (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_B3P_Install227.Types base))
    (claims : Array (Array ProverRwFull.aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array ProverRwFull.aspis_core.field.QM31 10#usize)
    (c : ProverRwFull.aspis_core.state_only_prefix.r0.Challenges) :
    ∃ public1 value,
      @ProverRwFull.ExternalFuns.op227 (PV_B3P_Install227.Types base)
        (PV_B3P_Install227.actual base ops) public1 claims point c = .ok (.Ok value) := by
  let recipient : Array U32 8#usize := Array.repeat 8#usize 0#u32
  obtain ⟨value,hvalue⟩ := installed_success8 base ops seed_public recipient claims point c
  exact ⟨installed_public8 base seed_public recipient,value,hvalue⟩

#print axioms installed_nonvacuity8
#print axioms installed_success8
end PV_B3P_Success227
