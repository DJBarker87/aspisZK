import NIM_NHY_COMBINED_IMPORT
import NHT_AdapterInstall
import AdapterRwCuts
set_option autoImplicit false
noncomputable section
namespace NIS_Tx2Boundary
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev E := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev Out := Result (core.result.Result Unit PE)

def mapped (ops : AdapterRw.Ops) (reply : Result (core.result.Result Unit E)) : Out := do
  let r ← reply
  AdapterRw.core.result.Result.map_err (BuiltinFnOnce E PE) r ops.op44

/-- Exact emitted owned-stage tail after its public/proof/checkpoint bindings.
The child and mapped error retain their full Result, including fail/div. -/
def tail (ops : AdapterRw.Ops) (pub proof checkpoint : Slice U8) : Out := do
  let observer ← AdapterRw.observer ops
  let r ← ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
    pub proof checkpoint () observer
  AdapterRw.core.result.Result.map_err (BuiltinFnOnce E PE) r ops.op44

theorem digest_instance (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NHT_AdapterInstall.install adapter stage) =
    AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 adapter := rfl

theorem ports (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    @AdapterRw.Ops.op10 (NHT_AdapterInstall.install adapter stage)=@AdapterRw.Ops.op10 adapter ∧
    (NHT_AdapterInstall.install adapter stage).op43=adapter.op43 ∧
    (NHT_AdapterInstall.install adapter stage).op44=adapter.op44 := ⟨rfl,rfl,rfl⟩

theorem emitted (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    (pub proof checkpoint : Slice U8) :
    tail (NHT_AdapterInstall.install adapter stage) pub proof checkpoint =
      mapped adapter (NHT_EmittedAuth.tx2_authenticated (NHT_Tx2CommonModel.constants stage)
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 adapter)
        pub proof checkpoint () none) := by
  simp only [tail,AspisR1.AdapterRw.Cuts.observer_none,bind_tc_ok]
  change mapped adapter (NHT_EmittedAuth.tx2_authenticated (NHT_Tx2CommonModel.constants stage)
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NHT_AdapterInstall.install adapter stage))
    pub proof checkpoint () none)=_
  rw [digest_instance]

theorem cohort (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    (pub proof checkpoint : Slice U8) :
    tail (NHT_AdapterInstall.install adapter stage) pub proof checkpoint =
      mapped adapter (VTop_Stages.verifier.candidate.tx2_authenticated
        (NHT_Tx2CommonModel.constants stage)
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 adapter)
        pub proof checkpoint () none) := by
  rw [emitted,NHT_Tx2AuthModel.source]

theorem abort_prefix (ops : AdapterRw.Ops) (error : Error) :
    mapped ops (.fail error)=.fail error ∧ mapped ops .div=.div := ⟨rfl,rfl⟩

#print axioms digest_instance
#print axioms ports
#print axioms emitted
#print axioms cohort
#print axioms abort_prefix
end NIS_Tx2Boundary
