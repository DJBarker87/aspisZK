import NDO_JHn_TX1Frontier
import NDO_JHn_ExactReturned
set_option autoImplicit false
set_option pp.proofs false
open Lean Elab Command
run_cmd logInfo "NDR_TX1_POST_IMPORT"
noncomputable section
namespace AspisR1.JHq_TX1
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
variable [trees : JHe_SHARealization]

-- Named application of the independently checked byte-identity proof.
#check AspisR1.JHn_TX1Frontier.of_byte_identity
#check AspisR1.JHn_ExactReturned.source

theorem accepted1_saved (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first base stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 := by
  exact JHn_TX1Frontier.of_byte_identity base stage JHn_ExactReturned.source
#print axioms accepted1_saved
#check accepted1_saved
end AspisR1.JHq_TX1
end
