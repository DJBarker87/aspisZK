import NLR_RowSpec087
import NLV_LowerTrace
import NLV_EvalTrace
import NLJ_Tx1Step
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_PreparePacket
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
abbrev RowSpec_087 := NLR_Interface.RowSpec_087
abbrev Native087 := NLR_Interface.Native087
def configuration (cfg : NLJ_Tx1.Configuration) : NLJ_Prepare.Configuration :=
 ⟨Op5T_Concrete.current {cfg.base with op16:=Tx1Q_Install.writer},cfg.boundaries,cfg.std⟩
def input (i : NLJ_Tx1.Input) (g : NLJ_Tx1.Scratch) : NLJ_Prepare.Input Unit :=
 ⟨i.digest,i.publicValue,i.proof,(),g⟩
def code (cfg : NLJ_Tx1.Configuration) (i : NLJ_Tx1.Input) (g : NLJ_Tx1.Scratch) :=
 SdkD_PrepareSource.code (configuration cfg).base cfg.boundaries cfg.std
 i.digest i.publicValue i.proof () g
/-- EXACT sibling087 packet at this TX1 state's input and scratch, with
chronological full-result lowering. No successful-child or chosen endpoint
hypothesis is supplied; 087 itself remains an OPEN packet parameter. -/
theorem at_call (cfg : NLJ_Tx1.Configuration) (native : Native087)
 (child : RowSpec_087 (configuration cfg) native)
 (i : NLJ_Tx1.Input) (g : NLJ_Tx1.Scratch) (frame : NLR_Interface.ExternalFrame)
 (associated : SdkD_PrepareLower.Associated i.hashv (code cfg i g))
 (before : SdkC_Source.Log) :
 let observed:=native (input i g) frame
 observed.afterInput=input i g ∧ observed.afterFrame=frame ∧
 SdkC_Source.run i.hashv (SdkD_PrepareLower.lower (code cfg i g)) before =
 (observed.reply,before++observed.log.map NLV_LowerTrace.event) := by
 have packet:=child (input i g) frame
 refine ⟨packet.1,packet.2.1,?_⟩
 have source:=NLV_LowerTrace.source i.hashv (code cfg i g) associated before
 have actual := packet.2.2.2
 change AspisR1PublicPreparation.PreparedHashCode.run (code cfg i g)=_ at actual
 rw [actual] at source
 exact source
/-- A source cut discharged by the SAME child law, rather than an endpoint
premise of a proposed parent root. Native physical footprints remain separate. -/
theorem source_cut (cfg : NLJ_Tx1.Configuration) (native : Native087)
 (child : RowSpec_087 (configuration cfg) native)
 (i : NLJ_Tx1.Input) (g : NLJ_Tx1.Scratch) (frame : NLR_Interface.ExternalFrame)
 (associated : SdkD_PrepareLower.Associated i.hashv (code cfg i g)) :
 NHZ_DRIVER.Cuts i.hashv (SdkD_PrepareLower.lower (code cfg i g))
 (native (input i g) frame).reply ((native (input i g) frame).log.map NLV_LowerTrace.event) := by
 apply NHZ_DRIVER.Cuts.leaf
 apply NLV_EvalTrace.of_run
 simpa only [List.nil_append] using (at_call cfg native child i g frame associated []).2.2
#print axioms at_call
#print axioms source_cut
#print at_call
end AspisR1.NLV_PreparePacket
end
