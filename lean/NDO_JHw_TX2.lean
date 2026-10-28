import NDO_JHw_Wrapper
import NDO_JHi_SHAProof
import NDO_JHi_SHAPublic
import NDO_JHi_SHAChecksum
import NDO_JHe_SHARealization
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHw_TX2
open Aeneas Aeneas.Std Result
open JHv_Configuration JHu_FixturePdaRuntime

/-- The three inherited, independently checked byte-digest equations. -/
theorem byteSHA : JHi_SHARealization.SHARealization :=
  ⟨JHi_SHAProof.source, JHi_SHAPublic.source, JHi_SHAChecksum.source⟩
#print axioms byteSHA

/-- The explicit seven-call PDA runtime law is the only remaining TX2 premise. -/
theorem accepted2_runtime (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) :
    S2W_D189Wrappers.second (JHe_Natives.second (adapter base) stage)
      CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
      JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,())) :=
  JHw_Wrapper.source base stage slot runtime byteSHA
#print axioms accepted2_runtime

/-- Joint interface: exactly the existing tree-digest certificate and the
original deferred fixture PDA runtime law; the TX2 implication is stronger. -/
theorem accepted2 [trees : JHe_SHARealization]
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) :
    S2W_D189Wrappers.second (JHe_Natives.second (adapter base) stage)
      CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
      JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,())) :=
  accepted2_runtime base stage slot runtime
#print axioms accepted2
set_option pp.proofs false in
#print accepted2
end AspisR1.JHw_TX2
end
