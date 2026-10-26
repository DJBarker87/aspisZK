import F3T_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_Leaves
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem actual {F : Type} (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (v : AspisR1Stage2.verifier.View) (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (H : Bytes → State) (trace : List (Bytes × State)) (parsed : OraclePortCompactDraft.Parsed)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : RecordedBinaryExperimentBin.SourceInputs) (D : LiteralByteProtocol.Decoder) (i : F3_Model.Input)
    (values : F3S_AcceptanceValues.Values finish v p a H trace parsed q tr data D i) :
    ∃ x : F3S_FinishWitness.Primitives finish v p a,
      F3T_Leaves.Holds finish v p a x q parsed tr data →
        AuS1_Finish.Collision H trace parsed q ∨ (eval H (F3_Model.verifier D i)).2=true := by
  obtain ⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,ha0,ha1,hw,has,hp,hd,cont⟩ := values
  let x : F3S_FinishWitness.Primitives finish v p a := ⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,ha0,ha1,hw,has,hp,hd⟩
  exact ⟨x,fun leaves=>F3T_Leaves.apply_values finish v p a H trace parsed q tr data D i x leaves
    ⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,ha0,ha1,hw,has,hp,hd,cont⟩⟩

#print axioms actual
end AspisR1.F3V_Leaves
end
