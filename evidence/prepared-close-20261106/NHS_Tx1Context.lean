import NHL_Tx1Model
import NFW_Invert
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_Tx1Context
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NHL_Tx1Stages
/-- Invert the actual beforeQuery prefix. The complete Context and both
initializer calls share the same prepared/scratch/weights allocations. -/
theorem source (ops : Ops) {H : Type} (prepareCall : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (publicBytes proof : Slice U8) (k : Usize) (hash : H) (c : Context)
 (run : beforeQuery ops prepareCall D pub publicBytes proof k hash none=ok (.Ok c)) :
 ∃ zero p scratch a geometry b,
 aspis_core.field.wide_exact.WideExact.ZERO ops=ok zero ∧
 prepareCall D pub proof hash none (Array.repeat 29#usize zero)=ok (.Ok p,scratch) ∧
 ops.op20 .S2=ok (.Ok a) ∧ ops.op19 p.queries 0#usize k=ok (.Ok geometry) ∧
 ops.op18 a.weights.deref=ok (.Ok b) ∧ c=Context.mk p a scratch geometry b := by
 unfold beforeQuery at run
 split at run
 · cases run
 · obtain ⟨parse,parseCall,run⟩ := NFW_Invert.bind _ _ _ run
   cases parse with
   | Err e =>
     simp only [core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
       core.convert.FromSame.from,bind_tc_ok] at run
     cases run
   | Ok parsed =>
     simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
     obtain ⟨scan,scanCall,run⟩ := NFW_Invert.bind _ _ _ run
     cases scan with
     | Err e =>
       simp only [core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
         core.convert.FromSame.from,bind_tc_ok] at run
       cases run
     | Ok u =>
       simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,verifier.mark] at run
       obtain ⟨zero,zeroCall,run⟩ := NFW_Invert.bind _ _ _ run
       obtain ⟨pair,preparedCall,run⟩ := NFW_Invert.bind _ _ _ run
       rcases pair with ⟨reply,scratch⟩
       dsimp! only at run
       cases reply with
       | Err e =>
         simp only [core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
           core.convert.FromSame.from,bind_tc_ok] at run
         cases run
       | Ok p =>
         simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
         obtain ⟨initial,initialCall,run⟩ := NFW_Invert.bind _ _ _ run
         cases initial with
         | Err e =>
           simp only [core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
             core.convert.FromSame.from,bind_tc_ok] at run
           cases run
         | Ok a =>
           simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,verifier.mark] at run
           obtain ⟨off,offCall,run⟩ := NFW_Invert.bind _ _ _ run
           obtain ⟨stop,stopCall,run⟩ := NFW_Invert.bind _ _ _ run
           obtain ⟨slice,sliceCall,run⟩ := NFW_Invert.bind _ _ _ run
           obtain ⟨rootResult,rootCall,run⟩ := NFW_Invert.bind _ _ _ run
           obtain ⟨root,unwrapCall,run⟩ := NFW_Invert.bind _ _ _ run
           obtain ⟨batch,batchCall,run⟩ := NFW_Invert.bind _ _ _ run
           cases batch with
           | Err e =>
             simp only [core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
               core.convert.FromSame.from,bind_tc_ok] at run
             cases run
           | Ok u =>
             simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,verifier.mark] at run
             obtain ⟨geometry,geometryCall,run⟩ := NFW_Invert.bind _ _ _ run
             cases geometry with
             | Err e =>
               simp only [core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                 core.convert.FromSame.from,bind_tc_ok] at run
               cases run
             | Ok geometry =>
               simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
               obtain ⟨pending,pendingCall,run⟩ := NFW_Invert.bind _ _ _ run
               cases pending with
               | Err e =>
                 simp only [core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                   core.convert.FromSame.from,bind_tc_ok] at run
                 cases run
               | Ok b =>
                 simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                 have same := core.result.Result.Ok.inj (Result.ok.inj run)
                 exact ⟨zero,p,scratch,a,geometry,b,zeroCall,preparedCall,initialCall,geometryCall,pendingCall,same.symm⟩
#print axioms source
end AspisR1.NHS_Tx1Context
