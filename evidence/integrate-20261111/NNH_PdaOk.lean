import NNH_Tx2ModelSlots
import NNH_OptionOk
set_option autoImplicit false
noncomputable section
namespace NNH_PdaOk
open RSL NND_Returned
attribute [local instance] Classical.propDecidable

theorem guard (env : Env) (bad : Bool) (seeds : List Bytes) (program expected : B32)
 (success : (if bad then Except.error ProgramError.invalidAccountData else
  ebind (NNH_RegistryEval.pdaValue env seeds program)
   (fun k => echeck (decide (k ≠ expected)) .invalidAccountData))=.ok ()) :
 bad=false ∧ env.pda seeds program=some expected := by
 cases bad with
 | true => cases success
 | false =>
  refine ⟨rfl,?_⟩
  change ebind (NNH_RegistryEval.pdaValue env seeds program)
   (fun k => echeck (decide (k ≠ expected)) .invalidAccountData)=.ok () at success
  unfold NNH_RegistryEval.pdaValue at success
  cases source : env.pda seeds program with
  | none => simp only [source,option,ebind] at success; cases success
  | some k =>
   simp only [source,option,ebind] at success
   unfold echeck at success
   split at success
   · cases success
   · rename_i h
     have same : k=expected := by simpa using h
     simpa only [same] using source

open Aeneas Aeneas.Std AdapterRw NND_Carrier

theorem native (base : Ops) (env : Env) (seeds : Slice (Slice U8))
 (program expected : solana_pubkey.Pubkey)
 (success : env.pda (seeds.val.map bytes) (key program)=some (key expected)) :
 (NNH_Tx2ModelSlots.install base env).op38 seeds program=.ok (.Ok expected) := by
 change NNH_MRegistryOps.pda env seeds program=_
 unfold NNH_MRegistryOps.pda
 simp only [success,key_back]
#print axioms guard
#print axioms native
end NNH_PdaOk
