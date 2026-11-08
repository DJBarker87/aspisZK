import NNG_ModelProjection345
import NNG_ArgsPort345
import NNG_ParentAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TotalProducer345
open RSL

/-- All-Args source port: reject the actual route/count failures before any
slice reification. On the reached branch, internally derive every Rust bound
of the source-preserving account projection and run the fresh emitted parent. -/
def producer (a : TX1_345.Args) (env : Env) : Obs (Except ProgramError Bytes) :=
 if good : TX1_345.badRoute a=false then
  NNG_Native345.producer (NNG_ReifyCore345.input (NNG_ProjectAccounts345.args a)
   (NNG_ArgsPort345.bounds a good)) env
 else NNG_Pure345.silent (.error .invalidInstructionData)

/-- Complete original-input association. Oversized fields are handled by
checked source-preserving normalization; no reference fallback is selected. -/
theorem interpretation (a : TX1_345.Args) (env : Env) :
 producer a env=NNG_Model345.interpretation a env := by
 unfold producer
 split
 · rw [NNG_ParentAssociation345.source,NNG_ReifyCore345.inverse,NNG_ModelProjection345.source]
 · rename_i bad
   have route : TX1_345.badRoute a=true := by
    cases h : TX1_345.badRoute a with
    | true=>rfl
    | false=>exact False.elim (bad h)
   unfold NNG_Model345.interpretation NNG_Phases345.run
   rw [if_pos route]
#print axioms interpretation

/-- Every complete native parent, with no own-input, success or representation
premise, agrees at its original program/account/data fields and full prefix. -/
theorem native {W : Type} (s : NMT_345.Parent W) (env : Env) :
 NNG_Native345.producer s env=producer (NNG_ProjectFrames345.original s) env :=
 (NNG_ParentAssociation345.source s env).trans (interpretation _ env).symm
#print axioms native
end AspisR1.NNG_TotalProducer345
