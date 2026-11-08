import NNG_Reify345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Producer345
open RSL

/-- Total observation interpreter of the checked emitted control flow. As in
NNF_Dispatch/NNF_Reify, the same source control rule extends the logical list
carrier; Rust representability occurs only in the reification certificate.
All child/library fields and all local allocation observations are fixed. -/
def producer (a : TX1_345.Args) (env : Env) : Obs (Except ProgramError Bytes) :=
 NNG_Phases345.run LIB_Instances.VL LIB_Instances.C (fun _=>true)
  NNG_Producer328.producer a env

/-- Every native parent, with no input premise, is interpreted at its complete
original arguments. This is the full fresh emitted-parent observation law. -/
theorem native {W : Type} (s : NMT_345.Parent W) (env : Env) :
 NNG_Native345.producer s env=producer (NNG_ProjectFrames345.original s) env :=
 NNG_ParentAssociation345.source s env

/-- Original logical arguments reify exactly whenever they have a Rust
carrier. These are representation facts, not RowSpec own-input clauses. -/
theorem reified (a : TX1_345.Args) (h : NNG_Reify345.representable a) (env : Env) :
 NNG_Native345.producer (NNG_Reify345.input a h) env=producer a env :=
 NNG_Reify345.source a h env
#print axioms native
#print axioms reified
end AspisR1.NNG_Producer345
