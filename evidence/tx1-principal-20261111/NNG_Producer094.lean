import NNG_Input094
import NNG_Events094
import NNG_EraseHead094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Producer094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136
abbrev Args := NNG_Input094.Args

def port : NNG_Context094.Output → Except LIB_VCarriers.VErr RSL.Bytes
 | .Ok bytes=>.ok (LIB_Carriers.bytes bytes.deref)
 | .Err error=>.error (NNG_ParseCall094.error error)

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit) :
 erase (NNG_Tree094.f_guard (NNG_InstalledCalls094.calls env) s)=
 NNG_Context094.body (NNG_InstalledCalls094.calls env) s :=
 NNG_EraseHead094.source _ _
#print axioms source

/-- Value from the fresh emitted body; chronological effects from its
source-ordered typed call tree at those exact original input carriers. -/
def producer (a : Args) (obs : RSL.Observer) (env : RSL.Env) :
 RSL.Obs (Except LIB_Instances.VL.VErr RSL.Bytes) :=
 let c:=NNG_InstalledCalls094.calls env
 let s:=NNG_Input094.input a obs env
 ⟨exit port (NNG_Context094.body c s),
  (run (NNG_Tree094.f_guard c s)).2.flatMap (NNG_Events094.events env)⟩

theorem tree (a : Args) (obs : RSL.Observer) (env : RSL.Env) :
 producer a obs env=observation port (NNG_Events094.events env)
  (NNG_Tree094.f_guard (NNG_InstalledCalls094.calls env) (NNG_Input094.input a obs env)) := by
 unfold producer observation
 dsimp only
 rw [run_result,source]
 rfl
#print axioms tree
end AspisR1.NNG_Producer094
