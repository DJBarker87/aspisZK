import NNG_PreludeAssociation345
import NNG_MiddleAssociation345
import NNG_TailAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SelectedAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

theorem source {W : Type} (s : Selected W) (env : RSL.Env)
 (route : s.data.val.length=2) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_Tree345.selected (NNG_Calls345.calls env) s)=
 NNG_Phases345.bodyRun LIB_Instances.VL LIB_Instances.C (fun _=>true)
 NNG_Producer328.producer (NNG_ProjectFrames345.selected s) env := by
 change observation _ _ (NNG_TreeBase345.prelude (NNG_Calls345.calls env) s
   (fun d=>NNG_TreeBase345.middle (NNG_Calls345.calls env) d (NNG_TreeTail345.bounds (NNG_Calls345.calls env))))=
  NNG_PreludeAssociation345.canonical (NNG_ProjectFrames345.selected s) _
 apply NNG_PreludeAssociation345.source
 intro ck pub st hd
 apply NNG_MiddleAssociation345.source _ env hd
 intro hv candidate proof
 exact NNG_TailAssociation345.source ⟨⟨⟨⟨⟨s,ck⟩,pub⟩,st⟩,candidate⟩,proof⟩ env hd hv route
#print axioms source
end AspisR1.NNG_SelectedAssociation345
