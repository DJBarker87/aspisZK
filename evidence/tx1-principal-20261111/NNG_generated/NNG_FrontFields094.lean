import NNG_SemanticFields094
import NNG_FrontValue087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FrontFields094
open Aeneas Aeneas.Std Result NMP_prepare NMP_PrepareSteps
abbrev Parent := NMP_Emitted.Parent Unit Unit
def Fields (out : r1_semantic.Verified Unit) : Prop :=
 (∀ q∈(NMP_Transport.toT11 out).alpha.val,NHS_Fields.QCanonical q) ∧
 (∀ z∈(NMP_Transport.toT11 out).z.val,NHS_Fields.QCanonical z.x ∧ NHS_Fields.QCanonical z.y)

theorem observed (env : RSL.Env) (s : Parent) (v : verifier.View)
 (out : r1_semantic.Verified Unit) (outv : verifier.View)
 (native : NNG_FrontValue087.observed (NNG_PrepareEmission087.calls env) s v=.ok (.Ok (out,outv))) : Fields out := by
 unfold NNG_FrontValue087.observed at native
 obtain ⟨r,called,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 cases r with
 | Err e=>cases tail
 | Ok sem=>
   have same := Prod.mk.inj (core.result.Result.Ok.inj (Result.ok.inj tail))
   have equal : sem=out := same.1
   subst sem
   change NNG_Context137.emitted (NNG_Context137.calls env)
    ⟨s.digest,s.publicValue,v.semantic,s.hash,s.observer⟩=.ok (.Ok out) at called
   exact NNG_SemanticFields094.returned env _ out called
#print axioms observed

theorem view (env : RSL.Env) (s : Parent) (semantic y1 : Slice U8)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.view (NNG_PrepareEmission087.calls env) s semantic y1=.ok (.Ok (out,v))) : Fields out := by
 unfold NNG_FrontValue087.view at native
 obtain ⟨r,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 cases r with
 | Err e=>cases tail
 | Ok input=>exact observed env s input out v tail
#print axioms view

theorem values (env : RSL.Env) (s : Parent) (semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.values (NNG_PrepareEmission087.calls env) s semantic y1 back vecBack=.ok (.Ok (out,v))) : Fields out := by
 unfold NNG_FrontValue087.values at native
 obtain ⟨src,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 obtain ⟨pair,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ tail
 rcases pair with ⟨r,after⟩
 cases r with
 | Err e=>cases tail
 | Ok u=>
   obtain ⟨semantic,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ tail
   obtain ⟨y1,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ tail
   exact view env s semantic y1 out v tail
#print axioms values

theorem semantic (env : RSL.Env) (s : Parent) (semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.semantic (NNG_PrepareEmission087.calls env) s semantic y1 back vecBack=.ok (.Ok (out,v))) : Fields out := by
 unfold NNG_FrontValue087.semantic at native
 obtain ⟨src,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 obtain ⟨pair,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ tail
 rcases pair with ⟨r,after⟩
 cases r with
 | Err e=>cases tail
 | Ok u=>exact values env s after y1 back vecBack out v tail
#print axioms semantic

theorem split (env : RSL.Env) (s : Parent) (logical : alloc.vec.Vec U8)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.split (NNG_PrepareEmission087.calls env) s logical=.ok (.Ok (out,v))) : Fields out := by
 unfold NNG_FrontValue087.split at native
 obtain ⟨pair,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 rcases pair with ⟨⟨semantic,y1⟩,back⟩
 exact NNG_FrontFields094.semantic env s semantic y1 back (alloc.vec.Vec.deref_mut logical).2 out v tail
#print axioms split

theorem returned (env : RSL.Env) (s : Parent) (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.tree (NNG_PrepareEmission087.calls env) s=.ok (.Ok (out,v))) : Fields out := by
 unfold NNG_FrontValue087.tree at native
 obtain ⟨r,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 cases r with
 | Err e=>cases tail
 | Ok logical=>exact split env s logical out v tail
#print axioms returned
end AspisR1.NNG_FrontFields094
