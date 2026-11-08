import NNG_ReadyView087
import NNG_FrontValue087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FrontOrigin094
open Aeneas Aeneas.Std Result NMP_prepare NMP_PrepareSteps
abbrev Parent := NMP_Emitted.Parent Unit Unit
/-- The original observed call at the SAME returned View; no new or
independently selected successful semantic execution is assumed. -/
def Origin (env : RSL.Env) (s : Parent) (out : r1_semantic.Verified Unit) (v : verifier.View) : Prop :=
 NNG_Context137.emitted (NNG_Context137.calls env)
  ⟨s.digest,s.publicValue,v.semantic,s.hash,s.observer⟩=.ok (.Ok out)

theorem observed (env : RSL.Env) (s : Parent) (v : verifier.View)
 (out : r1_semantic.Verified Unit) (outv : verifier.View)
 (native : NNG_FrontValue087.observed (NNG_PrepareEmission087.calls env) s v=.ok (.Ok (out,outv))) : Origin env s out outv := by
 unfold NNG_FrontValue087.observed at native
 obtain ⟨r,called,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 cases r with
 | Err e=>cases tail
 | Ok sem=>
   have same := Prod.mk.inj (core.result.Result.Ok.inj (Result.ok.inj tail))
   have equal : sem=out := same.1
   subst sem
   have equalView : v=outv := same.2
   subst outv
   change NNG_Context137.emitted (NNG_Context137.calls env)
    ⟨s.digest,s.publicValue,v.semantic,s.hash,s.observer⟩=.ok (.Ok out) at called
   exact called
#print axioms observed

theorem view (env : RSL.Env) (s : Parent) (semantic y1 : Slice U8)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.view (NNG_PrepareEmission087.calls env) s semantic y1=.ok (.Ok (out,v))) : Origin env s out v := by
 unfold NNG_FrontValue087.view at native
 obtain ⟨r,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 cases r with
 | Err e=>cases tail
 | Ok input=>exact observed env s input out v tail
#print axioms view

theorem values (env : RSL.Env) (s : Parent) (semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack)
 (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.values (NNG_PrepareEmission087.calls env) s semantic y1 back vecBack=.ok (.Ok (out,v))) : Origin env s out v := by
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
 (native : NNG_FrontValue087.semantic (NNG_PrepareEmission087.calls env) s semantic y1 back vecBack=.ok (.Ok (out,v))) : Origin env s out v := by
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
 (native : NNG_FrontValue087.split (NNG_PrepareEmission087.calls env) s logical=.ok (.Ok (out,v))) : Origin env s out v := by
 unfold NNG_FrontValue087.split at native
 obtain ⟨pair,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 rcases pair with ⟨⟨semantic,y1⟩,back⟩
 exact NNG_FrontOrigin094.semantic env s semantic y1 back (alloc.vec.Vec.deref_mut logical).2 out v tail
#print axioms split

theorem returned (env : RSL.Env) (s : Parent) (out : r1_semantic.Verified Unit) (v : verifier.View)
 (native : NNG_FrontValue087.tree (NNG_PrepareEmission087.calls env) s=.ok (.Ok (out,v))) : Origin env s out v := by
 unfold NNG_FrontValue087.tree at native
 obtain ⟨r,_,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 cases r with
 | Err e=>cases tail
 | Ok logical=>exact split env s logical out v tail
#print axioms returned
end AspisR1.NNG_FrontOrigin094
