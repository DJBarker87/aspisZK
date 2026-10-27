import JFn_LineTotal
import SAQ_LineQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_LineArrayTotal
open Aeneas Aeneas.Std Result
open SAQ_WideABI

theorem source (alpha : E) (v : Array E 4#usize) (inverse : Array U32 5#usize)
    (hAlpha : Port4C_QueryArithmetic.CanonE alpha)
    (canonical : ∀ j : Fin 4,
      Port4C_QueryArithmetic.CanonE (v.val[j.val]'(by rw [v.property];exact j.isLt))) :
    ∃ out, SAQ_LineQuery.line alpha v inverse=ok out ∧ Port4C_QueryArithmetic.CanonE out := by
  obtain ⟨a,b,c,d,hv⟩ := SAQ_LineArrays.four v
  obtain ⟨ix,iy,lx,ly,lz,hi⟩ := SAQ_LineArrays.five inverse
  subst v
  subst inverse
  have ca := (w_canonical a).mp (canonical ⟨0,by decide⟩)
  have cb := (w_canonical b).mp (canonical ⟨1,by decide⟩)
  have cc := (w_canonical c).mp (canonical ⟨2,by decide⟩)
  have cd := (w_canonical d).mp (canonical ⟨3,by decide⟩)
  obtain ⟨out,run,canon⟩ := JFn_LineTotal.source (toW alpha) (toW a) (toW b) (toW c) (toW d)
    ix iy lx ly lz ((w_canonical alpha).mp hAlpha) ca cb cc cd
  refine ⟨fromW out,?_,(w_canonical (fromW out)).mpr canon⟩
  simpa only [SAQ_LineQuery.line,SAQ_LineQuery.toValues,Array.make,Array.to_slice,
    List.map_cons,List.map_nil,bind_tc_ok] using
    congrArg (fun r => do let z ← r;ok (fromW z)) run

#print axioms source
end AspisR1.JFn_LineArrayTotal
end
