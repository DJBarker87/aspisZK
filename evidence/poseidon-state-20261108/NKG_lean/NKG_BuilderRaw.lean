import NKG_OracleChoices
import NKG_GroupRaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_BuilderRaw
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FJh_ProjectedCall (Capture call)
open NKG_OracleCuts (Packed)
open NKG_InternalChoices (get)
def reply (c : Capture) (g : Usize) : NQ := (get (call c g) (field.QM31.ZERO,c)).1
def values (c : Capture) : Packed :=
 ⟨List.ofFn (fun i : Fin (4#usize).val=>reply c (NKG_GroupFrame.index ⟨i.val,i.isLt⟩)),by simp⟩
theorem reply_ok (c : Capture) (g : Usize) (x : NQ) (last : Capture)
 (run : call c g=ok (x,last)) : reply c g=x := by unfold reply;rw [run];rfl
/-- Exact raw array from the SAME four callback Results, preserving the whole
capture. This is a source/std law, paired with K026/K027/K028 natively. -/
theorem source (c : Capture) (out : Packed)
 (run : array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy FJh_ProjectedArrayValue.callback
   field.QM31.ZERO c=ok out) : out=values c := by
 rcases c with ⟨o,internal,block,p,lead,full⟩
 let c : Capture := (o,internal,block,p,lead,full)
 let model : Nat → NQ := fun n=>if h:n<4 then reply c (NKG_GroupFrame.index ⟨n,h⟩) else field.QM31.ZERO
 have built := FIx_Builder.fromFn 4#usize FJh_ProjectedArrayValue.callback (fun _=>True) id model c out (by
   intro i hi x last called
   change call c i=ok (x,last) at called
   have h4 : i.val<4 := hi
   have eq : NKG_GroupFrame.index ⟨i.val,h4⟩=i := UScalar.eq_of_val_eq rfl
   obtain ⟨start,stop,ts,ins,target,ip,rs,re,rts,rt,rins,ri,ra,hlast⟩ :=
     FJh_ProjectedCall.reached o internal block p lead full i x last called
   refine ⟨True.intro,?_,hlast⟩
   change x=model i.val
   dsimp only [model]
   rw [dif_pos h4,eq]
   exact (reply_ok c i x last called).symm) run
 apply Subtype.ext
 change out.val=List.ofFn (fun i : Fin (4#usize).val=>reply c (NKG_GroupFrame.index ⟨i.val,i.isLt⟩))
 have e := built.2
 simp only [List.map_id] at e
 refine e.trans (congrArg (fun f : Fin (4#usize).val → NQ=>List.ofFn f) (funext ?_))
 intro i
 change (if h:i.val<4 then reply c (NKG_GroupFrame.index ⟨i.val,h⟩) else field.QM31.ZERO)=_
 rw [dif_pos (show i.val<4 from i.isLt)]
#print reply_ok
#print axioms reply_ok
#print source
#print axioms source
end AspisR1.NKG_BuilderRaw
end
