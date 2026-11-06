import NKG_GroupFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_GroupRaw
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_PreparedNew (NP)
open FJh_Base (State cell)
open FIw_ArrayValue (canonical)
open FJa_PoseidonOrigins (Openings)
open FJh_ProjectedCall (Capture call)
open NKG_OracleCuts (Packed Prepared)
open NKG_InternalChoices (get_ok)
/-- All native split replies are the SAME source-child Results, not an inverse
association of independently chosen logs. This helper's run is discharged by
NKG_CellTotal at the positive root. -/
theorem value (o : Openings) (internal : State) (block : NP) (p : Prepared)
 (lead full : Packed) (g : Fin 4) (out : NQ) (last : Capture)
 (ct : canonical o.succ_z) (ci : canonical internal)
 (run : call (o,internal,block,p,lead,full) (NKG_GroupFrame.index g)=ok (out,last)) :
 NKG_GroupFrame.model o.succ_z internal lead full p block g=out := by
 obtain ⟨first,final,ts,ins,target,ip,rs,re,rts,rt,rins,ri,ra,_⟩ :=
   FJh_ProjectedCall.reached o internal block p lead full (NKG_GroupFrame.index g) out last run
 have bounds := FJh_GroupBounds.value (NKG_GroupFrame.index g) first final g.isLt rs re
 have firstEq : first=NKG_GroupFrame.start g := by
   apply UScalar.eq_of_val_eq
   change first.val=4*g.val
   exact bounds.1
 have finalEq : final=NKG_GroupFrame.stop g := by
   apply UScalar.eq_of_val_eq
   change final.val=4*g.val+4
   exact bounds.2.1
 subst first;subst final
 have hle : (NKG_GroupFrame.start g).val≤(NKG_GroupFrame.stop g).val := bounds.2.2.1
 have hb : (NKG_GroupFrame.stop g).val≤16 := bounds.2.2.2
 have span : (NKG_GroupFrame.stop g).val=(NKG_GroupFrame.start g).val+4 := rfl
 have st := (NKG_SliceTotal.slice o.succ_z (NKG_GroupFrame.start g) (NKG_GroupFrame.stop g) hle hb span ct).1
 have si := (NKG_SliceTotal.slice internal (NKG_GroupFrame.start g) (NKG_GroupFrame.stop g) hle hb span ci).1
 have ets := Result.ok.inj (rts.symm.trans st)
 have eis := Result.ok.inj (rins.symm.trans si)
 subst ts;subst ins
 have tp : NKG_GroupFrame.pack o.succ_z g=target := get_ok _ _ _ rt
 have ipack : NKG_GroupFrame.pack internal g=ip := get_ok _ _ _ ri
 unfold FJh_ProjectedAfter.source at ra
 obtain ⟨l,rl,ra⟩ := FIv_Map.bind_success _ _ _ ra
 obtain ⟨dl,rdl,ra⟩ := FIv_Map.bind_success _ _ _ ra
 obtain ⟨f,rf,ra⟩ := FIv_Map.bind_success _ _ _ ra
 obtain ⟨df,rdf,ra⟩ := FIv_Map.bind_success _ _ _ ra
 obtain ⟨di,rdi,ra⟩ := FIv_Map.bind_success _ _ _ ra
 obtain ⟨sum,rsum,ra⟩ := FIv_Map.bind_success _ _ _ ra
 have ll : l=cell lead g := Result.ok.inj
   (rl.symm.trans (RawPoseidonExternalRowReads.array_index_usize_ok lead (NKG_GroupFrame.index g) g.isLt))
 have ff : f=cell full g := Result.ok.inj
   (rf.symm.trans (RawPoseidonExternalRowReads.array_index_usize_ok full (NKG_GroupFrame.index g) g.isLt))
 have dlv : NKG_GroupFrame.sub target (cell lead g)=dl := by rw [←ll];exact get_ok _ _ _ rdl
 have dfv : NKG_GroupFrame.sub target (cell full g)=df := by rw [←ff];exact get_ok _ _ _ rdf
 have div : NKG_GroupFrame.sub target ip=di := get_ok _ _ _ rdi
 have sv : NKG_GroupFrame.sum p (Array.make 3#usize [dl,df,di])=sum := get_ok _ _ _ rsum
 have mv : NKG_GroupFrame.mul block sum=out := get_ok _ _ _ ra
 unfold NKG_GroupFrame.model
 rw [tp,ipack,NKG_GroupFrame.differences,dlv,dfv,div,sv,mv]
#print value
#print axioms value
end AspisR1.NKG_GroupRaw
end
