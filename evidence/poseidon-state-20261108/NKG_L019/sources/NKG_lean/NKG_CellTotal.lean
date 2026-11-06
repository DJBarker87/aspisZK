import NKG_AfterTotal
import NKG_SliceTotal
import RPv_FJh_ProjectedArrayValue
import NDO_JFy_BoundedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_CellTotal
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM Canonical)
open FIv_NativeArithmetic (qm)
open FIv_PreparedNew (NP prepared)
open FIw_ArrayValue (canonical)
open FJa_PoseidonOrigins (Openings)
open FJh_ProjectedAfter (Packed)
open FJh_ProjectedCall (Capture call)
/-- One arbitrary packed group. All slice, pack, subtraction, prepared-sum
and multiply domains follow from SAME arrays and actual constructor Results. -/
theorem cell (o : Openings) (internal : State) (theta : QM) (block : NP)
 (p : Array NP 3#usize) (lead full : Packed) (w : Array QM 3#usize)
 (g : Usize) (hg : g.val<4) (ct : canonical o.succ_z) (ci : canonical internal)
 (cb : Canonical theta) (cl : canonical lead) (cf : canonical full) (cw : canonical w)
 (rp : FIq_Native.core.array.Array.map (BuiltinFnMut QM NP) w field.PreparedQm31Multiplier.new=ok p)
 (rb : field.PreparedQm31Multiplier.new theta=ok block) :
 ∃ out,call (o,internal,block,p,lead,full) g=ok (out,(o,internal,block,p,lead,full)) ∧ Canonical out := by
 obtain ⟨start,rs,vs⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=4#usize) (y:=g) (by scalar_tac))
 change start.val=4*g.val at vs
 obtain ⟨finish,re,ve⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=start) (y:=4#usize) (by scalar_tac))
 change finish.val=start.val+4 at ve
 have hb : finish.val≤16 := by omega
 have hle : start.val≤finish.val := by omega
 obtain ⟨rts,lts,cts⟩ := NKG_SliceTotal.slice o.succ_z start finish hle hb ve ct
 obtain ⟨target,rt,ctarget⟩ := FIw_PackTotal.source (FJh_GroupSlices.sliceAt o.succ_z start finish) lts cts
 obtain ⟨ris,lis,cis⟩ := NKG_SliceTotal.slice internal start finish hle hb ve ci
 obtain ⟨ip,ri,cip⟩ := FIw_PackTotal.source (FJh_GroupSlices.sliceAt internal start finish) lis cis
 obtain ⟨out,ra,ca⟩ := NKG_AfterTotal.result target ip theta lead full w p block g hg
   ctarget cip cb cl cf cw (FJh_PreparedCells.value w p cw rp) (FIv_PreparedNew.valid theta block cb rb)
 refine ⟨out,?_,ca⟩
 rw [FJh_ProjectedCall.factor]
 simp only [rs,re,rts,rt,ris,ri,ra,bind_tc_ok]

/-- Native from_fn construction is framed by the pinned safe std builder;
four arbitrary-group laws, never a whole-buffer arithmetic unroll in Kani. -/
theorem array (o : Openings) (internal : State) (theta : QM) (block : NP)
 (p : Array NP 3#usize) (lead full : Packed) (w : Array QM 3#usize)
 (ct : canonical o.succ_z) (ci : canonical internal) (cb : Canonical theta)
 (cl : canonical lead) (cf : canonical full) (cw : canonical w)
 (rp : FIq_Native.core.array.Array.map (BuiltinFnMut QM NP) w field.PreparedQm31Multiplier.new=ok p)
 (rb : field.PreparedQm31Multiplier.new theta=ok block) :
 ∃ out,array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
   FJh_ProjectedArrayValue.callback field.QM31.ZERO (o,internal,block,p,lead,full)=ok out ∧ canonical out := by
 obtain ⟨out,run,co⟩ := JFy_BoundedCanonical.source Canonical 4#usize FJh_ProjectedArrayValue.callback
   (o,internal,block,p,lead,full) (by intro g hg;exact cell o internal theta block p lead full w g hg ct ci cb cl cf cw rp rb)
 exact ⟨out,run,co⟩
#print cell
#print axioms cell
#print array
#print axioms array
end AspisR1.NKG_CellTotal
end
