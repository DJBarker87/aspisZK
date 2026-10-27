import RPv_FJh_ProjectedCall
import RPv_FJh_GroupBounds
import RPv_FJh_SlicePackValue
import RPv_FJh_PreparedCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_ProjectedCallValue
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM Decode Canonical)
open FIv_NativeArithmetic (qm)
open FIv_PreparedNew (NP prepared)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings)
open FJh_ProjectedCall (Capture call)
open FJh_ProjectedAfter (Packed)
open ExtractedMaskPreparedState (PreparedFor)
open FJe_Sum3Value (cell)
def model (o : Openings) (internal : State) (theta : QM) (lead full : Packed)
    (w : Array QM 3#usize) (g : Fin 4) :=
  Decode theta *
    (Decode (cell w ⟨0,by decide⟩)*(FJh_SlicePackValue.pack o.succ_z g-decoded lead g)+
     Decode (cell w ⟨1,by decide⟩)*(FJh_SlicePackValue.pack o.succ_z g-decoded full g)+
     Decode (cell w ⟨2,by decide⟩)*(FJh_SlicePackValue.pack o.succ_z g-FJh_SlicePackValue.pack internal g))
/-- Both actual slices/packs,three differences,sum3,and block multiplication
are joined on the SAME selected output call and its ordered prepared map. -/
theorem value (o : Openings) (internal : State) (theta : QM)
    (block : NP) (p : Array NP 3#usize) (lead full : Packed) (w : Array QM 3#usize)
    (g : Usize) (hg : g.val<4) (out : QM) (last : Capture)
    (ct : canonical o.succ_z) (ci : canonical internal) (cb : Canonical theta)
    (cl : canonical lead) (cf : canonical full) (cw : canonical w)
    (rp : FIq_Native.core.array.Array.map (BuiltinFnMut QM NP) w field.PreparedQm31Multiplier.new=ok p)
    (rb : field.PreparedQm31Multiplier.new theta=ok block)
    (run : call (o,internal,block,p,lead,full) g=ok (out,last)) :
    Canonical out ∧ Decode out=model o internal theta lead full w ⟨g.val,hg⟩ ∧
      last=(o,internal,block,p,lead,full) := by
  obtain ⟨start,stop,ts,ins,target,ip,rs,re,rts,rt,rins,ri,ra,hlast⟩ :=
    FJh_ProjectedCall.reached o internal block p lead full g out last run
  have bounds := FJh_GroupBounds.value g start stop hg rs re
  have finish : stop.val=start.val+4 := by omega
  have vt := FJh_SlicePackValue.value o.succ_z start stop g ts target hg bounds.1 finish bounds.2.2.2 ct rts rt
  have vi := FJh_SlicePackValue.value internal start stop g ins ip hg bounds.1 finish bounds.2.2.2 ci rins ri
  have vo := FJh_ProjectedAfter.value target ip theta lead full w p block g hg out
    vt.1 vi.1 cb cl cf cw (FJh_PreparedCells.value w p cw rp)
    (FIv_PreparedNew.valid theta block cb rb) ra
  refine ⟨vo.1,vo.2.trans ?_,hlast⟩
  exact congrArg₂ (fun t n : FJh_Base.Exact=>Decode theta *
    (Decode (cell w ⟨0,by decide⟩)*(t-decoded lead ⟨g.val,hg⟩)+
     Decode (cell w ⟨1,by decide⟩)*(t-decoded full ⟨g.val,hg⟩)+
     Decode (cell w ⟨2,by decide⟩)*(t-n))) vt.2 vi.2
#print axioms value
end AspisR1.FJh_ProjectedCallValue
end
