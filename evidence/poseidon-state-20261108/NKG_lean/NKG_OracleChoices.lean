import NKG_OracleSource
import NKG_GroupFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_OracleChoices
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical)
open FJa_PoseidonOrigins (Openings Selectors)
open FJh_Base (State)
open NKG_OracleCuts (Packed Prepared Three)
open NKG_InternalChoices (get get_ok)
def zeroPrepared : NP := ⟨Array.repeat 3#usize (Array.repeat 3#usize 0#u32)⟩
def leadingLow (s : Selectors) := get (Array.index_usize s.local 0#usize) field.QM31.ZERO
def fullLow (s : Selectors) := get (FJa_PoseidonOrigins.fullFold s) field.QM31.ZERO
def internalLow (s : Selectors) := get (FJa_PoseidonOrigins.internalFold s) field.QM31.ZERO
def weights (s : Selectors) : Three := Array.make 3#usize [leadingLow s,fullLow s,internalLow s]
def leading (o : Openings) := get (state_only_poseidon.leading_pair_packed o) (Array.repeat 4#usize field.QM31.ZERO)
def full (o : Openings) (s : Selectors) := get (state_only_poseidon.interpolated_full_pair_packed o.z s.local) (Array.repeat 4#usize field.QM31.ZERO)
def internal (o : Openings) (s : Selectors) := get (state_only_poseidon.interpolated_internal_pair o.z s.local) (Array.repeat 16#usize field.QM31.ZERO)
def prepared (s : Selectors) : Prepared := get (FIq_Native.core.array.Array.map
 (BuiltinFnMut NQ NP) (weights s) field.PreparedQm31Multiplier.new) (Array.repeat 3#usize zeroPrepared)
def block (s : Selectors) := get (field.PreparedQm31Multiplier.new s.block) zeroPrepared
def capture (o : Openings) (s : Selectors) : FJh_ProjectedCall.Capture :=
 (o,internal o s,block s,prepared s,leading o,full o s)
/-- Derived complete child Results and next-stage domains, never a root premise. -/
structure Ready (o : Openings) (s : Selectors) : Prop where
 leadingCanonical : canonical (leading o)
 fullCanonical : canonical (full o s)
 internalCanonical : canonical (internal o s)
 weightsCanonical : canonical (weights s)
 preparedCall : FIq_Native.core.array.Array.map (BuiltinFnMut NQ NP) (weights s) field.PreparedQm31Multiplier.new=ok (prepared s)
 blockCall : field.PreparedQm31Multiplier.new s.block=ok (block s)

theorem ready (o : Openings) (s : Selectors)
 (hz : canonical o.z) (hx : canonical o.xor12_z) (hs : canonical s.local) (hb : Canon s.block) : Ready o s := by
 obtain ⟨l0,r0,c0⟩ := JFy_ArrayTotal.read s.local 0#usize (by decide) hs
 obtain ⟨lf,rf,cf⟩ := NKG_LowTotal.full s hs
 obtain ⟨li,ri,ci⟩ := NKG_LowTotal.internal s hs
 have v0 : leadingLow s=l0 := get_ok _ _ _ r0
 have vf : fullLow s=lf := get_ok _ _ _ rf
 have vi : internalLow s=li := get_ok _ _ _ ri
 have cw : canonical (weights s) := by
   unfold weights
   rw [v0,vf,vi]
   intro x hx
   simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl|rfl|rfl
   · exact c0
   · exact cf
   · exact ci
 obtain ⟨lead,rl,cl,_⟩ := NIH_Leading.result o hz hx
 obtain ⟨f,rfull,cfull,_⟩ := NKG_FullSource.result o.z s.local hz hs
 obtain ⟨i,rinternal,cinternal,_⟩ := NKG_InternalSource.result o.z s.local hz hs
 have vl : leading o=lead := get_ok _ _ _ rl
 have vfull : full o s=f := get_ok _ _ _ rfull
 have vint : internal o s=i := get_ok _ _ _ rinternal
 obtain ⟨p,rp⟩ := NKG_PreparedMap.result (weights s) cw
 obtain ⟨b,rb,_⟩ := FIv_PreparedNewTotal.value s.block hb
 have vp : prepared s=p := get_ok _ _ _ rp
 have vb : block s=b := get_ok _ _ _ rb
 exact ⟨vl.symm ▸ cl,vfull.symm ▸ cfull,vint.symm ▸ cinternal,cw,vp.symm ▸ rp,vb.symm ▸ rb⟩
/-- Remove no prefix. Every chosen value is obtained from the SAME complete
parent call's actual child Results in source order. -/
theorem builder (o : Openings) (s : Selectors) (out : Packed)
 (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out) :
 array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy FJh_ProjectedArrayValue.callback
   field.QM31.ZERO (capture o s)=ok out := by
 obtain ⟨l0,lf,li,lead,f,i,p,b,r0,rf,ri,rl,rfull,rinternal,rp,rb,rarr⟩ := FJa_PoseidonOrigins.reached o s out run
 have v0 : leadingLow s=l0 := get_ok _ _ _ r0
 have vf : fullLow s=lf := get_ok _ _ _ rf
 have vi : internalLow s=li := get_ok _ _ _ ri
 have vl : leading o=lead := get_ok _ _ _ rl
 have vfull : full o s=f := get_ok _ _ _ rfull
 have vint : internal o s=i := get_ok _ _ _ rinternal
 have vw : weights s=Array.make 3#usize [l0,lf,li] := (congrArg₂ (fun a b=>Array.make 3#usize [a,b,internalLow s]) v0 vf).trans (congrArg (fun c=>Array.make 3#usize [l0,lf,c]) vi)
 have vp : prepared s=p := by unfold prepared;rw [vw];exact get_ok _ _ _ rp
 have vb : block s=b := get_ok _ _ _ rb
 simpa only [capture,vint,vb,vp,vl,vfull] using rarr
#print ready
#print axioms ready
#print builder
#print axioms builder
end AspisR1.NKG_OracleChoices
end
