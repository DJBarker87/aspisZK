import NJQ_Checkpoint
import NJI_PolicyCut
set_option autoImplicit false
noncomputable section
namespace NJQ_CheckpointCut
open Aeneas Aeneas.Std Result NJQ_Checkpoint
attribute [local instance] Classical.propDecidable

def prefixResult (b : Slice U8) (len : b.val.length=192) : core.result.Result Unit F :=
 match NJQ_Header.model b 192#usize magic with
 | .Err e=>.Err e
 | .Ok _=>if (trailing b len).val≠List.replicate 16 0#u8 then .Err .NonZeroReserved else
   if masterBytes b len=Array.repeat 32#usize 0#u8 then .Err .ZeroRequiredBinding else
   if domainBytes b len=Array.repeat 32#usize 0#u8 then .Err .ZeroRequiredBinding else .Ok ()

def Coordinates (b : Slice U8) (len : b.val.length=192) (root : Digest) (lanes : Words) (p : C) : Prop :=
 p.bump=NHY_ZeroStep.byte b 7 ∧ p.checkpoint_sequence=NJQ_Words.word b 72 (by omega) ∧
 (∀ i,i<32 → NHY_ArrayExt.coord p.master i=NHY_ZeroStep.byte b (8+i) ∧
   NHY_ArrayExt.coord p.deployment_domain i=NHY_ZeroStep.byte b (40+i)) ∧
 (∀ i,i<8 → NHY_ArrayExt.coord p.global_root i=NHY_ArrayExt.coord root i ∧
   NHY_ArrayExt.coord p.lane_sequences i=NHY_ArrayExt.coord lanes i)

theorem complete_record (b : Slice U8) (len : b.val.length=192) (root : Digest) (lanes : Words) (p : C)
 (h : Coordinates b len root lanes p) : p=record b len root lanes := by
 have hm : p.master=masterBytes b len := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show masterBytes b len=NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 8 i _ hi]
  exact (h.2.2.1 i hi).1
 have hd : p.deployment_domain=domainBytes b len := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show domainBytes b len=NHY_NaturalReads.array b 40 32#usize (by change 40+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 40 i _ hi]
  exact (h.2.2.1 i hi).2
 have hr : p.global_root=root := by
  apply NHY_ArrayExt.whole
  intro i hi _
  exact (h.2.2.2 i hi).1
 have hl : p.lane_sequences=lanes := by
  apply NHY_ArrayExt.whole
  intro i hi _
  exact (h.2.2.2 i hi).2
 have hb:=h.1
 have hs:=h.2.1
 cases p
 unfold record at *
 simp_all

/-- Source-ordered composition of native prefix, digest-result, one-step loop,
and constructor clauses. Std any and digest146 replies are instantiated internally.
The Trace rejecting constructor has no suffix; input is shared immutable throughout. -/
def Cut (b : Slice U8) (len : b.val.length=192) (out : core.result.Result C F) : Prop :=
 match prefixResult b len with
 | .Err e=>out=.Err e
 | .Ok _=>∃ arg : Array U8 32#usize,
   (∀ i,i<32 → NHY_ArrayExt.coord arg i=NHY_ZeroStep.byte b (80+i)) ∧
   match NJQ_DigestPort.decoded arg with
   | .Err _=>out=.Err .NonCanonicalDigest
   | .Ok root=>∃ loopOut,
     NJQ_CheckpointTrace.Trace (sequences b len) 0 (Array.repeat 8#usize 0#u64) loopOut ∧
     match loopOut with
     | .Err e=>out=.Err e
     | .Ok lanes=>∃ p,out=.Ok p ∧ Coordinates b len root lanes p

def pipeline (b : Slice U8) (len : b.val.length=192) : core.result.Result C F :=
 match prefixResult b len with
 | .Err e=>.Err e
 | .Ok _=>match NJQ_DigestPort.decoded (digestArg b len) with
   | .Err _=>.Err .NonCanonicalDigest
   | .Ok root=>match NJQ_ArrayAll.loop (sequences b len) with
     | .Err e=>.Err e
     | .Ok lanes=>.Ok (record b len root lanes)

theorem cut_result (b : Slice U8) (len : b.val.length=192) (out : core.result.Result C F)
 (cut : Cut b len out) : out=pipeline b len := by
 unfold Cut at cut
 unfold pipeline
 cases hp : prefixResult b len with
 | Err e=>simp only [hp] at cut ⊢;exact cut
 | Ok u=>
   simp only [hp] at cut ⊢
   obtain ⟨arg,coords,post⟩:=cut
   have same : arg=digestArg b len := by
    apply NHY_ArrayExt.whole
    intro i hi _
    rw [show digestArg b len=NHY_NaturalReads.array b 80 32#usize (by change 80+32≤b.val.length;omega) from rfl]
    rw [NJI_PolicyCut.field_coordinate b 80 i _ hi]
    exact coords i hi
   subst arg
   cases hg : NJQ_DigestPort.decoded (digestArg b len) with
   | Err e=>simp only [hg] at post ⊢;exact post
   | Ok root=>
     simp only [hg] at post ⊢
     obtain ⟨loopOut,trace,post⟩:=post
     have same:=NJQ_ArrayAll.native_result (sequences b len) loopOut trace
     rw [same] at post
     cases hl : NJQ_ArrayAll.loop (sequences b len) with
     | Err e=>simp only [hl] at post ⊢;exact post
     | Ok lanes=>
       simp only [hl] at post ⊢
       obtain ⟨p,ret,coords⟩:=post
       rw [complete_record b len root lanes p coords] at ret
       exact ret

theorem model_closed (b : Slice U8) (len : b.val.length=192) : model b=ok (pipeline b len) := by
 unfold model pipeline prefixResult
 simp only [dif_pos len]
 cases hh : NJQ_Header.model b 192#usize magic with
 | Err e=>simp only [hh]
 | Ok u=>
   simp only [hh]
   by_cases hz : (trailing b len).val=List.replicate 16 0#u8 <;>
    by_cases hm : masterBytes b len=Array.repeat 32#usize 0#u8 <;>
    by_cases hd : domainBytes b len=Array.repeat 32#usize 0#u8 <;> simp_all
   all_goals cases NJQ_DigestPort.decoded (digestArg b len) <;> simp_all
   all_goals cases NJQ_ArrayAll.loop (sequences b len) <;> rfl

/-- (aq)(2): input and the reviewed parent cut only. Child/digest and loop laws
are discharged above on the same byte argument; no accepted-output premise. -/
theorem native_source (b : Slice U8) (len : b.val.length=192) (out : core.result.Result C F)
 (cut : Cut b len out) : ok out=reference b := by
 rw [source,model_closed b len]
 exact congrArg Result.ok (cut_result b len out cut)

set_option pp.proofs false in
#print native_source
#print axioms complete_record
#print axioms cut_result
#print axioms model_closed
#print axioms native_source
end NJQ_CheckpointCut
