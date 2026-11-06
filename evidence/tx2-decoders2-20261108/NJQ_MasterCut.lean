import NJQ_Master
import NJQ_ChildTotal
import NJI_PolicyCut
set_option autoImplicit false
noncomputable section
namespace NJQ_MasterCut
open Aeneas Aeneas.Std Result NJQ_Master
attribute [local instance] Classical.propDecidable

def prefixResult (b : Slice U8) (len : b.val.length=384) : core.result.Result Bool F :=
 match NJQ_Header.model b 384#usize magic with
 | .Err e=>.Err e
 | .Ok _=>if (reserved b len).val≠List.replicate 14 0#u8 then .Err .NonZeroReserved else
  if (tail b len).val≠List.replicate 8 0#u8 then .Err .NonZeroReserved else
  if bindingArg b len≠NJQ_MasterBinding.binding then .Err .WrongFormatBinding else
  parseBool (NHY_ZeroStep.byte b 49)

def Coordinates (b : Slice U8) (len : b.val.length=384) (id : I) (policy : P)
 (has : Bool) (lanes : Words) (m : M) : Prop :=
 m.bump=NHY_ZeroStep.byte b 7 ∧ m.identity=id ∧ m.verifier_policy=policy ∧
 m.initialized_lane_mask=NHY_ZeroStep.byte b 48 ∧ m.has_checkpoint=has ∧
 m.next_checkpoint_sequence=NJQ_Words.word b 40 (by omega) ∧
 ∀ i,i<8 → NHY_ArrayExt.coord m.last_checkpoint_lane_sequences i=NHY_ArrayExt.coord lanes i

theorem complete_record (b : Slice U8) (len : b.val.length=384) (id : I) (policy : P)
 (has : Bool) (lanes : Words) (m : M) (h : Coordinates b len id policy has lanes m) :
 m=record b len id policy has lanes := by
 have seq : m.last_checkpoint_lane_sequences=lanes := by
  apply NHY_ArrayExt.whole
  intro i hi _
  exact h.2.2.2.2.2.2 i hi
 obtain ⟨hb,hi,hp,hm,hh,hn,_⟩:=h
 cases m
 unfold record
 simp_all

/-- Ordered prefix, closed child calls at their exact windows, one arbitrary
native step iterated by induction, full constructor and validator Result.
No accepted-child or endpoint premise is admitted. The argument/frame cuts
are the retained K025/K027 source stages; this support is not row credit. -/
def Cut (b : Slice U8) (len : b.val.length=384) (out : core.result.Result M F) : Prop :=
 match prefixResult b len with
 | .Err e=>out=.Err e
 | .Ok has=>
  match NJQ_ChildTotal.identity (identityArg b) with
  | .Err _=>out=.Err .Identity
  | .Ok id=>
   match NJQ_ChildTotal.policy (policyArg b) with
   | .Err _=>out=.Err .Policy
   | .Ok policy=>∃ lanes,
    NJQ_MasterTrace.Writes (sequences b len) 0 (Array.repeat 8#usize 0#u64) lanes ∧
    ∃ m,Coordinates b len id policy has lanes m ∧
     match NJQ_ChildTotal.master m with
     | .Err e=>out=.Err e
     | .Ok _=>out=.Ok m

def pipeline (b : Slice U8) (len : b.val.length=384) : core.result.Result M F :=
 match prefixResult b len with
 | .Err e=>.Err e
 | .Ok has=>
  match NJQ_ChildTotal.identity (identityArg b) with
  | .Err _=>.Err .Identity
  | .Ok id=>
   match NJQ_ChildTotal.policy (policyArg b) with
   | .Err _=>.Err .Policy
   | .Ok policy=>
    let m:=record b len id policy has (sequences b len)
    match NJQ_ChildTotal.master m with | .Err e=>.Err e | .Ok _=>.Ok m

theorem cut_result (b : Slice U8) (len : b.val.length=384) (out : core.result.Result M F)
 (cut : Cut b len out) : out=pipeline b len := by
 unfold Cut at cut
 unfold pipeline
 cases hp : prefixResult b len with
 | Err e=>simp only [hp] at cut ⊢;exact cut
 | Ok has=>
  simp only [hp] at cut ⊢
  cases hi : NJQ_ChildTotal.identity (identityArg b) with
  | Err e=>simp only [hi] at cut ⊢;exact cut
  | Ok id=>
   simp only [hi] at cut ⊢
   cases hpol : NJQ_ChildTotal.policy (policyArg b) with
   | Err e=>simp only [hpol] at cut ⊢;exact cut
   | Ok policy=>
    simp only [hpol] at cut ⊢
    obtain ⟨lanes,trace,m,coords,post⟩:=cut
    have same:=NJQ_MasterTrace.initial (sequences b len) lanes trace
    subst lanes
    rw [complete_record b len id policy has (sequences b len) m coords] at post
    cases hv : NJQ_ChildTotal.master (record b len id policy has (sequences b len)) <;>
     simp only [hv] at post ⊢ <;> exact post

theorem model_closed (b : Slice U8) (len : b.val.length=384) : model b=ok (pipeline b len) := by
 unfold model pipeline prefixResult
 simp only [dif_pos len,NJQ_ChildTotal.identity_value,NJQ_ChildTotal.policy_value,
  NJQ_ChildTotal.master_value,bind_tc_ok]
 cases hh : NJQ_Header.model b 384#usize magic with
 | Err e=>simp only [hh]
 | Ok u=>
  simp only [hh]
  by_cases hr : (reserved b len).val=List.replicate 14 0#u8 <;>
   by_cases ht : (tail b len).val=List.replicate 8 0#u8 <;>
   by_cases hb : bindingArg b len=NJQ_MasterBinding.binding <;> simp_all
  all_goals cases parseBool (NHY_ZeroStep.byte b 49) <;> simp_all
  all_goals cases NJQ_ChildTotal.identity (identityArg b) <;> simp_all
  all_goals cases NJQ_ChildTotal.policy (policyArg b) <;> simp_all
  all_goals cases NJQ_ChildTotal.master _ <;> rfl

theorem native_source (b : Slice U8) (len : b.val.length=384) (out : core.result.Result M F)
 (cut : Cut b len out) : ok out=reference b := by
 rw [source,model_closed b len]
 exact congrArg Result.ok (cut_result b len out cut)

set_option pp.proofs false in
#print native_source
#print axioms complete_record
#print axioms cut_result
#print axioms model_closed
#print axioms native_source
end NJQ_MasterCut
