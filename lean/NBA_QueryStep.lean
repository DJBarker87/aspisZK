import Query31ExplicitListLoop
set_option autoImplicit false
namespace AspisR1.NBA_QueryStep
open Aeneas Aeneas.Std Result ControlFlow
open Query31ExplicitScanBody Query31ExplicitListLoop Query31ExplicitScanConcreteSteps
abbrev State := Query31ExplicitScanBody.CurrentScan

/-- Exactly the three continuing-state facts checked by native K013. -/
def Frame (s next : State) (x : U32) (member : Bool) : Prop :=
  next.draws.val=s.draws.val+1 ∧
  next.accepted_len.val=s.accepted_len.val+(if member then 0 else 1) ∧
  next.accepted.val=(if member then s.accepted.val else s.accepted.val.set s.accepted_len.val x)

theorem unique {s left right : State} {x : U32} {member : Bool}
    (hl : Frame s left x member) (hr : Frame s right x member) : left=right := by
  have ha : left.accepted=right.accepted := Subtype.ext (hl.2.2.trans hr.2.2.symm)
  have hn : left.accepted_len=right.accepted_len := UScalar.eq_of_val_eq (hl.2.1.trans hr.2.1.symm)
  have hd : left.draws=right.draws := UScalar.eq_of_val_eq (hl.1.trans hr.1.symm)
  cases left
  cases right
  cases ha
  cases hn
  cases hd
  rfl

theorem update (s : State) (x : U32) (hlen : s.accepted_len.val<22) :
    s.accepted.update s.accepted_len x=ok (s.accepted.set s.accepted_len x) := by
  obtain ⟨a,call,value⟩ := WP.spec_imp_exists
    (Array.update_spec s.accepted s.accepted_len x (by simpa only [Array.length,s.accepted.property,show (22#usize).val=22 by rfl] using hlen))
  exact call.trans (congrArg ok value)

theorem fresh (xs : List U32) (s next : State) (x : U32)
    (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64)
    (hfresh : x.val ∉ acceptedPrefix s) (frame : Frame s next x false) :
    body (stdOps listNext) (x::xs) s=ok (.cont (xs,next)) := by
  obtain ⟨d,n,a,hd,vd,hn,vn,ha,hbody,_⟩ :=
    fresh_from_bounds listNext (x::xs) xs s x rfl hlen hdraw hfresh
  have sameArray : a=s.accepted.set s.accepted_len x := Result.ok.inj (ha.symm.trans (update s x hlen))
  have f : Frame s {accepted:=a,accepted_len:=n,draws:=d} x false := by
    refine ⟨vd,?_,?_⟩
    · simpa only [Bool.false_eq_true,↓reduceIte] using vn
    · simp only [Bool.false_eq_true,↓reduceIte,sameArray]
      rfl
  have same := unique f frame
  simpa only [same] using hbody

theorem val_mem (xs : List U32) (x : U32) : x.val ∈ xs.map (fun y => y.val) ↔ x ∈ xs := by
  constructor
  · intro h
    obtain ⟨y,hy,hv⟩ := List.mem_map.mp h
    have he : y=x := UScalar.eq_of_val_eq hv
    exact he ▸ hy
  · intro h
    exact List.mem_map.mpr ⟨x,h,rfl⟩

theorem duplicate (xs : List U32) (s next : State) (x : U32)
    (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64)
    (hmember : x.val ∈ acceptedPrefix s) (frame : Frame s next x true) :
    body (stdOps listNext) (x::xs) s=ok (.cont (xs,next)) := by
  have small : s.draws.val+(1#usize).val≤Usize.max := by scalar_tac
  obtain ⟨d,hd,vd⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=s.draws) (y:=1#usize) (by simpa only [UScalar.max_USize_eq] using small))
  have bound : s.accepted_len.val≤s.accepted.length := by
    simp only [Array.length,s.accepted.property,show (22#usize).val=22 by rfl]
    omega
  obtain ⟨sl,read,spec⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
      ({«end»:=s.accepted_len} : core.ops.range.RangeTo Usize) (Array.to_slice s.accepted) bound)
  have slval : sl.val=s.accepted.val.take s.accepted_len.val := by
    rcases spec with ⟨value,_⟩
    simpa only [Array.to_slice,List.slice,Nat.sub_zero,List.drop_zero] using value
  have member : x∈sl.val := by
    rw [slval]
    exact (val_mem _ x).mp hmember
  have contains : core.slice.Slice.contains core.cmp.PartialEqU32 sl x=ok true := by
    rw [slice_contains_eq_mem]
    simp only [member,decide_true]
  have notFull : s.accepted_len≠22#usize := by scalar_tac
  have notCap : s.draws≠64#usize := by scalar_tac
  have b := duplicate_step (stdOps listNext) (x::xs) xs s x d sl rfl notFull notCap hd read contains
  have f : Frame s {s with draws:=d} x true := by
    refine ⟨?_,?_,rfl⟩
    · simpa using vd
    · simp only [↓reduceIte,Nat.add_zero]
  have same := unique f frame
  simpa only [same] using b

theorem valid {s next : State} {x : U32} {member : Bool}
    (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64) (frame : Frame s next x member) :
    validState next := by
  apply validState_of_bounds
  · have n := frame.2.1
    cases member <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero] at n <;> omega
  · have n := frame.1
    omega

#print axioms unique
#print axioms update
#print axioms fresh
#print axioms val_mem
#print axioms duplicate
#print axioms valid
end AspisR1.NBA_QueryStep
