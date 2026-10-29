import R1Z.PV_RunJoin_QueryLeafChannel64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryLeafRows64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]
open PV_RunJoin_QueryLeafChannel64 (State)

def Read (words : Slice host_commitment.Word) (lanes : Slice Usize) (u s : Usize) : Prop :=
  ∃ (bytes : Array U8 480#usize) (at1 : Usize) (out : Array U8 480#usize × Usize),
    host_commitment.commitment_leaf_bytes_loop0_loop0 words lanes u bytes at1 s 0#usize=ok out

theorem body (words : Slice host_commitment.Word) (lanes : Slice Usize)
    (u : Usize) (bytes : Array U8 480#usize) (at1 s : Usize) (more : s<4#usize) :
    Post (fun cf => ∃ next : State, cf=.cont next ∧ next.2.2.val=s.val+1 ∧ Read words lanes u s)
      (host_commitment.commitment_leaf_bytes_loop0.body words lanes u bytes at1 s) := by
  unfold host_commitment.commitment_leaf_bytes_loop0.body
  simp only [more,if_true,lift,bind_tc_ok,Aeneas.Std.uncurry]
  apply PV_RunJoin_PostEquation60.bind
  rintro ⟨nextBytes,nextAt⟩ hr
  exact ⟨_,rfl,PV_RunJoin_QueryLeafVisit64.increment s
    (by change s.val<4 at more;omega),bytes,at1,_,hr⟩

theorem visited (words : Slice host_commitment.Word) (lanes : Slice Usize)
    (u : Usize) (bytes : Array U8 480#usize) (at1 i target : Usize)
    (out : Array U8 480#usize × Usize) (begin1 : i.val≤target.val) (bound : target.val<4)
    (success : host_commitment.commitment_leaf_bytes_loop0 words lanes u bytes at1 i=ok out) :
    Read words lanes u target := by
  let step := fun a : State => host_commitment.commitment_leaf_bytes_loop0.body
    words lanes u a.1 a.2.1 a.2.2
  let P := fun n : Nat => ∀ s : Usize,s.val=n → Read words lanes u s
  have progress : ∀ a cf, a.2.2.val<4 → step a=ok cf →
      ∃ next, cf=.cont next ∧ next.2.2.val=a.2.2.val+1 ∧ P a.2.2.val := by
    rintro ⟨bytes,at1,s⟩ cf more hr
    have post := body words lanes u bytes at1 s more
    obtain ⟨next,hn,hi,hread⟩ := PV_RunJoin_ResultPost41.success _ _ cf post hr
    refine ⟨next,hn,hi,?_⟩
    intro other same
    have eq : other=s := UScalar.eq_of_val_eq same
    subst other
    exact hread
  have h : P target.val := PV_RunJoin_LoopVisit64.visited step (fun a => a.2.2.val) P
    4 target.val progress bound (target.val-i.val) (bytes,at1,i) (by change i.val+(target.val-i.val)=target.val;omega) out success
  exact h target rfl

theorem last_row (words : Slice host_commitment.Word) (lanes : Slice Usize)
    (u : Usize) (out : Array U8 480#usize × Usize)
    (success : host_commitment.commitment_leaf_bytes words lanes u=ok out) :
    Read words lanes u 3#usize :=
  visited words lanes u (Array.repeat 480#usize 0#u8) 0#usize 0#usize 3#usize out
    (by decide) (by decide) success

#print axioms Read
#print axioms body
#print axioms visited
#print axioms last_row
end R1Z.PV_RunJoin_QueryLeafRows64
