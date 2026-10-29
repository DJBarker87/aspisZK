import R1Z.PV_RunJoin_QueryLeafVisit64
import R1Z.PV_RunJoin_QueryReadBounds64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryLeafChannel64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]
abbrev State := Array U8 480#usize × Usize × Usize

def Read (words : Slice host_commitment.Word) (u s j : Usize) : Prop :=
  ∃ word value, Slice.index_usize words j=ok word ∧
    host_commitment.Word.value word (Usize.wrapping_add (Usize.wrapping_mul 4#usize u) s)=ok value

theorem body (words : Slice host_commitment.Word) (lanes : Slice Usize)
    (u s : Usize) (bytes : Array U8 480#usize) (at1 j : Usize)
    (small : lanes.length≤29) (more : j.val<lanes.length) :
    Post (fun cf => ∃ next : State, cf=.cont next ∧ next.2.2.val=j.val+1 ∧ Read words u s j)
      (host_commitment.commitment_leaf_bytes_loop0_loop0.body words lanes u s bytes at1 j) := by
  unfold host_commitment.commitment_leaf_bytes_loop0_loop0.body
  have hmore : j<Slice.len lanes := more
  simp only [hmore,if_true,lift,bind_tc_ok,Aeneas.Std.uncurry]
  apply PV_RunJoin_PostEquation60.bind
  intro word hword
  apply PV_RunJoin_PostEquation60.bind
  intro value hvalue
  apply PV_RunJoin_ResultPost41.bind
  intro encoded
  apply PV_RunJoin_ResultPost41.bind
  intro lane
  apply PV_RunJoin_ResultPost41.bind
  intro width
  apply PV_RunJoin_ResultPost41.bind
  rintro ⟨slice,back⟩
  apply PV_RunJoin_ResultPost41.bind
  intro piece
  apply PV_RunJoin_ResultPost41.bind
  intro written
  exact ⟨_,rfl,PV_RunJoin_QueryLeafVisit64.increment j (by omega),word,value,hword,hvalue⟩

theorem visited (words : Slice host_commitment.Word) (lanes : Slice Usize)
    (u s : Usize) (small : lanes.length≤29)
    (bytes : Array U8 480#usize) (at1 i target : Usize)
    (out : Array U8 480#usize × Usize)
    (begin1 : i.val≤target.val) (bound : target.val<lanes.length)
    (success : host_commitment.commitment_leaf_bytes_loop0_loop0 words lanes u bytes at1 s i=ok out) :
    Read words u s target := by
  let step := fun a : State => host_commitment.commitment_leaf_bytes_loop0_loop0.body
    words lanes u s a.1 a.2.1 a.2.2
  let P := fun n : Nat => ∀ j : Usize,j.val=n → Read words u s j
  have progress : ∀ a cf, a.2.2.val<lanes.length → step a=ok cf →
      ∃ next, cf=.cont next ∧ next.2.2.val=a.2.2.val+1 ∧ P a.2.2.val := by
    rintro ⟨bytes,at1,j⟩ cf more hr
    have post := body words lanes u s bytes at1 j small more
    obtain ⟨next,hn,hi,hread⟩ := PV_RunJoin_ResultPost41.success _ _ cf post hr
    refine ⟨next,hn,hi,?_⟩
    intro other same
    have eq : other=j := UScalar.eq_of_val_eq same
    subst other
    exact hread
  have h : P target.val := PV_RunJoin_LoopVisit64.visited step (fun a => a.2.2.val) P
    lanes.length target.val progress bound (target.val-i.val) (bytes,at1,i) (by change i.val+(target.val-i.val)=target.val;omega) out success
  exact h target rfl

#print axioms Read
#print axioms body
#print axioms visited
end R1Z.PV_RunJoin_QueryLeafChannel64
