import R1Z.PV_RunJoin_QueryLeafWordBounds64
import R1Z.PV_RunJoin_QuerySliceRead64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoldedLeafWord64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev State := Array U8 128#usize × Usize

def Read (word : Slice W) (u s : Usize) : Prop :=
  ∃ value, Slice.index_usize word (Usize.wrapping_add (Usize.wrapping_mul 4#usize u) s)=ok value

theorem body (word : Slice W) (u : Usize) (values : Array U8 128#usize)
    (s : Usize) (more : s<4#usize) :
    Post (fun cf => ∃ next : State,cf=.cont next ∧ next.2.val=s.val+1 ∧ Read word u s)
      (prover.folded_leaves_loop0_loop0.body word u values s) := by
  unfold prover.folded_leaves_loop0_loop0.body
  simp only [more,if_true,lift,bind_tc_ok,Aeneas.Std.uncurry]
  apply PV_RunJoin_ResultPost41.bind
  rintro ⟨piece,back⟩
  apply PV_RunJoin_PostEquation60.bind
  intro value hvalue
  apply PV_RunJoin_ResultPost41.bind
  intro encoded
  apply PV_RunJoin_ResultPost41.bind
  intro copied
  exact ⟨_,rfl,PV_RunJoin_QueryLeafVisit64.increment s (by change s.val<4 at more;omega),value,hvalue⟩

theorem visited (word : Slice W) (u : Usize) (values : Array U8 128#usize)
    (i target : Usize) (out : Array U8 128#usize)
    (begin1 : i.val≤target.val) (bound : target.val<4)
    (success : prover.folded_leaves_loop0_loop0 word u values i=ok out) :
    Read word u target := by
  let step := fun a : State => prover.folded_leaves_loop0_loop0.body word u a.1 a.2
  let P := fun n : Nat => ∀ s : Usize,s.val=n → Read word u s
  have progress : ∀ a cf,a.2.val<4 → step a=ok cf →
      ∃ next,cf=.cont next ∧ next.2.val=a.2.val+1 ∧ P a.2.val := by
    rintro ⟨values,s⟩ cf more hr
    have post := body word u values s more
    obtain ⟨next,hn,hi,hread⟩ := PV_RunJoin_ResultPost41.success _ _ cf post hr
    refine ⟨next,hn,hi,?_⟩
    intro other same
    have eq : other=s := UScalar.eq_of_val_eq same
    subst other
    exact hread
  have h : P target.val := PV_RunJoin_LoopVisit64.visited step (fun a => a.2.val) P
    4 target.val progress bound (target.val-i.val) (values,i) (by change i.val+(target.val-i.val)=target.val;omega) out success
  exact h target rfl

theorem complete (word : Slice W) (values out : Array U8 128#usize)
    (success : prover.folded_leaves_loop0_loop0 word 65535#usize values 0#usize=ok out) :
    262144≤word.length := by
  obtain ⟨value,hvalue⟩ := visited word 65535#usize values 0#usize 3#usize out
    (by decide) (by decide) success
  have h := PV_RunJoin_QuerySliceRead64.bound word _ value hvalue
  have index : (Usize.wrapping_add (Usize.wrapping_mul 4#usize 65535#usize) 3#usize).val=262143 := by
    rw [Usize.wrapping_add_val_eq,PV_RunJoin_QueryLaneTotal64.first 65535#usize (by decide)]
    change (4*65535+3)%UScalar.size .Usize=262143
    rw [Nat.mod_eq_of_lt (by have h := PV_RunJoin_SamplerByteIndices54.size;omega)]
  rw [index] at h
  omega

#print axioms body
#print axioms visited
#print axioms complete
end R1Z.PV_RunJoin_FoldedLeafWord64
