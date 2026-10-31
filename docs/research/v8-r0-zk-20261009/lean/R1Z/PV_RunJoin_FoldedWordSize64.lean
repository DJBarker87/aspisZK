import R1Z.PV_RunJoin_FoldedLeafWord64
import R1Z.PV_RunJoin_FoldedLeafLimits64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FoldedWordSize64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Leaves := alloc.vec.Vec (Array U8 32#usize)

def Read (word : Slice W) (u : Usize) : Prop := u.val<65536 →
  ∃ values, prover.folded_leaves_loop0_loop0 word u (Array.repeat 128#usize 0#u8) 0#usize=ok values

theorem body (hash : aspis_core.digest.LegacyHashFn) (word : Slice W)
    (salts : host_commitment.PrivateSalts) (leaves : Leaves) (u : Usize) (more : u.val<262144) :
    Post (fun cf => ∃ next : Leaves × Usize,cf=.cont next ∧ next.2.val=u.val+1 ∧ Read word u)
      (prover.folded_leaves_loop0.body hash word salts leaves u) := by
  unfold prover.folded_leaves_loop0.body
  rw [PV_RunJoin_FoldedLeafLimits64.fibres]
  simp only [lift,bind_tc_ok]
  have hmore : u<262144#usize := more
  simp only [hmore,if_true,PV_RunJoin_FoldedLeafLimits64.populated]
  by_cases populated : u<65536#usize
  · simp only [populated,if_true]
    apply PV_RunJoin_PostEquation60.bind
    intro values hvalues
    apply PV_RunJoin_ResultPost41.bind
    intro salt
    apply PV_RunJoin_ResultPost41.bind
    intro leaf
    apply PV_RunJoin_ResultPost41.bind
    intro next
    exact ⟨_,rfl,PV_RunJoin_QueryLeafVisit64.increment u more,fun _ => ⟨values,hvalues⟩⟩
  · simp only [populated,if_false]
    apply PV_RunJoin_ResultPost41.bind
    intro salt
    apply PV_RunJoin_ResultPost41.bind
    intro leaf
    apply PV_RunJoin_ResultPost41.bind
    intro next
    refine ⟨_,rfl,PV_RunJoin_QueryLeafVisit64.increment u more,?_⟩
    intro bound
    exact (populated bound).elim

theorem complete (hash : aspis_core.digest.LegacyHashFn) (word : Slice W)
    (salts : host_commitment.PrivateSalts) (out : Leaves)
    (success : prover.folded_leaves hash word salts=ok out) : 262144≤word.length := by
  let step := fun pair : Leaves × Usize => prover.folded_leaves_loop0.body hash word salts pair.1 pair.2
  let P := fun n : Nat => ∀ u : Usize,u.val=n → Read word u
  have progress : ∀ a cf,a.2.val<262144 → step a=ok cf →
      ∃ next,cf=.cont next ∧ next.2.val=a.2.val+1 ∧ P a.2.val := by
    rintro ⟨leaves,u⟩ cf more hr
    obtain ⟨next,hn,hi,hread⟩ := PV_RunJoin_ResultPost41.success _ _ cf (body hash word salts leaves u more) hr
    refine ⟨next,hn,hi,?_⟩
    intro other same
    have eq : other=u := UScalar.eq_of_val_eq same
    subst other
    exact hread
  unfold prover.folded_leaves at success
  simp only [PV_RunJoin_FoldedLeafLimits64.fibres,lift,bind_tc_ok] at success
  have h : P 65535 := PV_RunJoin_LoopVisit64.visited step (fun a => a.2.val) P 262144 65535
    progress (by decide) 65535 (alloc.vec.Vec.with_capacity (Array U8 32#usize) 262144#usize,0#usize)
    rfl out success
  obtain ⟨values,hvalues⟩ := h 65535#usize rfl (by decide)
  exact PV_RunJoin_FoldedLeafWord64.complete word _ values hvalues

#print axioms body
#print axioms complete
end R1Z.PV_RunJoin_FoldedWordSize64
