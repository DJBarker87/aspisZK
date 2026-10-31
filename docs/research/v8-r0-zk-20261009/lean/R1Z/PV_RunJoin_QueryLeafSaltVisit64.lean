import R1Z.PV_RunJoin_QueryLeafVisit64
import R1Z.PV_RunJoin_QueryReadBounds64
import R1Z.PV_RunJoin_PostEquation60
import R1Z.PV_RunJoin_QueryWindow63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryLeafSaltVisit64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

theorem body (hash : aspis_core.digest.LegacyHashFn) (tag : U8)
    (lanes : Slice Usize) (words : Slice host_commitment.Word)
    (salts : host_commitment.PrivateSalts) (count : Usize) (small : count.val≤262144)
    (leaves : alloc.vec.Vec (Array U8 32#usize)) (u : Usize) (more : u<count) :
    Post (fun cf => ∃ next, cf=.cont next ∧ next.2.val=u.val+1 ∧
      ∃ salt, host_commitment.PrivateSalts.get salts u=ok salt)
      (host_commitment.salted_commitment_leaves_loop.body hash tag lanes words salts count leaves u) := by
  unfold host_commitment.salted_commitment_leaves_loop.body
  simp only [more,if_true,lift,bind_tc_ok,Aeneas.Std.uncurry]
  apply PV_RunJoin_ResultPost41.bind
  rintro ⟨bytes,at1⟩
  apply PV_RunJoin_PostEquation60.bind
  intro salt hsalt
  apply PV_RunJoin_ResultPost41.bind
  intro slice
  apply PV_RunJoin_ResultPost41.bind
  intro leaf
  apply PV_RunJoin_ResultPost41.bind
  rintro ⟨old,back⟩
  exact ⟨_,rfl,PV_RunJoin_QueryLeafVisit64.increment u (by change u.val<count.val at more;omega),_,hsalt⟩

theorem visited (hash : aspis_core.digest.LegacyHashFn) (tag : U8)
    (lanes : Slice Usize) (words : Slice host_commitment.Word)
    (salts : host_commitment.PrivateSalts) (count : Usize) (small : count.val≤262144)
    (leaves out : alloc.vec.Vec (Array U8 32#usize)) (i target : Usize)
    (begin1 : i.val≤target.val) (bound : target.val<count.val)
    (success : host_commitment.salted_commitment_leaves_loop hash tag lanes words salts leaves count i=ok out) :
    ∃ salt, host_commitment.PrivateSalts.get salts target=ok salt := by
  let step := fun pair : alloc.vec.Vec (Array U8 32#usize) × Usize =>
    host_commitment.salted_commitment_leaves_loop.body hash tag lanes words salts count pair.1 pair.2
  let P := fun n : Nat => ∀ u : Usize, u.val=n →
    ∃ salt, host_commitment.PrivateSalts.get salts u=ok salt
  have progress : ∀ a cf, a.2.val<count.val → step a=ok cf →
      ∃ next, cf=.cont next ∧ next.2.val=a.2.val+1 ∧ P a.2.val := by
    rintro ⟨prior,u⟩ cf more hr
    have post := body hash tag lanes words salts count small prior u more
    obtain ⟨next,hn,hi,payload,hpayload⟩ :=
      PV_RunJoin_ResultPost41.success _ _ cf post hr
    refine ⟨next,hn,hi,?_⟩
    intro other same
    have eq : other=u := UScalar.eq_of_val_eq same
    subst other
    exact ⟨payload,hpayload⟩
  have result : P target.val := PV_RunJoin_LoopVisit64.visited step (fun a => a.2.val) P
    count.val target.val progress bound (target.val-i.val) (leaves,i) (by change i.val+(target.val-i.val)=target.val;omega) out success
  exact result target rfl

theorem complete (hash : aspis_core.digest.LegacyHashFn) (tag : U8)
    (lanes : Slice Usize) (words : Slice host_commitment.Word)
    (salts : host_commitment.PrivateSalts)
    (leaves out : alloc.vec.Vec (Array U8 32#usize)) (length : leaves.length=262144)
    (success : host_commitment.salted_commitment_leaves hash tag lanes words salts leaves=ok out) :
    262144≤salts.length := by
  obtain ⟨salt,hsalt⟩ := visited hash tag lanes words salts (alloc.vec.Vec.len leaves)
    (by change leaves.length≤262144;omega) leaves out 0#usize 262143#usize
    (by decide) (by change 262143<leaves.length;omega) success
  have h := PV_RunJoin_QueryReadBounds64.vector salts 262143#usize salt hsalt
  change 262143<salts.length at h
  omega

#print axioms complete
#print axioms body
#print axioms visited
end R1Z.PV_RunJoin_QueryLeafSaltVisit64
