import R1Z.PV_RunJoin_LoopVisit64
import R1Z.PV_RunJoin_PostEquation60
import R1Z.PV_RunJoin_QueryWindow63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryLeafVisit64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

theorem increment (u : Usize) (bound : u.val<262144) :
    (Usize.wrapping_add u 1#usize).val=u.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (u.val+1)%UScalar.size .Usize=u.val+1
  exact Nat.mod_eq_of_lt (by have h := PV_RunJoin_SamplerByteIndices54.size;omega)

theorem body (hash : aspis_core.digest.LegacyHashFn) (tag : U8)
    (lanes : Slice Usize) (words : Slice host_commitment.Word)
    (salts : host_commitment.PrivateSalts) (count : Usize) (small : count.val≤262144)
    (leaves : alloc.vec.Vec (Array U8 32#usize)) (u : Usize) (more : u<count) :
    Post (fun cf => ∃ next, cf=.cont next ∧ next.2.val=u.val+1 ∧
      ∃ payload, host_commitment.commitment_leaf_bytes words lanes u=ok payload)
      (host_commitment.salted_commitment_leaves_loop.body hash tag lanes words salts count leaves u) := by
  unfold host_commitment.salted_commitment_leaves_loop.body
  simp only [more,if_true,lift,bind_tc_ok,Aeneas.Std.uncurry]
  apply PV_RunJoin_PostEquation60.bind
  rintro ⟨bytes,at1⟩ hbytes
  apply PV_RunJoin_ResultPost41.bind
  intro salt
  apply PV_RunJoin_ResultPost41.bind
  intro slice
  apply PV_RunJoin_ResultPost41.bind
  intro leaf
  apply PV_RunJoin_ResultPost41.bind
  rintro ⟨old,back⟩
  exact ⟨_,rfl,increment u (by change u.val<count.val at more;omega),_,hbytes⟩

theorem visited (hash : aspis_core.digest.LegacyHashFn) (tag : U8)
    (lanes : Slice Usize) (words : Slice host_commitment.Word)
    (salts : host_commitment.PrivateSalts) (count : Usize) (small : count.val≤262144)
    (leaves out : alloc.vec.Vec (Array U8 32#usize)) (i target : Usize)
    (begin1 : i.val≤target.val) (bound : target.val<count.val)
    (success : host_commitment.salted_commitment_leaves_loop hash tag lanes words salts leaves count i=ok out) :
    ∃ payload, host_commitment.commitment_leaf_bytes words lanes target=ok payload := by
  let step := fun pair : alloc.vec.Vec (Array U8 32#usize) × Usize =>
    host_commitment.salted_commitment_leaves_loop.body hash tag lanes words salts count pair.1 pair.2
  let P := fun n : Nat => ∀ u : Usize, u.val=n →
    ∃ payload, host_commitment.commitment_leaf_bytes words lanes u=ok payload
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
    count.val target.val progress bound (target.val-i.val) (leaves,i) (by omega) out success
  exact result target rfl

#print axioms increment
#print axioms body
#print axioms visited
end R1Z.PV_RunJoin_QueryLeafVisit64
