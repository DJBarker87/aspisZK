import R1Z.PV_RunJoin_ClaimLoop41
import R1Z.PV_RunJoin_PolyCanonical40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimBytes41
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PolyCell38 PV_RunJoin_PolyLoop38
variable [ExternalTypes]

theorem row (ops : ExternalFuns) (p : Nat → Q) (out : alloc.vec.Vec U8)
    (room : out.length+928≤Usize.max) :
    ∃ next, @host_semantic.append_claim_bytes _ (ProverRwP6BodyCandidate.selected ops)
      out (ProverCommitArray49.array 29#usize p)=.ok next ∧
      next.val=out.val ++ payload p 0 29 ∧ next.length=out.length+928 := by
  obtain ⟨next,hn,hv⟩ := PV_RunJoin_ClaimLoop41.complete ops p 29 0#usize out rfl room
  refine ⟨next,hn,?_,?_⟩
  · simpa only [show (0#usize).val=0 from rfl] using hv
  · change next.val.length=out.val.length+928
    rw [hv,List.length_append,payload_length]

def bytes (p : Nat → Nat → Q) (extras : Nat → Q) : List U8 :=
  payload (p 0) 0 29 ++ payload (p 1) 0 29 ++ payload (p 2) 0 29 ++ payload extras 0 29

/-- All source point claims followed by extras, with normalized wide encodings.
There is no successful encoder/validator call among the premises. -/
theorem encode (ops : ExternalFuns) (p : Nat → Nat → Q) (extras : Nat → Q) :
    ∃ next, @host_semantic.claim_bytes _ (ProverRwP6BodyCandidate.selected ops)
      (ProverCommitArray49.array 3#usize (fun i => ProverCommitArray49.array 29#usize (p i)))
      (ProverCommitArray49.array 29#usize extras)=.ok next ∧
      next.val=bytes p extras ∧ next.length=3712 := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  have cap : 3712≤Usize.max := by scalar_tac
  let out := alloc.vec.Vec.with_capacity U8 3712#usize
  have empty : out.length=0 := rfl
  obtain ⟨b0,h0,v0,l0⟩ := row ops (p 0) out (by omega)
  obtain ⟨b1,h1,v1,l1⟩ := row ops (p 1) b0 (by omega)
  obtain ⟨b2,h2,v2,l2⟩ := row ops (p 2) b1 (by omega)
  obtain ⟨next,h3,v3,l3⟩ := row ops extras b2 (by omega)
  refine ⟨next,?_,?_,?_⟩
  · unfold host_semantic.claim_bytes
    rw [ProverCommitArray49.index 3#usize _ 0#usize (by decide)]
    simp only [bind_tc_ok,show (0#usize).val=0 from rfl]
    rw [h0]
    simp only [bind_tc_ok]
    rw [ProverCommitArray49.index 3#usize _ 1#usize (by decide)]
    simp only [bind_tc_ok,show (1#usize).val=1 from rfl]
    rw [h1]
    simp only [bind_tc_ok]
    rw [ProverCommitArray49.index 3#usize _ 2#usize (by decide)]
    simp only [bind_tc_ok,show (2#usize).val=2 from rfl]
    rw [h2]
    simp only [bind_tc_ok]
    exact h3
  · rw [v3,v2,v1,v0]
    change ((([] ++ payload (p 0) 0 29) ++ payload (p 1) 0 29) ++ payload (p 2) 0 29) ++ payload extras 0 29=bytes p extras
    simp only [bytes,List.nil_append]
  · rw [l3,l2,l1,l0]
    rfl
#print axioms row
#print axioms encode
end R1Z.PV_RunJoin_ClaimBytes41
