import R1Z.PV_RunJoin_PolyCanonical40
import R1Z.PV_RunJoin_SemanticCompact40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PolyPublish40
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_PolyCell38
variable [ExternalTypes]

/-- Actual polynomial encoding followed by actual compaction: all 28
coefficients, exact ordered 448-byte payload, no byte-check or success premise.
The explicit output capacity is the standard backend vector domain. -/
theorem encode (ops : ExternalFuns) (p : Nat → Q) (out : alloc.vec.Vec U8)
    (room : out.length+448≤Usize.max) :
    ∃ logical next,
      @host_sumcheck.encode_polynomial _ (ProverRwP6BodyCandidate.selected ops)
        (ProverCommitArray49.array 28#usize p)=.ok logical ∧
      host_compact.compact_values (alloc.vec.Vec.deref logical) out=.ok (.Ok (),next) ∧
      next.val=out.val ++ PV_RunJoin_SemanticCompact40.low
        (PV_RunJoin_PolyLoop38.payload p 0 28) 28 ∧
      next.length=out.length+448 := by
  obtain ⟨logical,hl,hval,hlen,hzero⟩ := PV_RunJoin_PolyCanonical40.encode ops p
  have slen : (alloc.vec.Vec.deref logical).length=32*28 := hlen
  obtain ⟨next,hn,hnext,nextlen⟩ := PV_RunJoin_CompactSize39.encode
    (alloc.vec.Vec.deref logical) out 28 slen room
    (PV_RunJoin_HighDomain40.reads _ hzero)
  refine ⟨logical,next,hl,hn,?_,nextlen⟩
  change next.val=out.val ++ PV_RunJoin_SemanticCompact40.low logical.val 28 at hnext
  rw [hval] at hnext
  exact hnext
#print axioms encode
end R1Z.PV_RunJoin_PolyPublish40
