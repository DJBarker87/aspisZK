import R1Z.PV_RunJoin_EncodedLoop41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncodedComplete41
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_EncodedStep41 PV_RunJoin_EncodedLoop41
variable [ExternalTypes]

/-- Every actual input slice, including the folded four-value query opening,
is serialized in order. The multiplication/capacity domain is explicit. -/
theorem encode (ops : ExternalFuns) (values : Slice W)
    (room : 32*values.length≤Usize.max) :
    ∃ next, @prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops)
      values=.ok next ∧ next.val=payload values 0 values.length ∧
      next.length=32*values.length := by
  obtain ⟨next,hn,hv⟩ := PV_RunJoin_EncodedLoop41.complete ops values values.length
    0#usize (alloc.vec.Vec.with_capacity U8 (Usize.wrapping_mul 32#usize (Slice.len values)))
    (by change 0+values.length=values.length;omega)
    (by change 0+32*values.length≤Usize.max;omega)
  refine ⟨next,hn,?_,?_⟩
  · simpa only [alloc.vec.Vec.with_capacity,List.nil_append,show (0#usize).val=0 from rfl] using hv
  · change next.val.length=_
    rw [hv]
    change ([] ++ payload values 0 values.length).length=32*values.length
    rw [List.nil_append,PV_RunJoin_EncodedLoop41.length]
#print axioms encode
end R1Z.PV_RunJoin_EncodedComplete41
