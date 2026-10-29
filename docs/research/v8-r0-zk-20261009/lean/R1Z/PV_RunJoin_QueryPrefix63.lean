import R1Z.PV_RunJoin_QueryFactor63
import R1Z.PV_RunJoin_ActualPlanSources59
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryPrefix63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_QueryScript63

/-- Prefix law for one actual native query cell. The source success statement
contains no byte equality; the complete appended suffix is a conclusion. -/
theorem body (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (queries : Array U32 22#usize) (folded : Slice W) (salts : host_commitment.PrivateSalts)
    (i : Usize) (more : i<22#usize) (payload : alloc.vec.Vec U8)
    (success : @PV_RunJoin_ByteScript63.run
      (@script (types base) (selected base heap box ops) cc1 cc2 queries folded salts i)
      PV_RunJoin_ActualPlanSources59.empty=ok payload)
    (size : payload.length=832) (out : alloc.vec.Vec U8) (room : out.length+832≤Usize.max) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∃ next, prover.append_query_openings_loop.body cc1 cc2 queries folded salts out i=
      ok (.cont (next,Usize.wrapping_add i 1#usize)) ∧ next.val=out.val++payload.val := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨bytes,hbytes,extend⟩ := PV_RunJoin_ByteScript63.suffix _ _ _ success
  have equal : bytes=payload.val := by simpa only [PV_RunJoin_ActualPlanSources59.empty,List.nil_append] using hbytes.symm
  subst bytes
  obtain ⟨next,hnext,hval⟩ := extend out (by change out.length+payload.length≤Usize.max;rw [size];exact room)
  refine ⟨next,?_,hval⟩
  rw [PV_RunJoin_QueryFactor63.body base heap box ops cc1 cc2 queries folded salts out i more (by omega)]
  simp only [hnext,bind_tc_ok]

#print axioms body
end R1Z.PV_RunJoin_QueryPrefix63
