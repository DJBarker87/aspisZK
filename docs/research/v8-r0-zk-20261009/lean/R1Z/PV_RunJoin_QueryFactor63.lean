import R1Z.PV_RunJoin_OpeningEmit63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryFactor63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_QueryScript63

theorem body (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (queries : Array U32 22#usize) (folded : Slice W) (salts : host_commitment.PrivateSalts)
    (out : alloc.vec.Vec U8) (i : Usize) (more : i<22#usize)
    (room : out.length+608≤Usize.max) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    prover.append_query_openings_loop.body cc1 cc2 queries folded salts out i=
      (do let next ← PV_RunJoin_ByteScript63.run (script cc1 cc2 queries folded salts i) out
          ok (.cont (next,Usize.wrapping_add i 1#usize))) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  simp only [prover.append_query_openings_loop.body,more,if_true,script,
    PV_RunJoin_ByteScript63.run,head,lift,bind_tc_ok,bind_assoc_eq,Aeneas.Std.uncurry]
  apply congrArg (Aeneas.Std.bind _)
  funext q
  apply congrArg (Aeneas.Std.bind _)
  funext status
  apply congrArg (Aeneas.Std.bind _)
  funext u
  apply congrArg (Aeneas.Std.bind _)
  funext zero
  apply congrArg (Aeneas.Std.bind _)
  funext first
  apply congrArg (Aeneas.Std.bind _)
  funext opening
  rw [PV_RunJoin_OpeningEmit63.complete base heap box ops opening out room]
  simp only [tail,PV_RunJoin_ByteScript63.run,lift,bind_tc_ok,bind_assoc_eq]
  rfl

#print axioms body
end R1Z.PV_RunJoin_QueryFactor63
