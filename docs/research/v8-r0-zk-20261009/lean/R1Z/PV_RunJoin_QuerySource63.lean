import R1Z.PV_RunJoin_QueryCell63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QuerySource63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem returned (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (p : prover.Publication)
    (cc1 cc2 : host_commitment.Commitment) (hc1 : p.backend.c1=some cc1) (hc2 : p.backend.c2=some cc2)
    (i : Fin 22) (payload : alloc.vec.Vec U8)
    (success : PV_RunJoin_ByteScript63.run (@PV_RunJoin_QueryScript63.script (types base)
      (selected base heap box ops) cc1 cc2 p.queries (alloc.vec.Vec.deref p.folded_word)
      p.folded_salts (PV_RunJoin_QueryCell63.index i)) PV_RunJoin_ActualPlanSources59.empty=ok payload) :
    @PV_RunJoin_ActualPlanSources59.queryBytes (types base) (selected base heap box ops)
      p (PV_RunJoin_QueryCell63.index i)=ok payload := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  simp only [PV_RunJoin_ActualPlanSources59.queryBytes,hc1,hc2,core.option.Option.unwrap,ofOption,bind_tc_ok]
  rw [PV_RunJoin_QueryFactor63.body base heap box ops cc1 cc2 p.queries
    (alloc.vec.Vec.deref p.folded_word) p.folded_salts _ (PV_RunJoin_QueryCell63.index i)
    (by change i.val<22;exact i.isLt) (by change 0+608≤Usize.max;scalar_tac)]
  simp only [success,bind_tc_ok]

#print axioms returned
end R1Z.PV_RunJoin_QuerySource63
