import R1Z.PV_RunJoin_QueryPrefix63
import R1Z.PV_RunJoin_QueryParts63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryCell63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_QueryScript63

def index (i : Fin 22) : Usize := UScalar.ofNatCore i.val (by
  have hs := ProverCommitPairCounter47.usize_large
  have := i.isLt
  omega)

theorem source (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (p : prover.Publication)
    (cc1 cc2 : host_commitment.Commitment) (hc1 : p.backend.c1=some cc1) (hc2 : p.backend.c2=some cc2)
    (i : Fin 22) (payload : alloc.vec.Vec U8)
    (success : @PV_RunJoin_ActualPlanSources59.queryBytes (types base)
      (selected base heap box ops) p (index i)=ok payload) :
    @PV_RunJoin_ByteScript63.run
      (@script (types base) (selected base heap box ops) cc1 cc2 p.queries
        (alloc.vec.Vec.deref p.folded_word) p.folded_salts (index i))
      PV_RunJoin_ActualPlanSources59.empty=ok payload := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold PV_RunJoin_ActualPlanSources59.queryBytes at success
  simp only [hc1,hc2,core.option.Option.unwrap,bind_tc_ok] at success
  rw [PV_RunJoin_QueryFactor63.body base heap box ops cc1 cc2 p.queries
    (alloc.vec.Vec.deref p.folded_word) p.folded_salts _ (index i)
      (by change i.val<22;exact i.isLt) (by change 0+608≤Usize.max;scalar_tac)] at success
  simp only [bind_assoc_eq,bind_tc_ok] at success
  obtain ⟨next,hn,hret⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
  have same : next=payload := Result.ok.inj hret
  subst payload
  exact hn

theorem actual (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (phase : PV_RunJoin_NativeControl55.Phase)
    (p : prover.Publication) (cc1 cc2 : host_commitment.Commitment)
    (hc1 : p.backend.c1=some cc1) (hc2 : p.backend.c2=some cc2)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base)
      (selected base heap box ops) (@PV_RunJoin_ActualRun.runs (types base) (selected base heap box ops) phase) p)
    (i : Fin 22) (payload : alloc.vec.Vec U8)
    (success : @PV_RunJoin_ActualPlanSources59.queryBytes (types base)
      (selected base heap box ops) p (index i)=ok payload)
    (size : payload.length=832) (out : alloc.vec.Vec U8) (room : out.length+832≤Usize.max) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∃ next, prover.append_query_openings_loop.body cc1 cc2 p.queries
      (alloc.vec.Vec.deref p.folded_word) p.folded_salts out (index i)=
      ok (.cont (next,Usize.wrapping_add (index i) 1#usize)) ∧
      PV_RunJoin_PublishSkeleton54.bytes next.val=PV_RunJoin_PublishSkeleton54.bytes out.val ++
        ProverCommitPublish43.queryBytes (PV_RunJoin_ActualPlanSources59.queryPart phase i) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  have model := source base heap box ops p cc1 cc2 hc1 hc2 i payload success
  obtain ⟨next,hn,hv⟩ := PV_RunJoin_QueryPrefix63.body base heap box ops cc1 cc2 p.queries
    (alloc.vec.Vec.deref p.folded_word) p.folded_salts (index i)
      (by change i.val<22;exact i.isLt) payload model size out room
  have part := @PV_RunJoin_QueryParts63.actual (types base) (selected base heap box ops)
    phase p context i payload success size
  refine ⟨next,hn,?_⟩
  rw [hv,PV_RJN_Bytes.append,part]

#print axioms index
#print axioms source
#print axioms actual
end R1Z.PV_RunJoin_QueryCell63
