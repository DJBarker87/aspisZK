import R1Z.PV_RunJoin_QueryTail63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QuerySize63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_ResultPost41

theorem script (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (queries : Array U32 22#usize) (range : PV_RunJoin_PublishSkeleton57.QueryRange queries)
    (folded : Slice aspis_core.field.wide_exact.WideExact) (salts : host_commitment.PrivateSalts)
    (i : Fin 22) (out : alloc.vec.Vec U8) :
    Post (fun next => next.length=out.length+832)
      (PV_RunJoin_ByteScript63.run (@PV_RunJoin_QueryScript63.script (types base)
        (selected base heap box ops) cc1 cc2 queries folded salts (PV_RunJoin_QueryCell63.index i)) out) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  simp only [PV_RunJoin_QueryScript63.script,PV_RunJoin_ByteScript63.run]
  apply PV_RunJoin_PostBind63.guarded _ _ _ _
    (PV_RunJoin_QueryHead63.bound base heap box ops cc1 cc2 queries range i)
  rintro ⟨u,opening⟩ bound
  dsimp only
  apply PV_RunJoin_PostBind63.guarded _ _ _ _
    (PV_RunJoin_SliceBound62.append out (PV_RunJoin_QueryScript63.openingSlice opening))
  intro middle hmiddle
  change middle.length=out.length+(PV_RunJoin_OpeningPrefix63.payload opening).length at hmiddle
  rw [PV_RunJoin_OpeningPrefix63.length] at hmiddle
  rw [PV_RunJoin_QueryTail63.factor base heap box ops]
  have ht := PV_RunJoin_QueryTail63.length base heap box ops cc1 cc2 u bound folded salts middle
  cases he : PV_RunJoin_QueryTail63.run base heap box ops cc1 cc2 u folded salts middle with
  | fail e => trivial
  | div => trivial
  | ok final =>
    rw [he] at ht
    change final.length=middle.length+224 at ht
    change final.length=out.length+832
    omega

#print axioms script
end R1Z.PV_RunJoin_QuerySize63
