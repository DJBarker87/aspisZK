import R1Z.PV_RunJoin_QueryHeadTotal64
import R1Z.PV_RunJoin_QueryTailTotal64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryScriptTotal64
attribute [local irreducible] PV_RunJoin_WeightInstalled46.selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (domain1 : PV_RunJoin_QueryFillStep64.Domain cc1)
    (domain2 : PV_RunJoin_QueryFillStep64.Domain cc2)
    (s1 s2 : host_commitment.PrivateSalts)
    (stored1 : cc1.private_salts=some s1) (stored2 : cc2.private_salts=some s2)
    (size1 : 262144≤s1.length) (size2 : 262144≤s2.length)
    (queries : Array U32 22#usize) (range : PV_RunJoin_PublishSkeleton57.QueryRange queries)
    (folded : Slice aspis_core.field.wide_exact.WideExact) (size : 262144≤folded.length)
    (salts : host_commitment.PrivateSalts) (saltSize : 65536≤salts.length)
    (i : Fin 22) (out : alloc.vec.Vec U8) (room : out.length+832≤Usize.max) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∃ next, PV_RunJoin_ByteScript63.run
      (PV_RunJoin_QueryScript63.script cc1 cc2 queries folded salts (PV_RunJoin_QueryCell63.index i)) out=ok next ∧
      next.length=out.length+832 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨⟨u,opening⟩,hh,hu⟩ := PV_RunJoin_QueryHeadTotal64.complete base heap box ops cc1 cc2 domain1 domain2 queries range i
  obtain ⟨middle,hm,hv⟩ := PV_RunJoin_ByteAppend38.append out (PV_RunJoin_QueryScript63.openingSlice opening)
    (by change out.length+(PV_RunJoin_OpeningPrefix63.payload opening).length≤Usize.max
        rw [PV_RunJoin_OpeningPrefix63.length];omega)
  have hlen : middle.length=out.length+608 := by
    change middle.val.length=out.val.length+608
    rw [hv,List.length_append]
    change out.val.length+(PV_RunJoin_OpeningPrefix63.payload opening).length=out.val.length+608
    rw [PV_RunJoin_OpeningPrefix63.length]
  obtain ⟨next,hn,hl⟩ := PV_RunJoin_QueryTailTotal64.complete base heap box ops cc1 cc2 s1 s2
    stored1 stored2 size1 size2 folded size salts saltSize u hu middle (by omega)
  refine ⟨next,?_,by omega⟩
  simp only [PV_RunJoin_QueryScript63.script,PV_RunJoin_ByteScript63.run,hh,bind_tc_ok,hm]
  rw [PV_RunJoin_QueryTail63.factor]
  exact hn

#print axioms complete
end R1Z.PV_RunJoin_QueryScriptTotal64
