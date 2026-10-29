import R1Z.PV_RunJoin_QueryScriptTotal64
import R1Z.PV_RunJoin_QueryLoop63
import R1Z.PV_RunJoin_QueryRoom64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryLoopTotal64
attribute [local irreducible] PV_RunJoin_WeightInstalled46.selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

structure Domain (cc1 cc2 : host_commitment.Commitment)
    (folded : Slice aspis_core.field.wide_exact.WideExact) (salts : host_commitment.PrivateSalts) : Prop where
  first : PV_RunJoin_QueryFillStep64.Domain cc1
  second : PV_RunJoin_QueryFillStep64.Domain cc2
  firstSalts : ∃ s,cc1.private_salts=some s ∧ 262144≤s.length
  secondSalts : ∃ s,cc2.private_salts=some s ∧ 262144≤s.length
  foldedSize : 262144≤folded.length
  saltSize : 65536≤salts.length

theorem finite (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (queries : Array U32 22#usize) (range : PV_RunJoin_PublishSkeleton57.QueryRange queries)
    (folded : Slice aspis_core.field.wide_exact.WideExact) (salts : host_commitment.PrivateSalts)
    (domain : Domain cc1 cc2 folded salts)
    (n : Nat) (i : Usize) (out : alloc.vec.Vec U8)
    (rank : i.val+n=22) (room : out.length+832*n≤Usize.max) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := selected base heap box ops
    ∃ next, PV_RunJoin_ByteScript63.run (PV_RunJoin_QueryLoop63.series cc1 cc2 queries folded salts n i) out=ok next ∧
      next.length=out.length+832*n := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨s1,stored1,size1⟩ := domain.firstSalts
  obtain ⟨s2,stored2,size2⟩ := domain.secondSalts
  induction n generalizing i out with
  | zero => exact ⟨out,rfl,by omega⟩
  | succ n ih =>
    have more : i.val<22 := by omega
    let k : Fin 22 := ⟨i.val,more⟩
    have hk : PV_RunJoin_QueryCell63.index k=i := by apply UScalar.eq_of_val_eq;rfl
    have roomParts := PV_RunJoin_QueryRoom63.split out.length Usize.max n 832 832 (Nat.le_refl _) room
    obtain ⟨middle,hm,hlen⟩ := PV_RunJoin_QueryScriptTotal64.complete base heap box ops
      cc1 cc2 domain.first domain.second s1 s2 stored1 stored2 size1 size2 queries range folded
      domain.foldedSize salts domain.saltSize k out roomParts.1
    rw [hk] at hm
    have inc := ProverCommitPairCounter47.next_val i (by change i.val<1024;omega)
    obtain ⟨next,hn,hl⟩ := ih (Usize.wrapping_add i 1#usize) middle (by rw [inc];omega) (roomParts.2 middle.length hlen)
    refine ⟨next,?_,PV_RunJoin_QueryRoom64.length_step out.length middle.length next.length n 832 hlen hl⟩
    simp only [PV_RunJoin_QueryLoop63.series,PV_RunJoin_ByteSequence63.run,hm,bind_tc_ok,hn]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (cc1 cc2 : host_commitment.Commitment)
    (queries : Array U32 22#usize) (range : PV_RunJoin_PublishSkeleton57.QueryRange queries)
    (folded : Slice aspis_core.field.wide_exact.WideExact) (salts : host_commitment.PrivateSalts)
    (domain : Domain cc1 cc2 folded salts) (out : alloc.vec.Vec U8)
    (room : out.length+18304≤Usize.max) :
    ∃ next, @prover.append_query_openings (types base) (selected base heap box ops)
      out cc1 cc2 queries folded salts=ok next ∧ next.length=out.length+18304 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨next,hn,hl⟩ := finite base heap box ops cc1 cc2 queries range folded salts domain
    22 0#usize out rfl room
  refine ⟨next,?_,hl⟩
  change prover.append_query_openings_loop out cc1 cc2 queries folded salts 0#usize=ok next
  rw [PV_RunJoin_QueryLoop63.loop base heap box ops cc1 cc2 queries range folded salts 22 0#usize out rfl room]
  exact hn

#print axioms Domain
#print axioms finite
#print axioms complete
end R1Z.PV_RunJoin_QueryLoopTotal64
