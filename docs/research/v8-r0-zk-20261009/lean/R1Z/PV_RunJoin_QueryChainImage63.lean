import R1Z.PV_RunJoin_QueryLoop63
import R1Z.PV_RunJoin_QuerySource63
import R1Z.PV_RunJoin_QueryStream63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryChainImage63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54 (bytes)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (phase : @PV_RunJoin_NativeControl55.Phase (types base))
    (p : prover.Publication) (cc1 cc2 : host_commitment.Commitment)
    (hc1 : p.backend.c1=some cc1) (hc2 : p.backend.c2=some cc2)
    (context : @PV_RunJoin_PublishContext57.QueryContext (types base) (selected base heap box ops)
      (@PV_RunJoin_ActualRun.runs (types base) (selected base heap box ops) phase) p)
    (range : PV_RunJoin_PublishSkeleton57.QueryRange p.queries)
    (n : Nat) (i : Usize) (initial final : alloc.vec.Vec U8)
    (rank : i.val+n=22) (room : initial.length+832*n≤Usize.max)
    (success : PV_RunJoin_ByteScript63.run (@PV_RunJoin_QueryLoop63.series (types base)
      (selected base heap box ops) cc1 cc2 p.queries (alloc.vec.Vec.deref p.folded_word) p.folded_salts n i)
      initial=ok final) :
    bytes final.val=bytes initial.val++@PV_RunJoin_QueryStream63.stream
      (@PV_RunJoin_QueryStream63.part (types base) (selected base heap box ops) phase) i.val n := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  induction n generalizing i initial final with
  | zero =>
    have same : initial=final := Result.ok.inj success
    subst final
    simp only [PV_RunJoin_QueryStream63.stream,List.append_nil]
  | succ n ih =>
    have more : i.val<22 := by omega
    let fi : Fin 22 := ⟨i.val,more⟩
    have index : PV_RunJoin_QueryCell63.index fi=i := by apply UScalar.eq_of_val_eq;rfl
    have nextIndex := ProverCommitPairCounter47.next_val i (by omega)
    simp only [PV_RunJoin_QueryLoop63.series,PV_RunJoin_ByteSequence63.run] at success
    obtain ⟨middle,hfirst,htail⟩ := PV_RunJoin_ResultPost41.bind_success _ _ _ success
    have hsize := PV_RunJoin_QuerySize63.script base heap box ops cc1 cc2 p.queries range
      (alloc.vec.Vec.deref p.folded_word) p.folded_salts fi initial
    rw [index] at hsize
    have middleLength := PV_RunJoin_ResultPost41.success _ _ _ hsize hfirst
    change middle.length=initial.length+832 at middleLength
    obtain ⟨payloadBytes,hprefix,extend⟩ := PV_RunJoin_ByteScript63.suffix _ _ _ hfirst
    have emptyRoom : PV_RunJoin_ActualPlanSources59.empty.length+payloadBytes.length≤Usize.max := by
      have cap := middle.property
      rw [hprefix,List.length_append] at cap
      change 0+payloadBytes.length≤Usize.max
      omega
    obtain ⟨payload,hpayload,hpayloadBytes⟩ := extend PV_RunJoin_ActualPlanSources59.empty emptyRoom
    have hpval : payload.val=payloadBytes := by
      simpa only [PV_RunJoin_ActualPlanSources59.empty,List.nil_append] using hpayloadBytes
    have hpcode : PV_RunJoin_ByteScript63.run
        (PV_RunJoin_QueryScript63.script cc1 cc2 p.queries (alloc.vec.Vec.deref p.folded_word)
          p.folded_salts (PV_RunJoin_QueryCell63.index fi)) PV_RunJoin_ActualPlanSources59.empty=ok payload := by
      rw [index];exact hpayload
    have returned := PV_RunJoin_QuerySource63.returned base heap box ops p cc1 cc2 hc1 hc2 fi payload hpcode
    have plen := PV_RunJoin_QuerySize63.script base heap box ops cc1 cc2 p.queries range
      (alloc.vec.Vec.deref p.folded_word) p.folded_salts fi PV_RunJoin_ActualPlanSources59.empty
    rw [hpcode] at plen
    change payload.length=0+832 at plen
    have image := @PV_RunJoin_QueryParts63.actual (types base) (selected base heap box ops)
      phase p context fi payload returned (by omega)
    have firstBytes : bytes middle.val=bytes initial.val++
        ProverCommitPublish43.queryBytes (PV_RunJoin_ActualPlanSources59.queryPart phase fi) := by
      rw [hprefix,PV_RJN_Bytes.append,←hpval,←image]
    have tailRoom : middle.length+832*n≤Usize.max := by
      simp only [Nat.mul_add,Nat.mul_one] at room
      omega
    have tailBytes := ih (Usize.wrapping_add i 1#usize) middle final
      (by rw [nextIndex];omega) tailRoom htail
    rw [tailBytes,firstBytes,nextIndex]
    simp only [PV_RunJoin_QueryStream63.stream,PV_RunJoin_QueryStream63.part,dif_pos more,List.append_assoc]

#print axioms complete
end R1Z.PV_RunJoin_QueryChainImage63
