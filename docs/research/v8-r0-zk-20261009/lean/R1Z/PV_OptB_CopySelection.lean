import R0P.CopyRegistry
set_option autoImplicit false
namespace R1Z.PV_OptB_CopySelection
open R0P

/-- Select one source-list cell using a proved sparse key law, without
normalizing the whole arithmetic recurrence at a concrete trace. -/
theorem select_unique {A Key K : Type} [DecidableEq Key] [AddCommMonoid K]
    (xs : List A) (key : A → Key) (value : A → K) (target : A)
    (member : target ∈ xs) (unique : (xs.map key).Nodup) :
    (xs.map (fun a => if key a = key target then value a else 0)).sum = value target := by
  induction xs with
  | nil => cases member
  | cons a xs ih =>
    have tail_unique : (xs.map key).Nodup := (List.nodup_cons.mp unique).2
    rcases List.mem_cons.mp member with same | tail_member
    · subst target
      have zeros : xs.map (fun x => if key x = key a then value x else 0) = xs.map (fun _ => (0 : K)) := by
        apply List.map_congr_left
        intro x hx
        apply if_neg
        intro same_key
        exact (List.nodup_cons.mp unique).1 (List.mem_map.mpr ⟨x,hx,same_key⟩)
      simp only [List.map_cons,List.sum_cons,if_pos rfl,zeros]
      simp
    · have different : key a ≠ key target := by
        intro same
        exact (List.nodup_cons.mp unique).1 (List.mem_map.mpr ⟨target,tail_member,same.symm⟩)
      simp only [List.map_cons,List.sum_cons,if_neg different,zero_add]
      exact ih tail_member tail_unique

variable {K : Type} [Field K]

theorem producer_value (A : Trace K) (lam : K) (link : CopyLink) (member : link ∈ copyLinks) :
    copyRowValues A lam link.producer.row CopyLink.producer link.producer.slot =
      copyTupleValue lam (copyProducerTuple A link) := by
  classical
  simpa only [copyRowValues,Prod.mk.injEq,copyProducerTuple] using
    select_unique copyLinks (fun l => (l.producer.row,l.producer.slot))
      (fun l => copyTupleValue lam (copyEndpointTuple A l.tag l.producer)) link member copy_producer_slots_nodup

theorem consumer_value (A : Trace K) (lam : K) (link : CopyLink) (member : link ∈ copyLinks) :
    copyRowValues A lam link.consumer.row CopyLink.consumer link.consumer.slot =
      copyTupleValue lam (copyConsumerTuple A link) := by
  classical
  simpa only [copyRowValues,Prod.mk.injEq,copyConsumerTuple] using
    select_unique copyLinks (fun l => (l.consumer.row,l.consumer.slot))
      (fun l => copyTupleValue lam (copyEndpointTuple A l.tag l.consumer)) link member copy_consumer_slots_nodup

#print axioms select_unique
#print axioms producer_value
#print axioms consumer_value
end R1Z.PV_OptB_CopySelection
