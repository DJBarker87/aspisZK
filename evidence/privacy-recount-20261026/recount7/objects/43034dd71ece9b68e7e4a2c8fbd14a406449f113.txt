import R1Z.ProverRwRngOwnerInventory
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngOwnerCertificate
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerStep ProverRwRngOwnerEvents ProverRwRngOwnerInventory
variable [ErasureFns]

/-- Universal cap16 same-event certificate for the two source-derived owners.
No nonce/reply nonzero restriction, no prior-count<128 premise, no output-
equality premise, and no OS law or native-error/drop installation is assumed.
The `.ok` premise admits an extraction execution, including either native-
prototype error constructor. It excludes tape unavailability, not OS errors. -/
theorem universal_cap16 (nonce : Array U8 32#usize) (p : Tape) :
    old_owner nonce p = owner nonce p ∧
    ∀ after status, owner nonce p = .ok (after,status) →
      ∃ states,
        OwnerReplay (oldBody nonce) Prod.swap nonce p states (after,status) ∧
        OwnerReplay (newBody nonce) id nonce p states (after,status) ∧
        after.replies = p.replies ∧
        after.used.val = p.used.val + drawCount states ∧
        drawCount states ≤ 16 ∧
        events states = (List.range' p.used.val (drawCount states)).map
          (fun index => (Array.repeat 64#usize 0#u8,index,p.replies.val[index]?)) ∧
        (∀ event ∈ events states, event.2.2.isSome = true) ∧
        after.replies.val.drop after.used.val =
          p.replies.val.drop (p.used.val + drawCount states) := by
  obtain ⟨same,paths⟩ := ProverRwRngOwnerEvents.cap16_same_event nonce p
  refine ⟨same,?_⟩
  intro after status run
  obtain ⟨states,oldPath,newPath⟩ := paths after status run
  refine ⟨states,oldPath,newPath,?_⟩
  rcases newPath with rejected | entered
  · rcases rejected with ⟨scan,empty,final⟩
    cases final
    subst states
    exact ⟨rfl,rfl,by decide,rfl,by simp only [events,List.not_mem_nil,false_implies,implies_true],rfl⟩
  · rcases entered with ⟨scan,raw,replay,final⟩
    change raw = (after,status) at final
    subst raw
    obtain ⟨replies,cursor,bounded⟩ := replay_inventory nonce replay
    have cap : drawCount states ≤ 16 := bounded.trans (Nat.sub_le 16 _)
    refine ⟨replies,cursor,cap,replay_events nonce replay,replay_available nonce replay,?_⟩
    rw [replies,cursor]

/-- The historical single-iteration Kani restriction is sufficient for all
actual cap16 counts starting at zero. The universal proof above does not
consume that finite-machine cut: its source-body theorem is stronger. -/
theorem historical_cut_sufficient (used : Nat) (bounded : used ≤ 16) :
    used < 128 ∧ used + 1 < 65536 := by omega

#print axioms universal_cap16
#print axioms historical_cut_sufficient
end R1Z.ProverRwRngOwnerCertificate
