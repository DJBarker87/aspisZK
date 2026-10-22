import MultiproofConePhysicalTrace

set_option autoImplicit false
namespace AspisR1.MultiproofConePhysicalInvariant
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
open MultiproofConePhysicalTrace MultiproofConePhysicalLive

/-- Every layer retains its physical input/output, chronological actual child
reads/hash equations, and exact physical output prefix. -/
def Accounts {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X) (physical : Slice U8) :
    reference.Scratch → reference.Scratch → List (reference.Scratch × List Event) → Prop
  | s,final,[] => final=s
  | s,final,(after,events)::rest =>
      Trace D hash physical s 0#usize 0#usize after events ∧
      view after 0 after.n.val=events.map Event.output ∧
      (∀ e∈events, e.Valid D hash) ∧ Accounts D hash physical after final rest

/-- The level invariant is constructed by Lean induction over actual extracted
successful execution. It includes full digest data, not just sorted indices. -/
theorem iterate_accounts {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (height : Nat)
    (s final : reference.Scratch) (domain : Domain physical s)
    (success : iterate (fun s => reference.level_rows D hash s physical 0#usize 0#usize) height s=ok (.Done final)) :
    ∃ layers, layers.length=height ∧ Accounts D hash physical s final layers := by
  induction height generalizing s with
  | zero => cases success;exact ⟨[],rfl,rfl⟩
  | succ height ih =>
    simp only [iterate] at success
    cases eq : reference.level_rows D hash s physical 0#usize 0#usize with
    | fail e => simp only [eq,bind_tc_fail] at success;cases success
    | div => simp only [eq,bind_tc_div] at success;cases success
    | ok out =>
      rw [eq] at success
      simp only [bind_tc_ok] at success
      cases out with
      | Stop stopped => cases success
      | Done after =>
        obtain ⟨events,trace,content,valid⟩ := level_trace D hash total physical s after domain eq
        obtain ⟨layers,len,accounts⟩ := ih after
          (level_preserve D hash total physical s after domain eq) success
        exact ⟨(after,events)::layers,by simp [len],trace,content,valid,accounts⟩

theorem eighteen_accounts {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (s final : reference.Scratch)
    (domain : Domain physical s)
    (success : reference.levels D hash s physical 18#u32=ok (.Done final)) :
    ∃ layers, layers.length=18 ∧ Accounts D hash physical s final layers := by
  rw [levels_eq_iteration D hash physical 18#u32 (by decide) s] at success
  exact iterate_accounts D hash total physical 18 s final domain success

#print axioms iterate_accounts
#print axioms eighteen_accounts
end AspisR1.MultiproofConePhysicalInvariant
