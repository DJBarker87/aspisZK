import Port9OR_P6Rows

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_P6Levels
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConeNodeDomain MultiproofConeLevelIteration

def level (s : reference.Scratch) (physical : Slice U8) : Code reference.Level :=
  Port9OR_P6Rows.rows s.n.val s physical 0#usize 0#usize

def levels : Nat → reference.Scratch → Slice U8 → Code reference.Level
  | 0,s,_ => .done (.Done s)
  | h+1,s,physical => do
    let out ← level s physical
    match out with
    | .Stop stopped => pure (.Stop stopped)
    | .Done next => levels h next physical

theorem level_source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (s : reference.Scratch) (physical : Slice U8) (domain : Domain physical s) :
    erase D hash (level s physical)=reference.level_rows (Port9OR_P6Node.digest D) hash s physical 0#usize 0#usize :=
  Port9OR_P6Rows.source D hash physical s.n.val s _ _
    ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩ (by simp)

theorem level_preserve {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (s next : reference.Scratch) (physical : Slice U8) (domain : Domain physical s)
    (ran : reference.level_rows (Port9OR_P6Node.digest D) hash s physical 0#usize 0#usize=ok (.Done next)) :
    Domain physical next := by
  apply Port9OR_P6Rows.preserve D hash physical s.n.val s 0#usize 0#usize
    ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩ (Or.inl rfl) next
  exact (level_source D hash s physical domain).trans ran

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (h : Nat) (s : reference.Scratch) (physical : Slice U8) (domain : Domain physical s) :
    erase D hash (levels h s physical)=
      iterate (fun state => reference.level_rows (Port9OR_P6Node.digest D) hash state physical 0#usize 0#usize) h s := by
  induction h generalizing s with
  | zero => rfl
  | succ h ih =>
    simp only [levels,erase_bind,level_source D hash s physical domain,iterate]
    cases ran : reference.level_rows (Port9OR_P6Node.digest D) hash s physical 0#usize 0#usize with
    | fail e => rfl
    | div => rfl
    | ok out =>
      simp only [bind_tc_ok]
      cases out with
      | Stop stopped => rfl
      | Done next => exact ih next (level_preserve D hash s next physical domain ran)

theorem eighteen {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (s : reference.Scratch) (physical : Slice U8) (domain : Domain physical s) :
    erase D hash (levels 18 s physical)=reference.levels (Port9OR_P6Node.digest D) hash s physical 18#u32 := by
  rw [source D hash 18 s physical domain,levels_eq_iteration _ _ _ _ (by decide)]
  rfl

#print axioms level_source
#print axioms level_preserve
#print axioms source
#print axioms eighteen
end AspisR1.Port9OR_P6Levels
end
