import Port9OR_P6Levels

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_P6Verify
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConeLevelIteration

/-- Unchanged pure final guards AFTER the reached physical height traversal. -/
def after (root : CheckpointBytes5Effect.Digest) (nodes : Slice U8) :
    reference.Level → Result (Bool × reference.Scratch)
  | .Stop out => ok (false,out)
  | .Done out => do
    if out.n=1#usize then
      let index ← Array.index_usize out.idx 0#usize
      if index=0#u32 then
        let value ← Array.index_usize out.val 0#usize
        let same ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 value root
        if same then ok (out.«at»=Slice.len nodes,out) else ok (false,out)
      else ok (false,out)
    else ok (false,out)

def code (root : CheckpointBytes5Effect.Digest) (s : reference.Scratch)
    (nodes : Slice U8) : Code (Bool × reference.Scratch) := do
  if s.n=0#usize then pure (false,s) else
    if s.n>16#usize then pure (false,s) else
      let valid ← liftResult (reference.valid_indices s.idx s.n 0#usize)
      if valid then
        let rem ← liftResult (Slice.len nodes % 32#usize)
        if rem != 0#usize then pure (false,s) else
          let out ← Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes
          liftResult (after root nodes out)
      else pure (false,s)

def factored {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : CheckpointBytes5Effect.Digest) (s : reference.Scratch) (nodes : Slice U8) :
    Result (Bool × reference.Scratch) := do
  if s.n=0#usize then ok (false,s) else
    if s.n>16#usize then ok (false,s) else
      let valid ← reference.valid_indices s.idx s.n 0#usize
      if valid then
        let rem ← Slice.len nodes % 32#usize
        if rem != 0#usize then ok (false,s) else
          let out ← reference.levels D hash {s with «at»:=0#usize} nodes 18#u32
          after root nodes out
      else ok (false,s)

theorem source_factor {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : CheckpointBytes5Effect.Digest) (s : reference.Scratch) (nodes : Slice U8) :
    factored D hash root s nodes=reference.verify_owned D hash root s nodes := rfl

/-- ALL inputs/results, including invalid counts/indices, rejected padding,
short nodes, partial scratch and hash/checked primitive outer failure. -/
theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : CheckpointBytes5Effect.Digest) (s : reference.Scratch) (nodes : Slice U8) :
    erase D hash (code root s nodes)=reference.verify_owned (Port9OR_P6Node.digest D) hash root s nodes := by
  rw [← source_factor]
  unfold code factored
  simp only [erase_ite,erase_pure,erase_bind,erase_lift]
  split
  · rfl
  · rename_i nonzero
    split
    · rfl
    · rename_i bounded
      have domain : Domain nodes {s with «at»:=0#usize} := by
        refine ⟨?_,?_,?_⟩
        · have nz : s.n.val≠0 := by intro eq;exact nonzero (UScalar.eq_of_val_eq eq)
          omega
        · change ¬s.n.val>16 at bounded;omega
        · change 0≤nodes.val.length;omega
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro valid _
      split
      · apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro rem _
        split
        · rfl
        · rw [Port9OR_P6Levels.eighteen D hash _ nodes domain]
      · rfl

#print axioms source_factor
#print axioms source
end AspisR1.Port9OR_P6Verify
end
