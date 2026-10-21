import MultiproofConeRef.Funs
import OraclePortFrozenOrderSlot

/-! Checked height composition for the actual extracted recursive reference.
The one-level representation/preservation obligation is explicit. This is not
an inhabitant of the complete source cone and does not claim a source log. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeHeight
open Aeneas Aeneas.Std Result
open MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortFrozenOrder

/-- Relates reference poststates to a mathematical live frontier and suffix.
The relation can also retain all scratch suffix/frame properties. -/
abbrev Representation := reference.Scratch → Live → Bytes → Prop

def LevelMeaning (R : Representation) : reference.Level → Option (Live × Bytes) → Prop
  | .Stop _, none => True
  | .Done s, some (live,nodes) => R s live nodes
  | _, _ => False

/-- A local row contract, not an assumed height-18 or whole-cone equality.
Ordinary short-sibling rejection is included as Stop/none. -/
def RowJoin {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (physical : Slice U8) (H : Bytes → State) (R : Representation) : Prop :=
  ∀ s live nodes, R s live nodes → ∃ out,
    reference.level_rows D hash s physical 0#usize 0#usize = ok out ∧
    LevelMeaning R out (eval H (runLevel live.length live nodes)).2

theorem height_total {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (physical : Slice U8) (H : Bytes → State) (R : Representation)
    (rows : RowJoin D hash physical H R)
    (height : U32) (hbound : height.val ≤ 18)
    (s : reference.Scratch) (live : Live) (nodes : Bytes) (rep : R s live nodes) :
    ∃ out, reference.levels D hash s physical height = ok out ∧
      LevelMeaning R out (eval H (runLevels height.val live nodes)).2 := by
  generalize hn : height.val = n at hbound ⊢
  induction n generalizing height s live nodes with
  | zero =>
    have hz : height = 0#u32 := UScalar.eq_of_val_eq hn
    subst height
    rw [reference.levels]
    exact ⟨.Done s, rfl, rep⟩
  | succ n ih =>
    have hnz : height ≠ 0#u32 := by
      intro hz
      subst height
      simp at hn
    obtain ⟨row, hrow, meaning⟩ := rows s live nodes rep
    rw [reference.levels]
    simp only [hnz, if_false, hrow, bind_tc_ok]
    cases row with
    | Stop stopped =>
      refine ⟨.Stop stopped, rfl, ?_⟩
      have hm : (eval H (runLevel live.length live nodes)).2 = none := by
        cases hv : (eval H (runLevel live.length live nodes)).2 <;>
          simpa only [LevelMeaning, hv] using meaning
      simpa only [runLevels, eval_bind, hm, eval, LevelMeaning]
    | Done next =>
      cases hm : (eval H (runLevel live.length live nodes)).2 with
      | none => simp only [LevelMeaning, hm] at meaning
      | some pair =>
        rcases pair with ⟨nextLive,nextNodes⟩
        have nextRep : R next nextLive nextNodes := by
          simpa only [LevelMeaning, hm] using meaning
        have hsub : ∃ pred, height - 1#u32 = ok pred ∧ pred.val = n := by
          have spec := UScalar.sub_spec (x := height) (y := 1#u32) (by scalar_tac)
          obtain ⟨pred, hpred, hp⟩ := WP.spec_imp_exists spec
          exact ⟨pred,hpred,by scalar_tac⟩
        obtain ⟨pred,hpred,hpn⟩ := hsub
        obtain ⟨out,hout,mout⟩ := ih pred next nextLive nextNodes nextRep hpn (by omega)
        refine ⟨out, ?_, ?_⟩
        · simpa only [hpred, bind_tc_ok] using hout
        · simpa only [runLevels, eval_bind, hm] using mout

#print axioms height_total
end AspisR1.MultiproofConeHeight
end
