import Port12COUNT_Levels
import Port9OR_P6Verify
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port12COUNT_Verify
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConeNodeDomain MultiproofConeLevelIteration Port12COUNT_Potential Port12COUNT_Rows
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem eval_lift_join {A B Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (r : Result A) (k : A → Code B) :
    eval H (Port9OR_Code.program D hash (liftResult r >>= k)) =
      match r with
      | .ok a => eval H (Port9OR_Code.program D hash (k a))
      | .fail e => ([],.fail e)
      | .div => ([],.div) := by
  change eval H (Port9OR_Code.program D hash (CheckpointBytes5Effect.bind (liftResult r) k)) = _
  cases r <;> rfl

theorem bind_count {A B Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (code : Code A) (k : A → Code B)
    (n m : Nat) (first : (eval H (Port9OR_Code.program D hash code)).1.length≤n)
    (tail : ∀ a, (eval H (Port9OR_Code.program D hash code)).2=.ok a →
      (eval H (Port9OR_Code.program D hash (k a))).1.length≤m) :
    (eval H (Port9OR_Code.program D hash (code >>= k))).1.length≤n+m := by
  rw [eval_join]
  cases ran : eval H (Port9OR_Code.program D hash code) with
  | mk log result =>
    simp only [ran] at first
    cases result with
    | fail e => exact first.trans (by omega)
    | div => exact first.trans (by omega)
    | ok a =>
      have rest := tail a (congrArg Prod.snd ran)
      simp only [List.length_append]
      omega

/-- The real count guards imply the domain; every pre/post guard failure is
hash-free, and the physical levels consume the exact passed node slice. -/
theorem count {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State) (root : Digest) (s : reference.Scratch) (nodes : Slice U8) :
    (eval H (Port9OR_Code.program D hash (Port9OR_P6Verify.code root s nodes))).1.length ≤
      nodes.val.length/32+s.n.val-1 := by
  unfold Port9OR_P6Verify.code
  split
  · exact Nat.zero_le _
  · rename_i nonzero
    split
    · exact Nat.zero_le _
    · rename_i small
      have domain : Domain nodes {s with «at»:=0#usize} := by
        refine ⟨?_,?_,?_⟩
        · change 0<s.n.val
          have nz : s.n.val≠0 := by intro eq;exact nonzero (UScalar.eq_of_val_eq eq)
          omega
        · change s.n.val≤16
          change ¬s.n.val>16 at small;omega
        · change 0≤nodes.val.length;omega
      rw [eval_lift_join]
      split
      · split
        · rw [eval_lift_join]
          split
          · split
            · exact Nat.zero_le _
            · have first := Port12COUNT_Levels.count D hash H nodes 18 {s with «at»:=0#usize} domain
              have joined := bind_count D hash H
                (Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes)
                (fun out => liftResult (Port9OR_P6Verify.after root nodes out))
                (nodes.val.length/32+s.n.val-1) 0 (by simpa using first) (by
                  intro out _
                  cases Port9OR_P6Verify.after root nodes out <;> exact Nat.zero_le 0)
              simpa using joined
          · exact Nat.zero_le _
          · exact Nat.zero_le _
        · exact Nat.zero_le _
      · exact Nat.zero_le _
      · exact Nat.zero_le _

#print axioms eval_lift_join
#print axioms bind_count
#print axioms count
end AspisR1.Port12COUNT_Verify
end
