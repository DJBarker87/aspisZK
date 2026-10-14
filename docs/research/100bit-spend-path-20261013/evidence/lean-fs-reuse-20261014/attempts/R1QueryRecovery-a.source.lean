import R1DuplexRewind
import R1QueryContinuation

/-! Recover the finite advance path leading to the actual q22 continuation
state. All eight advance cells remain explicit table premises. This does
not yet discover the absorb boundary or construct a completing decoder. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryRecovery
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem selected_path_recovered (p : Params M Cv L) (T : Table (Addr L) State)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hT : ∀ a v, T a = some v → v = H a ∧ Read tr a)
    (s : Nat → State) (bs : List State) (hbs : bs.length = 8)
    (hstep : ∀ j < 8, s (j + 1) = H (advanceA p (s j)))
    (hcells : ∀ j < 8, T (advanceA p (s j)) = some (s (j + 1))) :
    ∃ k : Nat, k < 8 ∧
      (Q22.scanOut 8 Q22.q0 bs ((List.range 8).map (fun j => s (j + 1))) (s 0)).2 =
        s (k + 1) ∧
      DuplexRewind.rewind p T (k + 1)
        (Q22.scanOut 8 Q22.q0 bs ((List.range 8).map (fun j => s (j + 1))) (s 0)).2 =
        some ((List.range (k + 2)).map s) := by
  have hm := QueryContinuation.eight_pair_continuation bs
    ((List.range 8).map (fun j => s (j + 1))) (s 0) hbs (by simp)
  obtain ⟨k, hk, heq⟩ := List.mem_map.mp hm
  have hk8 : k < 8 := List.mem_range.mp hk
  refine ⟨k, hk8, heq.symm, ?_⟩
  rw [← heq]
  exact DuplexRewind.rewind_of_noColl p T H tr Qtot (k + 1) hcons hQ hcoll hT s
    (fun j hj => hstep j (by omega)) (fun j hj => hcells j (by omega))

#print axioms selected_path_recovered
end AspisR1.QueryRecovery
end
