import R1PrefixAnswers
import R1QueryCompletionSupport

/-! Use one ordered answer list for the missing cells of both decoded
components. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointPrefixAnswers

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def missing (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) : List (Addr L) :=
  (PrefixAnswers.missing p T rs ++ QueryDecoder.missing p T endpoint).dedup

def fromAnswers (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (as : List State) :=
  let acc := R0C.V3.DQ.accFrom (missing p T rs endpoint) as
  (completeRounds p T acc 0 rs, QueryDecoder.recover p T acc endpoint)

theorem missing_nodup (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) :
    (missing p T rs endpoint).Nodup := by
  exact List.nodup_dedup _

theorem prefix_mem (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (b : Addr L)
    (hb : b ∈ PrefixAnswers.missing p T rs) : b ∈ missing p T rs endpoint := by
  unfold missing
  apply List.mem_dedup.mpr
  apply List.mem_append.mpr
  exact Or.inl hb

theorem query_mem (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (b : Addr L)
    (hb : b ∈ QueryDecoder.missing p T endpoint) : b ∈ missing p T rs endpoint := by
  unfold missing
  apply List.mem_dedup.mpr
  apply List.mem_append.mpr
  exact Or.inr hb

theorem missing_cases (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (b : Addr L)
    (hb : b ∈ missing p T rs endpoint) :
    b ∈ PrefixAnswers.missing p T rs ∨ b ∈ QueryDecoder.missing p T endpoint := by
  unfold missing at hb
  rw [List.mem_dedup] at hb
  exact List.mem_append.mp hb

theorem fromAnswers_map (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (H : Addr L → State)
    (hT : ∀ a v, T a = some v → v = H a) :
    fromAnswers p T rs endpoint ((missing p T rs endpoint).map H) =
      (completeRounds p emptyTable H 0 rs, QueryDecoder.recover p T H endpoint) := by
  unfold fromAnswers
  dsimp only
  apply Prod.ext
  · apply PrefixAnswers.completeRounds_correct p T
      (R0C.V3.DQ.accFrom (missing p T rs endpoint)
        ((missing p T rs endpoint).map H)) H 0 rs hT
    intro r hr hnone
    exact R0C.V3.DQ.accFrom_map H (missing p T rs endpoint)
      (squeezeA p r.2.1)
      (prefix_mem p T rs endpoint _
        (PrefixAnswers.missing_mem p T rs r hr hnone))
  · apply QueryDecoder.recover_congr_on_missing p T
      (R0C.V3.DQ.accFrom (missing p T rs endpoint)
        ((missing p T rs endpoint).map H)) H endpoint
    intro b hb
    exact R0C.V3.DQ.accFrom_map H (missing p T rs endpoint) b
      (query_mem p T rs endpoint b hb)

#print axioms missing_nodup
#print axioms prefix_mem
#print axioms query_mem
#print axioms missing_cases
#print axioms fromAnswers_map

end AspisR1.JointPrefixAnswers
end
