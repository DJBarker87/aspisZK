import R1QueryDecoderAnswers
import R1RawRoundCompletion

/-! Complete raw semantic records from explicit answers for the missing
squeeze cells. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PrefixAnswers

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def missing (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) : List (Addr L) :=
  ((rs.map fun r => squeezeA p r.2.1).filter fun c => T c = none).dedup

def fromAnswers (p : Params M Cv L) (T : Table (Addr L) State)
    (offset : Nat) (rs : List (Rec M)) (as : List State) :=
  completeRounds p T (R0C.V3.DQ.accFrom (missing p T rs) as) offset rs

theorem missing_nodup (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) : (missing p T rs).Nodup := by
  exact List.nodup_dedup _

theorem missing_mem (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (r : Rec M) (hr : r ∈ rs)
    (hnone : T (squeezeA p r.2.1) = none) :
    squeezeA p r.2.1 ∈ missing p T rs := by
  unfold missing
  apply List.mem_dedup.mpr
  apply List.mem_filter.mpr
  constructor
  · exact List.mem_map.mpr ⟨r, hr, rfl⟩
  · simpa using hnone

theorem completeRounds_correct (p : Params M Cv L)
    (T : Table (Addr L) State) (acc H : Addr L → State)
    (offset : Nat) (rs : List (Rec M))
    (hT : ∀ a v, T a = some v → v = H a)
    (hmissing : ∀ r ∈ rs, T (squeezeA p r.2.1) = none →
      acc (squeezeA p r.2.1) = H (squeezeA p r.2.1)) :
    completeRounds p T acc offset rs = completeRounds p emptyTable H offset rs := by
  induction rs generalizing offset with
  | nil => rfl
  | cons r rs ih =>
      simp only [FS2.Duplex.completeRounds]
      rw [AspisR1.QueryCompletion.getter_correct T acc H
        (squeezeA p r.2.1) hT (fun hn => hmissing r (List.mem_cons_self ..) hn)]
      rw [AspisR1.QueryCompletion.getter_correct emptyTable H H
        (squeezeA p r.2.1) (by
          intro a v hv
          simp [emptyTable] at hv) (by intro hn; rfl)]
      rw [ih (offset + 1) (fun r' hr hn =>
        hmissing r' (List.mem_cons_of_mem _ hr) hn)]

theorem fromAnswers_map (p : Params M Cv L)
    (T : Table (Addr L) State) (offset : Nat) (rs : List (Rec M))
    (H : Addr L → State) (hT : ∀ a v, T a = some v → v = H a) :
    fromAnswers p T offset rs ((missing p T rs).map H) =
      completeRounds p emptyTable H offset rs := by
  unfold fromAnswers
  apply completeRounds_correct p T
    (R0C.V3.DQ.accFrom (missing p T rs) ((missing p T rs).map H)) H offset rs hT
  intro r hr hnone
  exact R0C.V3.DQ.accFrom_map H (missing p T rs)
    (squeezeA p r.2.1) (missing_mem p T rs r hr hnone)

#print axioms missing_nodup
#print axioms missing_mem
#print axioms completeRounds_correct
#print axioms fromAnswers_map

end AspisR1.PrefixAnswers
end
