import R1RawRoundCompletion
import R1PrefixPendingFacts

/-! Pointwise known-cell and read facts for explicit record lists. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PrefixRecordFacts

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.InitialWalk

variable {M Cv : Type} {L : Nat}

theorem recs_known (T : Table (Addr L) State)
    (s absorbed : Nat → State) (msg : Nat → M) (next : Nat → State) (n : Nat)
    (hknown : ∀ j < n, ∃ a, T a = some (absorbed j)) :
    ∀ r ∈ RawRoundCompletion.recs s absorbed msg next n,
      ∃ a, T a = some r.2.1 := by
  intro r hr
  unfold RawRoundCompletion.recs at hr
  rcases List.mem_map.mp hr with ⟨j, hj, h⟩
  have hjn : j < n := List.mem_range.mp hj
  subst r
  exact hknown j hjn

theorem recs_reads (p : Params M Cv L) (tr : List (Addr L × State))
    (s absorbed : Nat → State) (msg : Nat → M) (next : Nat → State) (n : Nat)
    (hreads : ∀ j < n, Read tr (squeezeA p (absorbed j))) :
    ∀ r ∈ RawRoundCompletion.recs s absorbed msg next n,
      Read tr (squeezeA p r.2.1) := by
  intro r hr
  unfold RawRoundCompletion.recs at hr
  rcases List.mem_map.mp hr with ⟨j, hj, h⟩
  have hjn : j < n := List.mem_range.mp hj
  subst r
  exact hreads j hjn

def ordinary (ss sb : Nat → State) (sm : Nat → M) (n : Nat)
    (os ob : Nat → State) (om : Nat → M) (k : Nat) : List (Rec M) :=
  (RawRoundCompletion.recs ss sb sm (fun j => ss (j + 1)) n ++
    [(ss n, sb n, sm n, os 0)]) ++
      RawRoundCompletion.recs os ob om (fun j => os (j + 1)) k

theorem ordinary_known (T : Table (Addr L) State)
    (ss sb : Nat → State) (sm : Nat → M) (n : Nat)
    (os ob : Nat → State) (om : Nat → M) (k : Nat)
    (hsemantic : ∀ j < n + 1, ∃ a, T a = some (sb j))
    (hopening : ∀ j < k, ∃ a, T a = some (ob j)) :
    ∀ r ∈ ordinary ss sb sm n os ob om k,
      ∃ a, T a = some r.2.1 := by
  intro r hr
  unfold ordinary at hr
  rcases List.mem_append.mp hr with hleft | hopen
  · rcases List.mem_append.mp hleft with hsemantic' | hboundary
    · exact recs_known T ss sb sm (fun j => ss (j + 1)) n
        (fun j hj => hsemantic j (by omega)) r hsemantic'
    · have hr' := List.mem_singleton.mp hboundary
      subst r
      exact hsemantic n (by omega)
  · exact recs_known T os ob om (fun j => os (j + 1)) k hopening r hopen

theorem ordinary_reads (p : Params M Cv L) (tr : List (Addr L × State))
    (ss sb : Nat → State) (sm : Nat → M) (n : Nat)
    (os ob : Nat → State) (om : Nat → M) (k : Nat)
    (hsemantic : ∀ j < n + 1, Read tr (squeezeA p (sb j)))
    (hopening : ∀ j < k, Read tr (squeezeA p (ob j))) :
    ∀ r ∈ ordinary ss sb sm n os ob om k,
      Read tr (squeezeA p r.2.1) := by
  intro r hr
  unfold ordinary at hr
  rcases List.mem_append.mp hr with hleft | hopen
  · rcases List.mem_append.mp hleft with hsemantic' | hboundary
    · exact recs_reads p tr ss sb sm (fun j => ss (j + 1)) n
        (fun j hj => hsemantic j (by omega)) r hsemantic'
    · have hr' := List.mem_singleton.mp hboundary
      subst r
      exact hsemantic n (by omega)
  · exact recs_reads p tr os ob om (fun j => os (j + 1)) k hopening r hopen

#print axioms recs_known
#print axioms recs_reads
#print axioms ordinary_known
#print axioms ordinary_reads

end AspisR1.PrefixRecordFacts
end
