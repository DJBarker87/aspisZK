import R1TraceTableMembership

/-! A total specification-level representative of an oracle table with a
finite graph. It depends only on the table, not on a future oracle or trace.
Actual first-read tables have such a representative. This choice-based
interface carries no efficient enumeration claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.TableLogRepresentative

open FS FS2.Duplex AspisV8PairedCommitment

variable {I A : Type} [DecidableEq I]

def Represents (T : Table I A) (tr : List (I × A)) : Prop :=
  ∀ a v, (a, v) ∈ tr ↔ T a = some v

noncomputable def logOf (T : Table I A) : List (I × A) := by
  classical
  exact if h : ∃ tr, Represents T tr then Classical.choose h else []

theorem logOf_represents (T : Table I A) (h : ∃ tr, Represents T tr) :
    Represents T (logOf T) := by
  rw [logOf, dif_pos h]
  exact Classical.choose_spec h

theorem represents_replay (H : I → A) (tr : List (I × A))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) :
    Represents (TraceTable.replay emptyTable tr) tr :=
  TraceTableMembership.mem_iff_replay_some H tr hcons

theorem represents_consistent (T : Table I A) (tr : List (I × A))
    (H : I → A) (hrep : Represents T tr)
    (hsound : ∀ a v, T a = some v → v = H a) :
    ∀ q ∈ tr, q.2 = H q.1 := by
  rintro ⟨a, v⟩ hq
  exact hsound a v ((hrep a v).mp hq)

theorem replay_of_represents (T : Table I A) (tr : List (I × A))
    (H : I → A) (hrep : Represents T tr)
    (hsound : ∀ a v, T a = some v → v = H a) :
    TraceTable.replay emptyTable tr = T := by
  funext a
  have hcons := represents_consistent T tr H hrep hsound
  cases ht : T a with
  | some v =>
      exact (TraceTableMembership.mem_iff_replay_some H tr hcons a v).mp
        ((hrep a v).mpr ht)
  | none =>
      cases hr : TraceTable.replay emptyTable tr a with
      | none => rfl
      | some v =>
          have hmem := (TraceTableMembership.mem_iff_replay_some H tr hcons a v).mpr hr
          have hv := (hrep a v).mp hmem
          rw [ht] at hv
          cases hv

theorem replay_sound (H : I → A) (tr : List (I × A))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (a : I) (v : A)
    (hv : TraceTable.replay emptyTable tr a = some v) : v = H a := by
  exact hcons (a, v) ((TraceTableMembership.mem_iff_replay_some H tr hcons a v).mpr hv)

/-- In particular, replacing a consistent finite trace by the table's chosen
representative preserves every recorded key/value pair and replayed table. -/
theorem logOf_replay (H : I → A) (tr : List (I × A))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) :
    (∀ q ∈ logOf (TraceTable.replay emptyTable tr), q.2 = H q.1) ∧
    TraceTable.replay emptyTable (logOf (TraceTable.replay emptyTable tr)) =
      TraceTable.replay emptyTable tr := by
  have hrep := logOf_represents (TraceTable.replay emptyTable tr)
    ⟨tr, represents_replay H tr hcons⟩
  have hs := replay_sound H tr hcons
  exact ⟨represents_consistent _ _ H hrep hs, replay_of_represents _ _ H hrep hs⟩

#print axioms logOf_represents
#print axioms represents_replay
#print axioms represents_consistent
#print axioms replay_of_represents
#print axioms logOf_replay
end AspisR1.TableLogRepresentative
end
