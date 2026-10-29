import R1Z.ProverCommitFuelJoin22
import PV_RJ4IDB_SourceTrace
set_option autoImplicit false
noncomputable section
namespace PV_FIB_Restricted
open R1Z R0Z.FsStatement

/-- Instantiate old and queries with EXACTLY the headline expressions, never
with a source prefix, a new abort event, or an independently sampled tape. -/
def OffCharged {M : Type} (old : Fin 8 → M → Prop)
    (queries : M → List ProverCommitSeedEvent19.Entry)
    (r : (M × OracleAnswer) × ProverCommitFuelJoin22.Tape) : Prop :=
  ¬ ∃ i, ProverCommitFuelJoin22.bad old queries i r

theorem offCharged_exact {M : Type} (old : Fin 8 → M → Prop)
    (queries : M → List ProverCommitSeedEvent19.Entry)
    (r : (M × OracleAnswer) × ProverCommitFuelJoin22.Tape) :
    OffCharged old queries r ↔
      (∀ i, ¬ old i r.1.1) ∧
      (¬ ProverCommitSeedEvent19.seedGuess (queries r.1.1) r.1.2) ∧
      (∀ j, ¬ ProverCommitFuelJoin22.failure j r.2) := by
  constructor
  · intro hn
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact hn ⟨i, Or.inl (Or.inl hi)⟩
    · intro hs
      exact hn ⟨0, Or.inl (Or.inr ⟨rfl, hs⟩)⟩
    · intro j hj
      exact hn ⟨0, Or.inr ⟨rfl, j, hj⟩⟩
  · rintro ⟨ho, hs, hf⟩ ⟨i, (hi | ⟨_, hit⟩) | ⟨_, j, hj⟩⟩
    · exact ho i hi
    · exact hs hit
    · exact hf j hj

/-- I ranges over COMMON samples of every actual invocation (including
witness and adversary). good i is OffCharged old queries (cp.toM s).
No acceptance, success, fixed witness, or fixed native prefix restriction.
Public equality includes the statement and ALL public invocation data.
Signal is only the owner-option-B failure signal, never elapsed time or a
secret-dependent prefix. Its native witness independence is a separate link. -/
def Fibres {I P S R V : Type} (good : I → Prop)
    (public : I → P) (signal : I → S) (returned : I → R)
    (observe : I → V) : Prop :=
  ∀ l r, good l → good r → public l = public r → signal l = signal r →
    returned l = returned r → observe l = observe r

/-- This form retains all successful states, same-error failure prefixes,
and every finite divergent prefix. It is stronger than decision equality. -/
def SourceFibres {I P S W A : Type} (good : I → Prop)
    (public : I → P) (signal : I → S)
    (run : I → R1Z.PV_W_Threading.Run W PV_RJ4IDB.Event Aeneas.Std.Error A)
    (render : Aeneas.Std.Error → PV_RJ4IDB.Bytes) : Prop :=
  Fibres good public signal
    (fun i => R1Z.PV_RunJoin_WorldDecode33.returned (run i))
    (fun i => PV_RJ4IDB.actualObservation render (run i))

theorem decoder_implies_fibres {I P S R V : Type} (good : I → Prop)
    (public : I → P) (signal : I → S) (returned : I → R) (observe : I → V)
    (decode : P → S → R → V)
    (link : ∀ i, good i → decode (public i) (signal i) (returned i) = observe i) :
    Fibres good public signal returned observe := by
  intro l r hl hr hp hs hout
  rw [← link l hl, ← link r hr, hp, hs, hout]

/-- A single unequal retained component refutes the COMPLETE fibre. -/
theorem component_obstruction {I P S R V C : Type} (good : I → Prop)
    (public : I → P) (signal : I → S) (returned : I → R) (observe : I → V)
    (component : V → C) (l r : I)
    (hl : good l) (hr : good r) (hp : public l = public r)
    (hs : signal l = signal r) (hout : returned l = returned r)
    (different : component (observe l) ≠ component (observe r)) :
    ¬ Fibres good public signal returned observe := by
  intro hf
  exact different (congrArg component (hf l r hl hr hp hs hout))

/-- Native application: extend ONE completed non-bad honest computation by
its post-computation clock read. The source audit, not this generic theorem,
justifies which values depend on that read. No non-bad native run is invented. -/
theorem post_clock_obstruction {I P S R T : Type} (good : I → Prop)
    (public : I → P) (signal : I → S) (returned : I → R)
    (s : I) (hs : good s) (t u : T) (different : t ≠ u) :
    ¬ Fibres (fun x : I × T => good x.1) (fun x => public x.1)
      (fun x => signal x.1) (fun x => returned x.1) (fun x => x.2) := by
  intro hf
  exact different (hf (s,t) (s,u) hs hs rfl rfl rfl)

#print axioms offCharged_exact
#print axioms decoder_implies_fibres
#print axioms component_obstruction
#print axioms post_clock_obstruction
end PV_FIB_Restricted
