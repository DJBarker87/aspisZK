import FS2.Theorem
import AspisV8R19.UniformStateFirstHit

/-! # The duplex instance of v2: addresses, samplers, decoder, collision event

Addresses are byte strings of bounded length `L`, stored padded so the index
type is the finite `List.Vector (Option Byte) L`; the frames are those of
`AspisV8R19.DuplexFrames`.  A round absorbs the message into the current
state (`absorb`), then squeezes the challenge material and advances the
state from the absorbed state (`squeeze`, `advance`), read in either order.
The challenge type carries the next state.

The decoder parses the absorb address, walks the table back from the
absorbed state to the initial state through the `advance` and `absorb`
cells, and completes the prefix; the challenge cells still missing from the
table are read by the completing sampler.

The collision event: some first read's fresh state equals the initial state,
equals an earlier output, or is a 32-byte prefix of an address read so far
(including the current one).  Its mass is bounded by v1's Lemma A with
density `2·Q_tot / 2^256` per first read: `κ(Q_tot) = 2·Q_tot² / 2^256`. -/
set_option autoImplicit false
namespace FS2.Duplex

open FS FS2 AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.UniformStateFirstHit
open scoped BigOperators
noncomputable section

/-! ## Bounded byte addresses -/

/-- Padded byte strings of length at most `L`. -/
abbrev Addr (L : Nat) := List.Vector (Option Byte) L

namespace Addr
variable {L : Nat}

def ofBytes (b : Bytes) (h : b.length ≤ L) : Addr L :=
  ⟨b.map some ++ List.replicate (L - b.length) none, by simp; omega⟩

def toBytes (a : Addr L) : Bytes := a.toList.filterMap id

theorem toBytes_ofBytes (b : Bytes) (h : b.length ≤ L) : toBytes (ofBytes b h) = b := by
  simp [toBytes, ofBytes, List.filterMap_append, List.filterMap_map, List.filterMap_replicate]

theorem ofBytes_injective (b b' : Bytes) (h : b.length ≤ L) (h' : b'.length ≤ L)
    (e : ofBytes b h = ofBytes b' h') : b = b' := by
  have := congrArg toBytes e
  rwa [toBytes_ofBytes, toBytes_ofBytes] at this

end Addr

/-! ## Frames -/

instance : Inhabited State := ⟨fun _ => 0⟩

/-- The duplex parameters: address bound, message encoding, labels, the
per-round challenge map from squeezed states, the initial state. -/
structure Params (M Cv : Type) (L : Nat) where
  D : Nat
  hL : 34 + D ≤ L
  enc : M → Bytes
  encLen : ∀ m, (enc m).length ≤ D
  dec : Bytes → Option M
  decEnc : ∀ m, dec (enc m) = some m
  lbl : Nat → Byte
  σ : Nat → State → Cv
  iv : State
  /-- number of challenge rounds (the decoder's walk fuel) -/
  rounds : Nat

variable {M Cv : Type} {L : Nat}

def absorbA (p : Params M Cv L) (s : State) (l : Byte) (data : Bytes) (h : data.length ≤ p.D) :
    Addr L :=
  Addr.ofBytes (absorb (bytes s) l data) (by
    simp [absorb, bytes_length]; have := p.hL; omega)

def squeezeA (p : Params M Cv L) (s : State) : Addr L :=
  Addr.ofBytes (squeeze (bytes s)) (by simp [squeeze, bytes_length]; have := p.hL; omega)

def advanceA (p : Params M Cv L) (s : State) : Addr L :=
  Addr.ofBytes (advance (bytes s)) (by simp [advance, bytes_length]; have := p.hL; omega)

theorem squeezeA_ne_advanceA (p : Params M Cv L) (s : State) : squeezeA p s ≠ advanceA p s := by
  intro h
  exact cross_disjoint _ _ (Addr.ofBytes_injective _ _ _ _ h)

theorem squeezeA_injective (p : Params M Cv L) : Function.Injective (squeezeA p) := by
  intro s s' h
  exact bytes_injective (squeeze_injective (Addr.ofBytes_injective _ _ _ _ h))

/-- Challenge: a value and the next state. -/
abbrev Chal (Cv : Type) := Cv × State

/-- The duplex state after a prefix: the last challenge's state, or `iv`. -/
def stateOf {X : Type} (p : Params M Cv L) (P : Prefix X M (Chal Cv)) : State :=
  match P.rounds.getLast? with
  | none => p.iv
  | some (_, c) => c.2

/-- Round `i`'s sampler: absorb, then squeeze and advance of the absorbed
state in either order. -/
def samp {X : Type} (p : Params M Cv L) (i : Nat) (P : Prefix X M (Chal Cv)) (m : M) :
    Sampler (Addr L) State (Chal Cv) :=
  .ask (absorbA p (stateOf p P) (p.lbl i) (p.enc m) (p.encLen m)) fun s' =>
    .multi (squeezeA p s') [advanceA p s'] (by simp [squeezeA_ne_advanceA]) fun acc =>
      .done (p.σ i (acc (squeezeA p s')), acc (advanceA p s'))

/-! ## Counting over an abstract finite answer type

Stated for abstract finite types so that no concrete `Finset.univ` over
`Fin 32 → Byte` is ever unfolded. -/

section Counting
variable {I S B : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S] [Nonempty S]

def dom (T : Table I S) : Finset I := Finset.univ.filter fun a => T a ≠ none

def outputs (T : Table I S) : Finset S := Finset.univ.filter fun f => ∃ a, T a = some f

omit [DecidableEq I] in
theorem outputs_card_le (T : Table I S) : (outputs T).card ≤ (dom T).card := by
  calc (outputs T).card ≤ ((dom T).image fun a => (T a).getD (Classical.arbitrary _)).card := by
        apply Finset.card_le_card
        intro f hf
        rw [outputs, Finset.mem_filter] at hf
        obtain ⟨a, ha⟩ := hf.2
        rw [Finset.mem_image]
        refine ⟨a, ?_, ?_⟩
        · rw [dom, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, by rw [ha]; exact Option.some_ne_none _⟩
        · rw [ha]; rfl
    _ ≤ (dom T).card := Finset.card_image_le

omit [Fintype I] [DecidableEq I] [DecidableEq S] [Nonempty S] in
theorem mean_indicator_card (q : S → Prop) [DecidablePred q] :
    mean (fun f : S => indicator (q f)) =
      ((Finset.univ.filter q).card : ℚ) / (Fintype.card S : ℚ) := by
  unfold mean
  congr 1
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : q f <;> simp [indicator, h]

omit [Fintype I] [DecidableEq I] [Nonempty S] in
theorem mean_indicator_mem (X : Finset S) :
    mean (fun f : S => indicator (f ∈ X)) = (X.card : ℚ) / (Fintype.card S : ℚ) := by
  rw [mean_indicator_card (fun f => f ∈ X), Finset.filter_mem_eq_inter, Finset.univ_inter]

omit [Fintype I] [DecidableEq I] [Nonempty S] in
theorem mean_indicator_eq (c : S) :
    mean (fun f : S => indicator (f = c)) = 1 / (Fintype.card S : ℚ) := by
  rw [mean_indicator_card (fun f => f = c)]
  simp [Finset.filter_eq']

omit [Fintype I] [DecidableEq I] [DecidableEq S] [Nonempty S] in
theorem mean_indicator_inj_mem [DecidableEq B] (e : S → B) (he : Function.Injective e)
    (X : Finset B) :
    mean (fun f : S => indicator (e f ∈ X)) ≤ (X.card : ℚ) / (Fintype.card S : ℚ) := by
  rw [mean_indicator_card (fun f => e f ∈ X)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card_of_injOn e
    (fun f hf => (Finset.mem_filter.mp hf).2) (fun f _ g _ h => he h)

end Counting

/-! ## The collision event -/

/-- A fresh state at a first read collides: it is the initial state, an
earlier output, or a 32-byte prefix of an address read so far (the current
one included).  The size guard ties the density to `Q_tot`. -/
def badColl (p : Params M Cv L) (Qtot : Nat) (a : Addr L) (T : Table (Addr L) State)
    (f : State) : Prop :=
  (dom T).card < Qtot ∧ (f = p.iv ∨ f ∈ outputs T ∨
    bytes f ∈ (insert a (dom T)).image fun a => a.toBytes.take 32)

theorem badColl_density (p : Params M Cv L) (Qtot : Nat) (a : Addr L) (T : Table (Addr L) State) :
    mean (fun f : State => indicator (badColl p Qtot a T f)) ≤
      (2 * Qtot : ℚ) / (Fintype.card State : ℚ) := by
  by_cases hsz : (dom T).card < Qtot
  · set Pr : Finset Bytes := (insert a (dom T)).image fun a => a.toBytes.take 32 with hPr
    have h1 : ∀ f, indicator (badColl p Qtot a T f) ≤
        indicator (f = p.iv) + indicator (f ∈ outputs T) + indicator (bytes f ∈ Pr) := by
      intro f
      calc indicator (badColl p Qtot a T f)
          ≤ indicator (f = p.iv ∨ f ∈ outputs T ∨ bytes f ∈ Pr) := indicator_mono fun h => h.2
        _ ≤ indicator (f = p.iv) + indicator (f ∈ outputs T ∨ bytes f ∈ Pr) := indicator_or_le _ _
        _ ≤ _ := by
            have := indicator_or_le (f ∈ outputs T) (bytes f ∈ Pr)
            linarith
    have hpre : (Pr.card : ℚ) ≤ ((dom T).card : ℚ) + 1 := by
      have : Pr.card ≤ (dom T).card + 1 :=
        Finset.card_image_le.trans (Finset.card_insert_le _ _)
      exact_mod_cast this
    have hout : ((outputs T).card : ℚ) ≤ ((dom T).card : ℚ) := by exact_mod_cast outputs_card_le T
    have hcard : (0 : ℚ) < (Fintype.card State : ℚ) := by positivity
    calc mean (fun f : State => indicator (badColl p Qtot a T f))
        ≤ mean (fun f : State => indicator (f = p.iv) + indicator (f ∈ outputs T) +
            indicator (bytes f ∈ Pr)) := mean_mono h1
      _ = mean (fun f : State => indicator (f = p.iv)) + mean (fun f : State => indicator (f ∈ outputs T)) +
            mean (fun f : State => indicator (bytes f ∈ Pr)) := by
          rw [mean_add, mean_add]
      _ ≤ 1 / (Fintype.card State : ℚ) + ((dom T).card : ℚ) / (Fintype.card State : ℚ) +
            (((dom T).card : ℚ) + 1) / (Fintype.card State : ℚ) := by
          rw [mean_indicator_eq, mean_indicator_mem]
          have h2 := div_le_div_of_nonneg_right hout hcard.le
          have h3 := (mean_indicator_inj_mem bytes bytes_injective Pr).trans
            (div_le_div_of_nonneg_right hpre hcard.le)
          linarith
      _ ≤ (2 * Qtot : ℚ) / (Fintype.card State : ℚ) := by
          rw [← add_div, ← add_div]
          apply div_le_div_of_nonneg_right _ hcard.le
          have : ((dom T).card : ℚ) + 1 ≤ Qtot := by exact_mod_cast hsz
          linarith
  · have hz : ∀ f, indicator (badColl p Qtot a T f) = 0 := by
      intro f
      rw [indicator_iff (q := False), indicator_false]
      exact ⟨fun h => hsz h.1, False.elim⟩
    rw [mean_congr hz, mean_const]
    positivity

/-- The collision event of an execution. -/
def Coll {Pf : Type} (p : Params M Cv L) (Qtot : Nat) (v : View (Addr L) State (Pf × Bool)) : Prop :=
  hitsBad (badColl p Qtot) emptyTable v.1

/-- `κ(Q_tot) = 2·Q_tot² / 2^256`. -/
def κ (Qtot : Nat) : ℚ := (Qtot : ℚ) * ((2 * Qtot : ℚ) / (256 ^ 32 : ℚ))

theorem coll_mass {X Pf : Type} (p : Params M Cv L) (Qtot : Nat)
    (P : Program (Addr L) State Pf) (V : X → Pf → Program (Addr L) State Bool) (x : X)
    (hQ : ∀ H, distinctFirstReads (eval H (experiment P V x)) ≤ Qtot) :
    mean (fun H : Addr L → State => indicator (Coll p Qtot (eval H (experiment P V x)))) ≤
      κ Qtot := by
  unfold Coll κ
  rw [empty_oracle_law (experiment P V x)
    (fun v => indicator (hitsBad (badColl p Qtot) emptyTable v.1))]
  have hε : (0 : ℚ) ≤ (2 * Qtot : ℚ) / (256 ^ 32 : ℚ) := by positivity
  have hdens : ∀ (a : Addr L) (T : Table (Addr L) State),
      mean (fun f => indicator (badColl p Qtot a T f)) ≤ (2 * Qtot : ℚ) / (256 ^ 32 : ℚ) := by
    intro a T
    have := badColl_density p Qtot a T
    rw [state_card] at this
    push_cast at this
    exact this
  apply FS.lemmaA (experiment P V x) emptyTable Qtot (badColl p Qtot) _ hε hdens
  apply firstReadsBound_of_traces
  intro H
  have := hQ H
  have hc : complete (emptyTable : Table (Addr L) State) H = H := rfl
  rw [hc]
  exact this

#print axioms coll_mass
end
end FS2.Duplex
