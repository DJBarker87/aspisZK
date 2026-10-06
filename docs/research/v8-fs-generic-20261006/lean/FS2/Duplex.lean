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

theorem advanceA_injective (p : Params M Cv L) : Function.Injective (advanceA p) := by
  intro s s' h
  exact bytes_injective (advance_injective (Addr.ofBytes_injective _ _ _ _ h))

theorem toBytes_squeezeA (p : Params M Cv L) (s : State) :
    (squeezeA p s).toBytes.take 32 = bytes s := by
  rw [squeezeA, Addr.toBytes_ofBytes, squeeze, List.take_append_of_le_length (by rw [bytes_length]),
    List.take_of_length_le (by rw [bytes_length])]

theorem toBytes_advanceA (p : Params M Cv L) (s : State) :
    (advanceA p s).toBytes.take 32 = bytes s := by
  rw [advanceA, Addr.toBytes_ofBytes, advance, List.take_append_of_le_length (by rw [bytes_length]),
    List.take_of_length_le (by rw [bytes_length])]

theorem toBytes_absorbA (p : Params M Cv L) (s : State) (l : Byte) (data : Bytes)
    (h : data.length ≤ p.D) : (absorbA p s l data h).toBytes.take 32 = bytes s := by
  rw [absorbA, Addr.toBytes_ofBytes, absorb, List.append_assoc,
    List.take_append_of_le_length (by rw [bytes_length]), List.take_of_length_le (by rw [bytes_length])]

theorem squeezeA_ne_absorbA (p : Params M Cv L) (s s' : State) (l : Byte) (data : Bytes)
    (h : data.length ≤ p.D) : squeezeA p s ≠ absorbA p s' l data h := by
  intro e
  have := congrArg (fun a : Addr L => a.toBytes.length) e
  simp [squeezeA, absorbA, Addr.toBytes_ofBytes, squeeze, absorb, bytes_length] at this
  omega

theorem advanceA_ne_absorbA (p : Params M Cv L) (s s' : State) (l : Byte) (data : Bytes)
    (h : data.length ≤ p.D) : advanceA p s ≠ absorbA p s' l data h := by
  intro e
  have := congrArg (fun a : Addr L => a.toBytes.length) e
  simp [advanceA, absorbA, Addr.toBytes_ofBytes, advance, absorb, bytes_length] at this
  omega

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
`Fin 32 → Byte` is ever unfolded; the collision predicate below mentions no
`Finset`, only existentials, for the same reason. -/

section Counting
variable {I S B : Type} [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S] [Nonempty S]

def dom (T : Table I S) : Finset I := Finset.univ.filter fun a => T a ≠ none

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
theorem mean_indicator_eq (c : S) :
    mean (fun f : S => indicator (f = c)) = 1 / (Fintype.card S : ℚ) := by
  rw [mean_indicator_card (fun f => f = c)]
  simp [Finset.filter_eq']

omit [DecidableEq S] in
/-- Outputs of a table: at most as many as its domain. -/
theorem mean_exists_output_le (T : Table I S) :
    mean (fun f : S => indicator (∃ a, T a = some f)) ≤ ((dom T).card : ℚ) / (Fintype.card S : ℚ) := by
  classical
  rw [mean_indicator_card (fun f => ∃ a, T a = some f)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (Finset.univ.filter fun f : S => ∃ a, T a = some f) ⊆
      (dom T).image fun a => (T a).getD (Classical.arbitrary S) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨a, ha⟩ := hf.2
    rw [Finset.mem_image]
    refine ⟨a, ?_, ?_⟩
    · rw [dom, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [ha]; exact Option.some_ne_none _⟩
    · rw [ha]; rfl
  exact_mod_cast (Finset.card_le_card this).trans Finset.card_image_le

omit [DecidableEq I] [DecidableEq S] [Nonempty S] in
/-- Values whose image under an injection hits the image of a predicate's
domain: at most as many as that domain. -/
theorem mean_exists_prefix_le [DecidableEq B] (e : S → B) (he : Function.Injective e)
    (P : I → Prop) [DecidablePred P] (g : I → B) :
    mean (fun f : S => indicator (∃ b, P b ∧ g b = e f)) ≤
      ((Finset.univ.filter P).card : ℚ) / (Fintype.card S : ℚ) := by
  classical
  rw [mean_indicator_card (fun f => ∃ b, P b ∧ g b = e f)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : (Finset.univ.filter fun f : S => ∃ b, P b ∧ g b = e f).card ≤
      ((Finset.univ.filter P).image g).card := by
    apply Finset.card_le_card_of_injOn e
    · intro f hf
      rw [Finset.mem_coe, Finset.mem_filter] at hf
      obtain ⟨b, hb, hg⟩ := hf.2
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, hg⟩
    · intro f _ f' _ h
      exact he h
  exact_mod_cast h1.trans Finset.card_image_le

omit [Fintype S] [DecidableEq S] [Nonempty S] in
theorem card_filter_insert_le (T : Table I S) (a : I) :
    (Finset.univ.filter fun b : I => b = a ∨ T b ≠ none).card ≤ (dom T).card + 1 := by
  calc (Finset.univ.filter fun b : I => b = a ∨ T b ≠ none).card
      ≤ (insert a (dom T)).card := by
        apply Finset.card_le_card
        intro b hb
        rw [Finset.mem_filter] at hb
        rw [Finset.mem_insert]
        rcases hb.2 with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    _ ≤ (dom T).card + 1 := Finset.card_insert_le _ _

end Counting

/-! ## The collision event -/

/-- A fresh state at a first read collides: it is the initial state, an
earlier output, or a 32-byte prefix of an address read so far (the current
one included).  The size guard ties the density to `Q_tot`. -/
def badColl (p : Params M Cv L) (Qtot : Nat) (a : Addr L) (T : Table (Addr L) State)
    (f : State) : Prop :=
  (dom T).card < Qtot ∧ (f = p.iv ∨ (∃ b, T b = some f) ∨
    ∃ b, (b = a ∨ T b ≠ none) ∧ b.toBytes.take 32 = bytes f)

theorem badColl_of_iv (p : Params M Cv L) (Qtot : Nat) (a : Addr L) (T : Table (Addr L) State)
    (f : State) (hsz : (dom T).card < Qtot) (h : f = p.iv) : badColl p Qtot a T f :=
  ⟨hsz, Or.inl h⟩

theorem badColl_of_output (p : Params M Cv L) (Qtot : Nat) (a : Addr L) (T : Table (Addr L) State)
    (f : State) (hsz : (dom T).card < Qtot) (b : Addr L) (h : T b = some f) : badColl p Qtot a T f :=
  ⟨hsz, Or.inr (Or.inl ⟨b, h⟩)⟩

theorem badColl_of_prefix (p : Params M Cv L) (Qtot : Nat) (a : Addr L) (T : Table (Addr L) State)
    (f : State) (hsz : (dom T).card < Qtot) (b : Addr L) (hb : b = a ∨ T b ≠ none)
    (h : b.toBytes.take 32 = bytes f) : badColl p Qtot a T f :=
  ⟨hsz, Or.inr (Or.inr ⟨b, hb, h⟩)⟩

theorem badColl_density (p : Params M Cv L) (Qtot : Nat) (a : Addr L) (T : Table (Addr L) State) :
    mean (fun f : State => indicator (badColl p Qtot a T f)) ≤
      (2 * Qtot : ℚ) / (Fintype.card State : ℚ) := by
  classical
  by_cases hsz : (dom T).card < Qtot
  · have h1 : ∀ f, indicator (badColl p Qtot a T f) ≤
        indicator (f = p.iv) + indicator (∃ b, T b = some f) +
          indicator (∃ b, (b = a ∨ T b ≠ none) ∧ b.toBytes.take 32 = bytes f) := by
      intro f
      calc indicator (badColl p Qtot a T f)
          ≤ indicator (f = p.iv ∨ (∃ b, T b = some f) ∨
              ∃ b, (b = a ∨ T b ≠ none) ∧ b.toBytes.take 32 = bytes f) :=
            indicator_mono fun h => h.2
        _ ≤ indicator (f = p.iv) + indicator ((∃ b, T b = some f) ∨
              ∃ b, (b = a ∨ T b ≠ none) ∧ b.toBytes.take 32 = bytes f) := indicator_or_le _ _
        _ ≤ _ := by
            have := indicator_or_le (∃ b, T b = some f)
              (∃ b, (b = a ∨ T b ≠ none) ∧ b.toBytes.take 32 = bytes f)
            linarith
    have hcard : (0 : ℚ) < (Fintype.card State : ℚ) := by positivity
    have hout := mean_exists_output_le T
    have hfilt : ((Finset.univ.filter fun b : Addr L => b = a ∨ T b ≠ none).card : ℚ) ≤
        ((dom T).card : ℚ) + 1 := by exact_mod_cast card_filter_insert_le T a
    have hpre := (mean_exists_prefix_le bytes bytes_injective (fun b : Addr L => b = a ∨ T b ≠ none)
      (fun b => b.toBytes.take 32)).trans (div_le_div_of_nonneg_right hfilt hcard.le)
    calc mean (fun f : State => indicator (badColl p Qtot a T f))
        ≤ mean (fun f : State => indicator (f = p.iv) + indicator (∃ b, T b = some f) +
            indicator (∃ b, (b = a ∨ T b ≠ none) ∧ b.toBytes.take 32 = bytes f)) := mean_mono h1
      _ = mean (fun f : State => indicator (f = p.iv)) +
            mean (fun f : State => indicator (∃ b, T b = some f)) +
            mean (fun f : State => indicator (∃ b, (b = a ∨ T b ≠ none) ∧ b.toBytes.take 32 = bytes f)) := by
          rw [mean_add, mean_add]
      _ ≤ 1 / (Fintype.card State : ℚ) + ((dom T).card : ℚ) / (Fintype.card State : ℚ) +
            (((dom T).card : ℚ) + 1) / (Fintype.card State : ℚ) := by
          rw [mean_indicator_eq]
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
