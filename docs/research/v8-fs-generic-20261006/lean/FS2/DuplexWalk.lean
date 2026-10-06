import FS2.DuplexTrace

/-! # The duplex transcript and the table walk

For the duplex protocol object, round `i` of the transcript absorbs at
`absC i` (state `sv i`, message `msg π i`), squeezes at `sqC i` and advances
at `adC i`; the challenge is `(σ_i (H (sqC i)), H (adC i))` and the next
state is `H (adC i)`.  `walk` recovers the round records from any
sub-table of a non-colliding execution that contains the earlier `advance`
and `absorb` cells. -/
set_option autoImplicit false
namespace FS2.Duplex

open FS FS2 AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8PairedCommitment AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section

variable {M Cv X W Pf : Type} {L : Nat}

section Transcript
variable (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
  (extract : X → Table (Addr L) State → Option W) (H : Addr L → State) (π : Pf)

local notation "pr" => protocol p x msg extract

/-- The duplex state before round `i`. -/
def sv (i : Nat) : State := stateOf p ((pr).transcript H x π i)

def absC (i : Nat) : Addr L := absorbA p (sv p x msg extract H π i) (p.lbl i) (p.enc (msg π i)) (p.encLen _)
/-- The absorbed state of round `i`. -/
def sv' (i : Nat) : State := H (absC p x msg extract H π i)
def sqC (i : Nat) : Addr L := squeezeA p (sv' p x msg extract H π i)
def adC (i : Nat) : Addr L := advanceA p (sv' p x msg extract H π i)

/-- The round records of the first `i` rounds. -/
def recs : Nat → List (Rec M)
  | 0 => []
  | i + 1 => recs i ++ [(sv p x msg extract H π i, sv' p x msg extract H π i, msg π i,
      H (adC p x msg extract H π i))]

theorem chain_eq (i : Nat) :
    (pr).chain H x π i = samp p i ((pr).transcript H x π i) (msg π i) := rfl

theorem firstCell_chain (i : Nat) : firstCell ((pr).chain H x π i) = some (absC p x msg extract H π i) := rfl

/-- The chain's own trace: absorb, squeeze, advance. -/
theorem chain_trace (i : Nat) :
    (eval H ((pr).chain H x π i).toProgram).1 =
      [(absC p x msg extract H π i, sv' p x msg extract H π i),
       (sqC p x msg extract H π i, H (sqC p x msg extract H π i)),
       (adC p x msg extract H π i, H (adC p x msg extract H π i))] := by
  rfl

theorem chal_eq (i : Nat) :
    (pr).chal H x π i = (p.σ i (H (sqC p x msg extract H π i)), H (adC p x msg extract H π i)) := by
  show (eval H (samp p i _ _).toProgram).2 = _
  simp only [samp, Sampler.toProgram, eval, multiProg, Function.update_self,
    Function.update_of_ne (squeezeA_ne_advanceA p _), Function.update_of_ne (Ne.symm (squeezeA_ne_advanceA p _))]
  rfl

theorem transcript_succ (i : Nat) :
    (pr).transcript H x π (i + 1) =
      ((pr).transcript H x π i).ext (msg π i) ((pr).chal H x π i) := rfl

theorem sv_zero : sv p x msg extract H π 0 = p.iv := rfl

theorem sv_succ (i : Nat) : sv p x msg extract H π (i + 1) = H (adC p x msg extract H π i) := by
  unfold sv
  rw [transcript_succ, stateOf]
  simp only [Prefix.ext, List.getLast?_append, List.getLast?_singleton, Option.some_or]
  rw [chal_eq]

/-- The transcript's rounds, as a range map. -/
theorem transcript_rounds (i : Nat) :
    ((pr).transcript H x π i).rounds = (List.range i).map fun j => (msg π j, (pr).chal H x π j) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [transcript_succ, Prefix.ext, List.range_succ, List.map_append, List.map_singleton]
      simp only [ih]

theorem recs_eq (i : Nat) :
    recs p x msg extract H π i = (List.range i).map fun j =>
      (sv p x msg extract H π j, sv' p x msg extract H π j, msg π j, H (adC p x msg extract H π j)) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [recs, List.range_succ, List.map_append, List.map_singleton, ih]

theorem parseAbsorb_absC (i : Nat) :
    parseAbsorb (absC p x msg extract H π i) =
      some (sv p x msg extract H π i, p.lbl i, p.enc (msg π i)) :=
  parseAbsorb_absorbA p _ _ _ _

theorem recs_length (i : Nat) : (recs p x msg extract H π i).length = i := by
  rw [recs_eq]; simp

theorem transcript_statement (i : Nat) : ((pr).transcript H x π i).statement = x := by
  induction i with
  | zero => rfl
  | succ i ih => rw [transcript_succ, Prefix.ext]; exact ih

/-- The completed rounds are the transcript's when every squeeze value read
by the completion is the oracle's. -/
theorem completeRounds_recs (T : Table (Addr L) State) (acc : Addr L → State) :
    ∀ i : Nat, (∀ j < i, (T (sqC p x msg extract H π j)).getD (acc (sqC p x msg extract H π j)) =
        H (sqC p x msg extract H π j)) →
      completeRounds p T acc 0 (recs p x msg extract H π i) = ((pr).transcript H x π i).rounds := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro h
      rw [recs, completeRounds_append, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), transcript_succ,
        Prefix.ext, recs_length, zero_add]
      simp only [chal_eq]
      have hi := h i (Nat.lt_succ_self i)
      unfold sqC at hi
      rw [hi]
      rfl

/-! ## The table walk -/

/-- Any sub-table of a non-colliding execution that contains the first `i`
rounds' `advance` and `absorb` cells walks back from `sv i` to the records. -/
theorem walk_eq (tr : List (Addr L × State)) (hcons : ∀ q ∈ tr, q.2 = H q.1) (Qtot : Nat)
    (hQ : firstReads emptyTable tr ≤ Qtot) (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (r : Nat)
    (hread : ∀ j < r, Read tr (absC p x msg extract H π j) ∧ Read tr (adC p x msg extract H π j)) :
    ∀ (i n : Nat), i ≤ r → i ≤ n → ∀ (T' : Table (Addr L) State),
      (∀ b v, T' b = some v → v = H b ∧ Read tr b) →
      (∀ j < i, T' (adC p x msg extract H π j) ≠ none ∧ T' (absC p x msg extract H π j) ≠ none) →
      walk p T' n (sv p x msg extract H π i) = some (recs p x msg extract H π i) := by
  intro i
  induction i with
  | zero =>
      intro n _ _ T' _ _
      cases n <;> simp [walk, sv_zero, recs]
  | succ i ih =>
      intro n hir hn T' hT' hcells
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hreadi := hread i (by omega)
      have hadRead := hreadi.2
      have hne : sv p x msg extract H π (i + 1) ≠ p.iv := by
        rw [sv_succ]
        exact (noColl p Qtot H tr hcons hQ hcoll _ hadRead).1
      have hadv : theUnique (advPre p T' (sv p x msg extract H π (i + 1))) =
          some (sv' p x msg extract H π i) := by
        apply theUnique_preimages
        intro s''
        constructor
        · intro h
          obtain ⟨hv, hr⟩ := hT' _ _ h
          rw [sv_succ] at hv
          by_contra hne'
          have hne'' : advanceA p s'' ≠ adC p x msg extract H π i := fun e =>
            hne' (advanceA_injective p e)
          exact noColl_injective p Qtot H tr hcons hQ hcoll _ _ hr hadRead hne'' hv.symm
        · rintro rfl
          obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hcells i (Nat.lt_succ_self i)).1
          rw [sv_succ]
          have := (hT' _ _ hv).1
          subst this
          exact hv
      have habs : theUnique (absCells T' (sv' p x msg extract H π i)) =
          some (absC p x msg extract H π i) := by
        apply theUnique_cellsWith
        intro a
        constructor
        · rintro ⟨h, _⟩
          obtain ⟨hv, hr⟩ := hT' _ _ h
          by_contra hne'
          exact noColl_injective p Qtot H tr hcons hQ hcoll _ _ hr hreadi.1 hne' hv.symm
        · rintro rfl
          obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hcells i (Nat.lt_succ_self i)).2
          have := (hT' _ _ hv).1
          subst this
          refine ⟨hv, ?_⟩
          rw [parseAbsorb_absC]; rfl
      have hih := ih n' (by omega) (by omega) T' hT' (fun j hj => hcells j (Nat.lt_succ_of_lt hj))
      simp only [walk, hne, if_false, hadv, habs, parseAbsorb_absC, p.decEnc, hih,
        Option.map_some, recs]
      rw [sv_succ]

end Transcript

end
end FS2.Duplex
