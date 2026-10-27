import R1Z.PV_L2_F3Words
import R1Z.SideChannelL1AttemptRecord

/-! Word-consumption/refill and partial tower prefixes for the cap-16 source
sampler. Candidate relabeling is an equivalence, not fresh resampling.
The remaining join is to the owned decoder's U32/byte carrier and its
witness-absorption translation, jointly with the actual L1 owner. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3Schedule
open R1Z.PV_L2_F3Words
attribute [local instance] Classical.propDecidable

/-- A scalar keeps its result, cursor and complete accept/reject sequence. -/
def scalar : Nat → (Nat → Candidate) → Nat → Option (Fin 2147483647) × Nat × List Bool
  | 0, _, cursor => (none,cursor,[])
  | n+1, words, cursor =>
    if hc : accepts (words cursor) then (some ⟨(words cursor).val,hc⟩,cursor+1,[true])
    else let tail := scalar n words (cursor+1)
         (tail.1,tail.2.1,false::tail.2.2)

theorem scalar_control (n : Nat) (words : Nat → Candidate) (cursor : Nat) :
    (scalar n words cursor).2.2 = PV_L2_F3Words.control n words cursor := by
  induction n generalizing cursor with
  | zero => rfl
  | succ n ih =>
    unfold scalar PV_L2_F3Words.control
    split_ifs with hc
    · simp only [decide_eq_true hc, if_true]
    · simp only [decide_eq_false hc, Bool.false_eq_true, if_false, ih]

/-- Successful values move by e; failed prefixes and cursors stay identical. -/
theorem scalar_permute (e : Fin 2147483647 ≃ Fin 2147483647)
    (n : Nat) (words : Nat → Candidate) (cursor : Nat) :
    scalar n (fun i => permute e (words i)) cursor =
      ((scalar n words cursor).1.map e, (scalar n words cursor).2) := by
  induction n generalizing cursor with
  | zero => rfl
  | succ n ih =>
    by_cases hc : accepts (words cursor)
    · have hc' := (accepts_permute e (words cursor)).mpr hc
      simp only [scalar, dif_pos hc, dif_pos hc', Option.map_some]
      change (words cursor).val < 2147483647 at hc
      congr 2
      apply Fin.ext
      simp only [permute, Equiv.trans_apply, cellEquiv, dif_pos hc,
        Equiv.optionCongr_apply, Option.map_some, Equiv.symm_mk, Equiv.coe_fn_mk]
    · have hc' : ¬ accepts (permute e (words cursor)) := by
        exact fun h => hc ((accepts_permute e (words cursor)).mp h)
      simp only [scalar, dif_neg hc, dif_neg hc', ih]

/-- Hash refills, cached-word offsets, and acceptance positions. Domain and
seed stay fixed on this ROM-answer permutation. Zero-based absolute cursor
is safe here; the source uses a wrapping u64 block counter. -/
def addresses (start : Nat) (history : List Bool) : List (Nat × Nat × Bool × Bool) :=
  history.zipIdx.map (fun p =>
    ((start+p.2)/8, 4*((start+p.2)%8), decide ((start+p.2)%8=0),p.1))

def tower : Nat → (Nat → Candidate) → Nat → Option (List (Fin 2147483647)) × Nat × List Bool
  | 0, _, cursor => (some [],cursor,[])
  | n+1, words, cursor =>
    let sample := scalar 16 words cursor
    match sample.1 with
    | none => (none,sample.2)
    | some value =>
      let rest := tower n words sample.2.1
      (rest.1.map (value::·),rest.2.1,sample.2.2 ++ rest.2.2)

theorem tower_permute (e : Fin 2147483647 ≃ Fin 2147483647)
    (n : Nat) (words : Nat → Candidate) (cursor : Nat) :
    tower n (fun i => permute e (words i)) cursor =
      ((tower n words cursor).1.map (List.map e), (tower n words cursor).2) := by
  induction n generalizing cursor with
  | zero => rfl
  | succ n ih =>
    simp only [tower,scalar_permute]
    cases hs : (scalar 16 words cursor).1 with
    | none => simp only [Option.map_none]
    | some value =>
      simp only [Option.map_some, ih]
      cases hr : (tower n words (scalar 16 words cursor).2.1).1 <;> rfl

theorem tower_refills (e : Fin 2147483647 ≃ Fin 2147483647)
    (words : Nat → Candidate) (cursor : Nat) :
    addresses cursor (tower 4 (fun i => permute e (words i)) cursor).2.2 =
      addresses cursor (tower 4 words cursor).2.2 := by rw [tower_permute]

#print axioms scalar_control
#print axioms scalar_permute
#print axioms tower_permute
#print axioms tower_refills
end R1Z.PV_L2_F3Schedule
