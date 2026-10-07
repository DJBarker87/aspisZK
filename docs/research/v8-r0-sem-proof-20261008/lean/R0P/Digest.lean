import R0P.Path
import R0P.EmptyRoots

/-! G2, pinned e4d68a70d3f6beb215c9f6dd418f4a2a3740c809.
T = crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs.
The literal eight-lane accumulator is preserved. The right-tweak helper is
specialized to its actual frozen-empty-root calls, with M31 arithmetic before
lifting. Public.recipient is tested for presence, not for Public.variant. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- T:682, low-bit intrinsic adapter for min(u64.trailing_ones(index),20).
Fuel bounds the number of observed low bits, independent of index magnitude. -/
def digestTrailingOnes : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, index => if (index &&& 1) = 0 then 0 else 1+digestTrailingOnes n (index >>> 1)

/-- T:682, only the first twenty low bits of the public u64 are observed. -/
def digestCarry (index : Nat) : Nat := digestTrailingOnes 20 index

theorem digest_trailing_ones_le (n index : Nat) : digestTrailingOnes n index ≤ n := by
  induction n generalizing index with
  | zero => simp only [digestTrailingOnes, le_refl]
  | succ n ih =>
    simp only [digestTrailingOnes]
    split_ifs
    · omega
    · have := ih (index >>> 1); omega

theorem digest_carry_le (index : Nat) : digestCarry index ≤ 20 := digest_trailing_ones_le 20 index

/-- T:615–691, call identities in the source's exact order. -/
inductive DigestKey where
  | anchor | nullifier | recipient | change | frontier (level : Fin 20) | nextRoot | carry
  deriving DecidableEq

/-- T:654, the literal shift/and append-bit branch. -/
abbrev digestBitZero (pub : Public K) (level : Fin 20) : Prop :=
  ((pub.nextPairIndex >>> level.val) &&& 1) = 0

/-- T:614–693, ordered calls including all twenty frontier levels. -/
def digestKeys (pub : Public K) : List DigestKey :=
  [.anchor, .nullifier] ++ (match pub.recipient with | none => [] | some _ => [.recipient]) ++
  [.change] ++ List.ofFn DigestKey.frontier ++ [.nextRoot] ++
  (if digestCarry pub.nextPairIndex < 20 then [.carry] else [])

/-- T:617,625,634,643,657,666,676,686, exact selector rows. -/
def digestRow (pub : Public K) : DigestKey → Fin 1024
  | .anchor => 56*16+11
  | .nullifier => 26*16+11
  | .recipient => 29*16+11
  | .change => 32*16+11
  | .frontier level => g2Row ⟨34+level.val, by omega⟩ (if digestBitZero pub level then 0 else 12)
  | .nextRoot => 53*16+11
  | .carry => g2Row ⟨33+digestCarry pub.nextPairIndex, by have := digest_carry_le pub.nextPairIndex; omega⟩ 11

/-- T:619,627,636,645,659,668,678,688, exact opened offsets. -/
def digestStart (pub : Public K) : DigestKey → Fin 9
  | .frontier level => if digestBitZero pub level then 8 else 0
  | _ => 0

/-- T:620,628,637,646,660–671,679,689: actual-call target specialization.
Only the frozen empty-root branch requests a right tweak. The source's M31
add and then lift is retained by emptyRootRightTarget. -/
def digestTarget (pub : Public K) : DigestKey → Digest K
  | .anchor => pub.anchor
  | .nullifier => pub.nullifier
  | .recipient => pub.recipient.getD (fun _ => 0)
  | .change => pub.change
  | .frontier level => if digestBitZero pub level then emptyRootRightTarget level else pub.snapshotFrontier level
  | .nextRoot => pub.nextRoot
  | .carry => if h : digestCarry pub.nextPairIndex < 20 then pub.nextFrontier ⟨digestCarry pub.nextPairIndex, h⟩ else fun _ => 0

/-- T:364–380, after the actual call's M31 target preprocessing. Each array
write is accumulator + selector * (opened[start+lane] - lifted target). -/
def digestAddBinding (acc : Digest K) (selector : K) (opened : Fin 16 → K)
    (start : Fin 9) (target : Digest K) : Digest K :=
  fun lane => acc lane + selector * (opened ⟨start.val+lane.val, by omega⟩ - target lane)

/-- T:609–694, literal ordered accumulator over the call list. -/
def publicDigestLanes (pub : Public K) (o : Openings K) (sel : Sel K) : Digest K :=
  (digestKeys pub).foldl (fun acc key => digestAddBinding acc (sel (digestRow pub key))
    o.z (digestStart pub key) (digestTarget pub key)) (fun _ => 0)

/-- T:609–694, production path before packed-digest-audit factoring. -/
def digestFamily : Family K where
  residuals := fun pub o sel => List.ofFn (publicDigestLanes pub o sel)

/-- T:364–380: address of the opened trace column for a call and lane. -/
def digestColumn (pub : Public K) (key : DigestKey) (lane : Fin 8) : Fin 29 :=
  ⟨(digestStart pub key).val+lane.val, by have := (digestStart pub key).isLt; omega⟩

/-- T:631 and 683: the two optional call guards; all other calls occur. -/
def digestEnabled (pub : Public K) : DigestKey → Prop
  | .recipient => ∃ recipient, pub.recipient = some recipient
  | .carry => digestCarry pub.nextPairIndex < 20
  | _ => True

theorem digest_key_mem (pub : Public K) (key : DigestKey) :
    key ∈ digestKeys pub ↔ digestEnabled pub key := by
  cases key <;> unfold digestKeys digestEnabled
  all_goals
    cases pub.recipient <;> dsimp only
    all_goals split_ifs <;> simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      List.mem_ofFn, or_false]
    all_goals aesop

theorem digest_keys_carry (pub : Public K) (key : DigestKey) (hk : key ∈ digestKeys pub)
    (he : key = .carry) : digestCarry pub.nextPairIndex < 20 := by
  subst key
  exact (digest_key_mem pub .carry).mp hk

omit [Field K] in
theorem digest_keys_nodup (pub : Public K) : (digestKeys pub).Nodup := by
  have hinj : Function.Injective DigestKey.frontier := by
    intro i j hij; cases hij; rfl
  unfold digestKeys
  cases pub.recipient <;> dsimp only
  all_goals
    split_ifs <;> simp only [List.nodup_append, List.nodup_cons, List.nodup_nil,
      List.mem_cons, List.not_mem_nil, not_false_eq_true, and_true, List.mem_ofFn,
      List.nodup_ofFn, List.mem_append]
    all_goals aesop

/-- Distinct source calls cannot cancel each other at a Boolean row. -/
theorem digest_rows_injective (pub : Public K) (x y : DigestKey)
    (hx : x ∈ digestKeys pub) (hy : y ∈ digestKeys pub)
    (he : digestRow pub x = digestRow pub y) : x = y := by
  have hcx : x = .carry → digestCarry pub.nextPairIndex < 20 := digest_keys_carry pub x hx
  have hcy : y = .carry → digestCarry pub.nextPairIndex < 20 := digest_keys_carry pub y hy
  have hv := congrArg Fin.val he
  cases x <;> cases y <;> simp only [digestRow, g2Row] at hv ⊢
  all_goals try simp_all only [true_implies]
  all_goals try norm_num at hv
  all_goals try omega
  all_goals try split_ifs at hv
  all_goals try simp_all only [Fin.val_zero]
  all_goals norm_num at hv
  all_goals first | (congr 1; apply Fin.ext; omega) | omega

theorem digest_rows_pairwise (pub : Public K) :
    (digestKeys pub).Pairwise (fun x y => digestRow pub x ≠ digestRow pub y) := by
  exact (digest_keys_nodup pub).imp_of_mem fun hx hy hne he =>
    hne (digest_rows_injective pub _ _ hx hy he)

theorem g2_row_sum_off {α : Type} (xs : List α) (row : α → Fin 1024)
    (f : α → Fin 1024 → K) (b : Fin 1024) (h : ∀ x ∈ xs, row x ≠ b) :
    (xs.map (fun x => rowSel b (row x)*f x b)).sum = 0 := by
  apply List.sum_eq_zero
  intro t ht
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
  rw [rowSel_ne b (row x) (h x hx), zero_mul]

theorem g2_row_sum_at {α : Type} (xs : List α) (row : α → Fin 1024)
    (f : α → Fin 1024 → K) (hp : xs.Pairwise (fun x y => row x ≠ row y))
    (x : α) (hx : x ∈ xs) :
    (xs.map (fun y => rowSel (row x) (row y)*f y (row x))).sum = f x (row x) := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at hx
  | cons y ys ih =>
    obtain ⟨hy, hys⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hx with hxy | hx
    · subst x
      simp only [List.map_cons, List.sum_cons, rowSel_self, one_mul]
      rw [g2_row_sum_off ys row f (row y) (fun z hz => Ne.symm (hy z hz)), add_zero]
    · simp only [List.map_cons, List.sum_cons]
      rw [rowSel_ne (row x) (row y) (hy x hx), zero_mul, zero_add, ih hys hx]

theorem g2_row_sum_iff {α : Type} (xs : List α) (row : α → Fin 1024)
    (f : α → Fin 1024 → K) (hp : xs.Pairwise (fun x y => row x ≠ row y)) :
    (∀ b, (xs.map (fun x => rowSel b (row x)*f x b)).sum = 0) ↔
      ∀ x ∈ xs, f x (row x) = 0 := by
  constructor
  · intro h x hx
    rw [← g2_row_sum_at xs row f hp x hx]
    exact h (row x)
  · intro h b
    apply List.sum_eq_zero
    intro t ht
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    by_cases hb : row x = b
    · subst b
      rw [h x hx, mul_zero]
    · rw [rowSel_ne b (row x) hb, zero_mul]

theorem digest_fold_eq (pub : Public K) (o : Openings K) (sel : Sel K)
    (xs : List DigestKey) (acc : Digest K) (lane : Fin 8) :
    (xs.foldl (fun acc key => digestAddBinding acc (sel (digestRow pub key))
      o.z (digestStart pub key) (digestTarget pub key)) acc) lane =
    acc lane + (xs.map (fun key => sel (digestRow pub key) *
      (o.z ⟨(digestStart pub key).val+lane.val, by have := (digestStart pub key).isLt; omega⟩-
        digestTarget pub key lane))).sum := by
  induction xs generalizing acc with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons key xs ih =>
    rw [List.foldl_cons, ih]
    simp only [digestAddBinding, List.map_cons, List.sum_cons, add_assoc]

theorem digest_holds_calls_iff (pub : Public K) (A : Trace K) :
    Holds digestFamily pub A ↔ ∀ key ∈ digestKeys pub, ∀ lane : Fin 8,
      A (digestColumn pub key lane) (digestRow pub key) = digestTarget pub key lane := by
  change (∀ b, ∀ r ∈ List.ofFn (publicDigestLanes pub (rowOpenings A b) (rowSel b)), r = 0) ↔ _
  simp only [List.forall_mem_ofFn_iff, publicDigestLanes, digest_fold_eq, zero_add]
  rw [forall_comm]
  constructor
  · intro h key hk lane
    have hh := (g2_row_sum_iff (digestKeys pub) (digestRow pub)
      (fun key b => A (digestColumn pub key lane) b - digestTarget pub key lane)
      (digest_rows_pairwise pub)).mp (h lane) key hk
    exact sub_eq_zero.mp hh
  · intro h lane
    apply (g2_row_sum_iff (digestKeys pub) (digestRow pub)
      (fun key b => A (digestColumn pub key lane) b - digestTarget pub key lane)
      (digest_rows_pairwise pub)).mpr
    intro key hk
    exact sub_eq_zero.mpr (h key hk lane)

/-- Complete public binding equations. Recipient is conditional on Option
presence (as in T:631), rather than on the variant field. For zero append
bits the last empty-root limb includes the reduced M31 right tweak. -/
theorem digest_holds_iff (pub : Public K) (A : Trace K) :
    Holds digestFamily pub A ↔
      (∀ i : Fin 8, A (i.castAdd 21) 907 = pub.anchor i) ∧
      (∀ i : Fin 8, A (i.castAdd 21) 427 = pub.nullifier i) ∧
      (∀ recipient, pub.recipient = some recipient → ∀ i : Fin 8, A (i.castAdd 21) 475 = recipient i) ∧
      (∀ i : Fin 8, A (i.castAdd 21) 523 = pub.change i) ∧
      (∀ level : Fin 20,
        (digestBitZero pub level → ∀ i : Fin 8,
          A ⟨8+i.val, by omega⟩ (g2Row ⟨34+level.val, by omega⟩ 0) = emptyRootRightTarget level i) ∧
        (¬ digestBitZero pub level → ∀ i : Fin 8,
          A (i.castAdd 21) (g2Row ⟨34+level.val, by omega⟩ 12) = pub.snapshotFrontier level i)) ∧
      (∀ i : Fin 8, A (i.castAdd 21) 859 = pub.nextRoot i) ∧
      (∀ hc : digestCarry pub.nextPairIndex < 20, ∀ i : Fin 8,
        A (i.castAdd 21) (g2Row ⟨33+digestCarry pub.nextPairIndex, by omega⟩ 11) =
          pub.nextFrontier ⟨digestCarry pub.nextPairIndex, hc⟩ i) := by
  rw [digest_holds_calls_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hh := h .anchor ((digest_key_mem pub .anchor).mpr trivial)
      simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget] using hh
    · have hh := h .nullifier ((digest_key_mem pub .nullifier).mpr trivial)
      simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget] using hh
    · intro recipient hr
      have hh := h .recipient ((digest_key_mem pub .recipient).mpr ⟨recipient, hr⟩)
      simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget, hr, Option.getD_some] using hh
    · have hh := h .change ((digest_key_mem pub .change).mpr trivial)
      simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget] using hh
    · intro level
      have hh := h (.frontier level) ((digest_key_mem pub (.frontier level)).mpr trivial)
      constructor
      · intro hb
        simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget, if_pos hb] using hh
      · intro hb
        simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget, if_neg hb] using hh
    · have hh := h .nextRoot ((digest_key_mem pub .nextRoot).mpr trivial)
      simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget] using hh
    · intro hc
      have hh := h .carry ((digest_key_mem pub .carry).mpr hc)
      simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget, dif_pos hc] using hh
  · rintro ⟨ha, hn, hr, hc, hf, hroot, hcarry⟩ key hk
    have he := (digest_key_mem pub key).mp hk
    cases key with
    | anchor => simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget] using ha
    | nullifier => simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget] using hn
    | recipient =>
      obtain ⟨recipient, he⟩ := he
      simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget, he, Option.getD_some] using hr recipient he
    | change => simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget] using hc
    | frontier level =>
      by_cases hb : digestBitZero pub level
      · simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget, if_pos hb] using (hf level).1 hb
      · simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget, if_neg hb] using (hf level).2 hb
    | nextRoot => simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget] using hroot
    | carry =>
      change digestCarry pub.nextPairIndex < 20 at he
      simpa [Fin.castAdd, Fin.castLE, Nat.zero_add, digestColumn, digestStart, digestRow, digestTarget, dif_pos he] using hcarry he

#print axioms digest_trailing_ones_le
#print axioms digest_carry_le
#print axioms digest_key_mem
#print axioms digest_keys_carry
#print axioms digest_keys_nodup
#print axioms digest_rows_injective
#print axioms digest_rows_pairwise
#print axioms g2_row_sum_off
#print axioms g2_row_sum_at
#print axioms g2_row_sum_iff
#print axioms digest_fold_eq
#print axioms digest_holds_calls_iff
#print axioms digest_holds_iff
end R0P
