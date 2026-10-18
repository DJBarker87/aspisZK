import R0Z.K4Values

/-! J2b (LOG D35): `TerminalClosed` from `SemK4 ∧ PublicBase`.

The R0P terminal `terminalValue pub λ χ θ μ zc B y α` reads only its
arguments: the public statement `pub`, the four challenges, `zc`, the packing
basis `B`, the claims `y` and the point `α` (its type takes no trace and no
other state).  Every constraint family it evaluates (Poseidon packed,
schedule, occupancy, path, value, digest, asset, copy) is built from these
by ring operations, inverses-free products, numerals, finite folds and
branches on public/static data.  Hence, for any subfield `S` containing `F`,
`B.i`, `B.u` and all those inputs, the terminal lies in `S`
(`terminalValue_mem`).  Specialised to `S = K₄` this is `terminalClosed`.

Proof style follows R0P/LaneMap's Boolean-row closure lemmas, generalised to
arbitrary openings and selector vectors with entries in `S`.  No table is
evaluated: numerals are discharged by `natCast_mem`, vectors by `Fin.cases`. -/

set_option autoImplicit false

noncomputable section

namespace R0Z.TerminalClosed

open scoped BigOperators
open R0P R0P.SemSource

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] (S : Subfield K)

/-! ## Generic tools -/

theorem foldl_mem {α : Type} (f : K → α → K) (l : List α) (init : K) (hinit : init ∈ S)
    (hf : ∀ acc, acc ∈ S → ∀ x ∈ l, f acc x ∈ S) : l.foldl f init ∈ S := by
  induction l generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact ih _ (hf init hinit x (List.mem_cons_self ..))
      (fun acc hacc y hy => hf acc hacc y (List.mem_cons_of_mem _ hy))

theorem getD_mem (l : List K) (h : ∀ x ∈ l, x ∈ S) (i : ℕ) : l.getD i 0 ∈ S := by
  induction l generalizing i with
  | nil => simpa using S.zero_mem
  | cons x xs ih =>
    cases i with
    | zero => simpa using h x (List.mem_cons_self ..)
    | succ i =>
      simpa using ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) i

theorem vec_cons_mem {n : Nat} (head : K) (tail : Fin n → K) (hh : head ∈ S)
    (ht : ∀ i, tail i ∈ S) : ∀ i, Matrix.vecCons head tail i ∈ S := by
  intro i; exact Fin.cases hh ht i

theorem vec_cons_fun {α : Type} {n : Nat} (P : α → Prop)
    (head : α) (tail : Fin n → α) (hh : P head) (ht : ∀ i, P (tail i)) :
    ∀ i, P (Matrix.vecCons head tail i) := by
  intro i; exact Fin.cases hh ht i

theorem vec_nil_fun {α : Type} (P : α → Prop) : ∀ i, P (Matrix.vecEmpty (α := α) i) := by
  intro i; exact Fin.elim0 i

/-! ## Selector adapters -/

section Sel

variable {S} (sel : Sel K) (hsel : ∀ k, sel k ∈ S)
include hsel

theorem g2High_mem (h : Fin 64) : g2High sel h ∈ S :=
  sum_mem fun l _ => hsel _

theorem g2Low_mem (l : Fin 16) : g2Low sel l ∈ S :=
  sum_mem fun h _ => hsel _

theorem g2SumHigh_mem (start count : Nat) (bound : start + count ≤ 64) :
    g2SumHigh sel start count bound ∈ S := by
  unfold g2SumHigh
  refine foldl_mem S _ _ _ S.zero_mem (fun acc hacc x hx => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact S.add_mem hacc (g2High_mem sel hsel _)

theorem scheduleNodes_mem : scheduleNodes sel ∈ S := by
  unfold scheduleNodes
  refine foldl_mem S _ _ _ S.zero_mem (fun acc hacc x hx => S.add_mem hacc ?_)
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact g2High_mem sel hsel _
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact g2High_mem sel hsel _

end Sel

/- The selector adapters and the copy registries are never unfolded by
definitional checks below. -/
attribute [local irreducible] g2High g2Low g2SumHigh scheduleNodes copyLinks copyPatterns
  copyActiveRowMasks copyLinksBeforePositivity copyLinksAfterPositivity

/- The closure tactic on goals `x ∈ S` (after unfolding): hypotheses of the
fixed names `hz hs hx hsel hhigh hlow`, ring operations, finite sums and
products, branches, and finally numerals.  No hypothesis is applied with an
unconstrained conclusion. -/
set_option hygiene false in
macro "sclose" : tactic => `(tactic| repeat' first
  | assumption
  | exact hhigh _
  | exact hlow _
  | exact hz _
  | exact hs _
  | exact hx _
  | exact hsel _
  | exact zero_mem _
  | exact one_mem _
  | constructor
  | (intro _)
  | apply add_mem
  | apply sub_mem
  | apply mul_mem
  | apply neg_mem
  | apply pow_mem
  | (apply sum_mem; intro _ _)
  | (apply prod_mem; intro _ _)
  | split_ifs
  | split
  | exact natCast_mem _ _)

/- A narrower closure for the schedule arithmetic (no list, branch or
big-operator alternatives). -/
set_option hygiene false in
macro "rclose" : tactic => `(tactic| repeat' first
  | assumption
  | exact hhigh _
  | exact hlow _
  | exact hz _
  | exact hsel _
  | exact zero_mem _
  | exact one_mem _
  | exact natCast_mem _ _
  | apply add_mem
  | apply sub_mem
  | apply mul_mem)

/-! ## Families at arbitrary openings and selectors -/

section Families

variable {S} (pub : Public K) (o : Openings K) (sel : Sel K)

theorem scheduleInitial_mem_pt (hz : ∀ i, o.z i ∈ S) (hsel : ∀ k, sel k ∈ S)
    (lane : Fin 16) : scheduleInitial .privateTransfer o sel lane ∈ S := by
  have hhigh := g2High_mem sel hsel
  have hlow := g2Low_mem sel hsel
  have hnodes := scheduleNodes_mem sel hsel
  unfold scheduleInitial scheduleVariantSelectors
  try dsimp only
  split_ifs <;> rclose

theorem scheduleInitial_mem_wd (hz : ∀ i, o.z i ∈ S) (hsel : ∀ k, sel k ∈ S)
    (lane : Fin 16) : scheduleInitial .withdrawal o sel lane ∈ S := by
  have hhigh := g2High_mem sel hsel
  have hlow := g2Low_mem sel hsel
  have hnodes := scheduleNodes_mem sel hsel
  unfold scheduleInitial scheduleVariantSelectors
  try dsimp only
  split_ifs <;> rclose

theorem scheduleInitial_mem (v : Variant) (hz : ∀ i, o.z i ∈ S) (hsel : ∀ k, sel k ∈ S)
    (lane : Fin 16) : scheduleInitial v o sel lane ∈ S := by
  cases v
  · exact scheduleInitial_mem_pt o sel hz hsel lane
  · exact scheduleInitial_mem_wd o sel hz hsel lane

theorem scheduleAbsorption_mem (v : Variant) (hz : ∀ i, o.z i ∈ S) (hsel : ∀ k, sel k ∈ S)
    (lane : Fin 16) : scheduleAbsorption v o sel lane ∈ S := by
  have hhigh := g2High_mem sel hsel
  have hlow := g2Low_mem sel hsel
  have hnodes := scheduleNodes_mem sel hsel
  cases v <;>
    (unfold scheduleAbsorption scheduleAbsorptionLiteral scheduleVariantSelectors; try dsimp only) <;>
    sclose

theorem schedule_mem (hz : ∀ i, o.z i ∈ S) (hsel : ∀ k, sel k ∈ S) :
    ∀ r ∈ scheduleFamily.residuals pub o sel, r ∈ S := by
  simp only [scheduleFamily, List.forall_mem_append, List.forall_mem_ofFn_iff]
  exact ⟨scheduleInitial_mem o sel _ hz hsel, scheduleAbsorption_mem o sel _ hz hsel⟩

theorem occupancy_mem (hz : ∀ i, o.z i ∈ S) (hsel : ∀ k, sel k ∈ S) :
    ∀ r ∈ occupancyFamily.residuals pub o sel, r ∈ S := by
  have he : occupancyExpected (K := K) pub.variant ∈ S := by
    cases pub.variant
    · exact S.one_mem
    · exact S.zero_mem
  simp only [occupancyFamily, occupancyLanesLiteral, List.forall_mem_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, List.forall_mem_ofFn_iff]
  sclose

theorem path_mem (hz : ∀ i, o.z i ∈ S) (hs : ∀ i, o.succ i ∈ S) (hsel : ∀ k, sel k ∈ S) :
    ∀ r ∈ pathFamily.residuals pub o sel, r ∈ S := by
  have hq : pathSelector sel ∈ S := by
    unfold pathSelector
    exact S.mul_mem (g2SumHigh_mem sel hsel _ _ _)
      (S.add_mem (S.add_mem (S.add_mem (g2Low_mem sel hsel _) (g2Low_mem sel hsel _))
        (g2Low_mem sel hsel _)) (g2Low_mem sel hsel _))
  simp only [pathFamily, pathLanes, List.forall_mem_append, List.forall_mem_cons,
    List.not_mem_nil, false_implies, implies_true, and_true, List.forall_mem_ofFn_iff]
  sclose

theorem value_mem (hz : ∀ i, o.z i ∈ S) (hs : ∀ i, o.succ i ∈ S) (hx : ∀ i, o.xor12 i ∈ S)
    (hsel : ∀ k, sel k ∈ S) : ∀ r ∈ valueFamily.residuals pub o sel, r ∈ S := by
  have hrz : valueReconstruct10 o.z ∈ S := by
    rw [value_reconstruct10_eq]; sclose
  have hrs : valueReconstruct10 o.succ ∈ S := by
    rw [value_reconstruct10_eq]; sclose
  have hrx : valueReconstruct10 o.xor12 ∈ S := by
    rw [value_reconstruct10_eq]; sclose
  have hrange : ∀ r ∈ valueRange o, r ∈ S := by
    simp only [valueRange, List.forall_mem_append, List.forall_mem_ofFn_iff,
      List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    sclose
  simp only [valueFamily, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, false_implies, implies_true, and_true]
  constructor
  · intro r hr
    refine S.mul_mem ?_ (hrange r hr)
    clear hrange
    sclose
  · clear hrange
    sclose

theorem emptyRoot_mem (level : Fin 20) (i : Fin 8) : emptyRootRightTarget (K := K) level i ∈ S := by
  unfold emptyRootRightTarget
  split_ifs <;> exact natCast_mem S _

theorem digestTarget_mem {F : Subfield K} (hFS : ∀ x ∈ F, x ∈ S) (hpub : PublicBase F pub)
    (key : DigestKey) (i : Fin 8) : digestTarget pub key i ∈ S := by
  obtain ⟨ha, hn, _, hr, hc, _, hsf, hroot, hnext⟩ := hpub
  cases key with
  | anchor => exact hFS _ (ha i)
  | nullifier => exact hFS _ (hn i)
  | recipient =>
      cases he : pub.recipient with
      | none => simp only [digestTarget, he, Option.getD_none]; exact S.zero_mem
      | some r =>
          simp only [digestTarget, he, Option.getD_some]
          exact hFS _ (hr r he i)
  | change => exact hFS _ (hc i)
  | frontier level =>
      simp only [digestTarget]
      split_ifs
      · exact emptyRoot_mem level i
      · exact hFS _ (hsf level i)
  | nextRoot => exact hFS _ (hroot i)
  | carry =>
      simp only [digestTarget]
      split_ifs
      · exact hFS _ (hnext _ i)
      · exact S.zero_mem

theorem digest_mem (hz : ∀ i, o.z i ∈ S) (hsel : ∀ k, sel k ∈ S) {F : Subfield K} (hFS : ∀ x ∈ F, x ∈ S) (hpub : PublicBase F pub) :
    ∀ r ∈ digestFamily.residuals pub o sel, r ∈ S := by
  simp only [digestFamily, List.forall_mem_ofFn_iff]
  intro i
  unfold publicDigestLanes
  rw [digest_fold_eq]
  apply S.add_mem S.zero_mem
  apply list_sum_mem
  intro x hx
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp hx
  exact S.mul_mem (hsel _) (S.sub_mem (hz _) (digestTarget_mem pub hFS hpub key i))

theorem asset_mem (hz : ∀ i, o.z i ∈ S) (hsel : ∀ k, sel k ∈ S) {F : Subfield K} (hFS : ∀ x ∈ F, x ∈ S) (hpub : PublicBase F pub) :
    ∀ r ∈ assetFamily.residuals pub o sel, r ∈ S := by
  have hasset : pub.assetId ∈ S := hFS _ hpub.2.2.1
  have hamount : pub.withdrawalAmount.getD 0 ∈ S := by
    cases he : pub.withdrawalAmount with
    | none => simp only [Option.getD_none]; exact S.zero_mem
    | some a =>
        simp only [Option.getD_some]
        exact hFS _ (hpub.2.2.2.2.2.1 a he)
  cases hv : pub.variant <;> cases hw : pub.withdrawalAmount.isSome
  all_goals
    simp only [assetFamily, assetScalarLanes, hv, hw, Bool.false_eq_true,
      ite_false, ite_true, List.forall_mem_cons, List.not_mem_nil,
      false_implies, implies_true, and_true]
    sclose

end Families

/-! ## Poseidon -/

section Poseidon

variable {S}

theorem poseidon_initial_mem : ∀ r lane, poseidonExternalInitial (K := K) r lane ∈ S := by
  unfold poseidonExternalInitial
  repeat' first
    | apply vec_cons_fun (fun row : Fin 16 → K => ∀ lane, row lane ∈ S)
    | apply vec_nil_fun (fun row : Fin 16 → K => ∀ lane, row lane ∈ S)
    | apply vec_cons_mem
    | apply vec_nil_fun
    | exact natCast_mem S _

theorem poseidon_final_mem : ∀ r lane, poseidonExternalFinal (K := K) r lane ∈ S := by
  unfold poseidonExternalFinal
  repeat' first
    | apply vec_cons_fun (fun row : Fin 16 → K => ∀ lane, row lane ∈ S)
    | apply vec_nil_fun (fun row : Fin 16 → K => ∀ lane, row lane ∈ S)
    | apply vec_cons_mem
    | apply vec_nil_fun
    | exact natCast_mem S _

theorem poseidon_internal_constants_mem : ∀ r, poseidonInternalConstants (K := K) r ∈ S := by
  unfold poseidonInternalConstants
  repeat' first
    | apply vec_cons_mem
    | apply vec_nil_fun
    | exact natCast_mem S _

theorem poseidon_pow5_mem (x : K) (hx : x ∈ S) : poseidonPow5 x ∈ S := by
  unfold poseidonPow5
  exact S.mul_mem (S.mul_mem (S.mul_mem hx hx) (S.mul_mem hx hx)) hx

theorem poseidon_mat4_mem (v : Fin 4 → K) (hv : ∀ i, v i ∈ S) : ∀ i, poseidonMat4 v i ∈ S := by
  unfold poseidonMat4
  repeat' first
    | apply vec_cons_mem
    | apply vec_nil_fun
    | apply S.add_mem
    | exact hv _

theorem poseidon_external_mem (v : Fin 16 → K) (hv : ∀ i, v i ∈ S) :
    ∀ i, poseidonExternalLinear v i ∈ S := by
  intro i
  unfold poseidonExternalLinear
  repeat' first
    | apply S.add_mem
    | exact S.zero_mem
    | apply poseidon_mat4_mem
    | intro j
    | exact hv _

theorem poseidon_internal_mem (v : Fin 16 → K) (hv : ∀ i, v i ∈ S) :
    ∀ i, poseidonInternalLinear v i ∈ S := by
  have hsum : (List.ofFn (fun i : Fin 15 => v i.succ)).foldl (· + ·) 0 ∈ S := by
    refine foldl_mem S _ _ _ S.zero_mem (fun acc hacc x hx => S.add_mem hacc ?_)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hv i.succ
  intro i
  unfold poseidonInternalLinear
  split_ifs
  · exact S.sub_mem hsum (hv 0)
  · exact S.add_mem (S.add_mem hsum (hv 0)) (S.mul_mem (hv i) (natCast_mem S _))

theorem poseidon_full_round_mem (v c : Fin 16 → K) (hv : ∀ i, v i ∈ S) (hc : ∀ i, c i ∈ S) :
    ∀ i, poseidonFullRound v c i ∈ S := by
  unfold poseidonFullRound
  apply poseidon_external_mem
  intro i
  exact poseidon_pow5_mem _ (S.add_mem (hv i) (hc i))

theorem poseidon_internal_round_mem (v : Fin 16 → K) (c : K) (hv : ∀ i, v i ∈ S) (hc : c ∈ S) :
    ∀ i, poseidonInternalRound v c i ∈ S := by
  unfold poseidonInternalRound
  apply poseidon_internal_mem
  intro i
  split_ifs
  · exact poseidon_pow5_mem _ (S.add_mem (hv 0) hc)
  · exact hv i

theorem poseidon_leading_mem (v a : Fin 16 → K) (hv : ∀ i, v i ∈ S) (ha : ∀ i, a i ∈ S) :
    ∀ i, poseidonLeadingPair v a i ∈ S := by
  unfold poseidonLeadingPair
  try dsimp only
  apply poseidon_full_round_mem
  · apply poseidon_full_round_mem
    · apply poseidon_external_mem
      intro i; split_ifs
      · exact S.add_mem (hv i) (ha i)
      · exact hv i
    · exact poseidon_initial_mem 0
  · exact poseidon_initial_mem 1

theorem poseidon_scalarResidual_mem (o : Openings K) (block : K) (low : Fin 16 → K)
    (hz : ∀ i, o.z i ∈ S) (hs : ∀ i, o.succ i ∈ S) (hx : ∀ i, o.xor12 i ∈ S)
    (hblock : block ∈ S) (hlow : ∀ i, low i ∈ S) (lane : Fin 16) :
    poseidonScalarResidual o block low lane ∈ S := by
  have hfull : ∀ i, poseidonInterpolatedFullPair o.z low i ∈ S := by
    unfold poseidonInterpolatedFullPair
    try dsimp only
    apply poseidon_full_round_mem
    · apply poseidon_full_round_mem _ _ hz
      intro i
      exact S.add_mem (S.add_mem (S.mul_mem (hlow _) (poseidon_initial_mem _ _))
        (S.mul_mem (hlow _) (poseidon_final_mem _ _))) (S.mul_mem (hlow _) (poseidon_final_mem _ _))
    · intro i
      exact S.add_mem (S.add_mem (S.mul_mem (hlow _) (poseidon_initial_mem _ _))
        (S.mul_mem (hlow _) (poseidon_final_mem _ _))) (S.mul_mem (hlow _) (poseidon_final_mem _ _))
  have hfoldc : ∀ (f : Fin 7 → K), (∀ i, f i ∈ S) → (List.ofFn f).foldl (· + ·) 0 ∈ S := by
    intro f hf
    refine foldl_mem S _ _ _ S.zero_mem (fun acc hacc x hx => S.add_mem hacc ?_)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hf i
  have hinternal : ∀ i, poseidonInterpolatedInternalPair o.z low i ∈ S := by
    unfold poseidonInterpolatedInternalPair
    try dsimp only
    apply poseidon_internal_round_mem
    · apply poseidon_internal_round_mem _ _ hz
      exact hfoldc _ (fun i => S.mul_mem (hlow _) (poseidon_internal_constants_mem _))
    · exact hfoldc _ (fun i => S.mul_mem (hlow _) (poseidon_internal_constants_mem _))
  have hleading := poseidon_leading_mem o.z o.xor12 hz hx
  have hfullLow : ([1, 9, 10] : List (Fin 16)).foldl (fun sum row => sum + low row) 0 ∈ S :=
    foldl_mem S _ _ _ S.zero_mem (fun acc hacc x _ => S.add_mem hacc (hlow x))
  have hinternalLow : (List.ofFn (fun i : Fin 7 => low ⟨i.val + 2, by omega⟩)).foldl (· + ·) 0 ∈ S :=
    hfoldc _ (fun i => hlow _)
  unfold poseidonScalarResidual
  try dsimp only
  exact S.mul_mem hblock (S.add_mem (S.add_mem (S.add_mem S.zero_mem
    (S.mul_mem (hlow 0) (S.sub_mem (hs lane) (hleading lane))))
    (S.mul_mem hfullLow (S.sub_mem (hs lane) (hfull lane))))
    (S.mul_mem hinternalLow (S.sub_mem (hs lane) (hinternal lane))))

theorem pack4_mem {F : Subfield K} (B : PackBasis F) (hi : B.i ∈ S) (hu : B.u ∈ S)
    (v : Fin 4 → K) (hv : ∀ j, v j ∈ S) : pack4 B v ∈ S := by
  unfold pack4
  exact S.add_mem (S.add_mem (S.add_mem (hv 0) (S.mul_mem hi (hv 1))) (S.mul_mem hu (hv 2)))
    (S.mul_mem (S.mul_mem hi hu) (hv 3))

theorem poseidonPacked_mem {F : Subfield K} (B : PackBasis F) (hi : B.i ∈ S) (hu : B.u ∈ S)
    (pub : Public K) (o : Openings K) (sel : Sel K)
    (hz : ∀ i, o.z i ∈ S) (hs : ∀ i, o.succ i ∈ S) (hx : ∀ i, o.xor12 i ∈ S)
    (hsel : ∀ k, sel k ∈ S) : ∀ r ∈ (poseidonPackedFamily B).residuals pub o sel, r ∈ S := by
  simp only [poseidonPackedFamily, List.forall_mem_ofFn_iff]
  intro group
  exact pack4_mem B hi hu _ (fun j => poseidon_scalarResidual_mem o _ _ hz hs hx
    (g2SumHigh_mem sel hsel _ _ _) (g2Low_mem sel hsel) _)

end Poseidon

/-! ## Copy -/

section Copy

variable {S}

theorem copySelectorRow_mem (s : CopySelectors K) (hh : ∀ i, s.high i ∈ S)
    (hl : ∀ i, s.low i ∈ S) (r : Fin 1024) : copySelectorRow s r ∈ S :=
  S.mul_mem (hh _) (hl _)

theorem copyMaskSum_mem (values : Fin 16 → K) (hv : ∀ i, values i ∈ S) (mask : Nat) :
    copySelectorMaskSum16 values mask ∈ S := by
  unfold copySelectorMaskSum16
  try dsimp only
  refine foldl_mem S _ _ _ ?_ (fun acc hacc x _ => ?_)
  · split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · try dsimp only
    split_ifs
    · exact S.sub_mem hacc (hv x)
    · exact S.add_mem hacc (hv x)

theorem copyActive_mem (s : CopySelectors K) (hh : ∀ i, s.high i ∈ S)
    (hl : ∀ i, s.low i ∈ S) : copyActiveLiteral s ∈ S := by
  unfold copyActiveLiteral
  refine foldl_mem S _ _ _ S.zero_mem (fun acc hacc x _ => ?_)
  try dsimp only
  split_ifs
  · exact S.add_mem hacc (S.mul_mem (hh x) (copyMaskSum_mem _ hl _))
  · exact hacc

theorem copyPowers_mem (lam : K) (hlam : lam ∈ S) (i : Fin 16) : copyPowers lam i ∈ S := by
  unfold copyPowers
  exact foldl_mem S _ _ _ hlam (fun acc hacc _ _ => S.mul_mem hacc hlam)

theorem copyPatternValues_mem (openings : Fin 16 → K) (ho : ∀ i, openings i ∈ S)
    (lam : K) (hlam : lam ∈ S) (p : Fin 14) : copyPatternValuesLiteral openings lam p ∈ S := by
  unfold copyPatternValuesLiteral
  try dsimp only
  refine foldl_mem S _ _ _ S.zero_mem (fun acc hacc x _ => ?_)
  try dsimp only
  split_ifs
  · exact S.add_mem hacc (S.mul_mem (copyPowers_mem lam hlam x)
      (S.add_mem (ho _) (natCast_mem S _)))
  · exact hacc

/-- Every field of a copy row extension in `S`. -/
def RowIn (row : CopyRowExtension K) : Prop :=
  (∀ s, row.producerValues s ∈ S) ∧ (∀ s, row.producerWeights s ∈ S) ∧
    (∀ s, row.consumerValues s ∈ S) ∧ (∀ s, row.consumerWeights s ∈ S)

theorem update_mem (f : Fin 2 → K) (hf : ∀ s, f s ∈ S) (slot : Fin 2) (x : K) (hx : x ∈ S) :
    ∀ s, Function.update f slot x s ∈ S := by
  intro s
  rw [Function.update_apply]
  split_ifs
  · exact hx
  · exact hf s

theorem copyAccumulate_mem (values weights : Fin 2 → K) (hv : ∀ s, values s ∈ S)
    (hw : ∀ s, weights s ∈ S) (ep : CopyEndpoint) (tag : Nat) (weight : K) (hwt : weight ∈ S)
    (patterns : Fin 14 → K) (hp : ∀ i, patterns i ∈ S) (sels : CopySelectors K)
    (hh : ∀ i, sels.high i ∈ S) (hl : ∀ i, sels.low i ∈ S) :
    (∀ s, (copyAccumulateEndpoint values weights ep tag weight patterns sels).1 s ∈ S) ∧
      (∀ s, (copyAccumulateEndpoint values weights ep tag weight patterns sels).2 s ∈ S) := by
  unfold copyAccumulateEndpoint
  try dsimp only
  have hsr := copySelectorRow_mem sels hh hl ep.row
  exact ⟨update_mem _ hv _ _ (S.add_mem (hv _) (S.mul_mem hsr
      (S.add_mem (natCast_mem S _) (hp _)))),
    update_mem _ hw _ _ (S.add_mem (hw _) (S.mul_mem hsr hwt))⟩

theorem copyResidual_mem (row : CopyRowExtension K) (hrow : RowIn (S := S) row)
    (helper chi : K) (hh : helper ∈ S) (hc : chi ∈ S) : copyResidual row helper chi ∈ S := by
  obtain ⟨r1, r2, r3, r4⟩ := hrow
  have d : ∀ i, (![chi - row.producerValues 0, chi - row.producerValues 1,
      chi - row.consumerValues 0, chi - row.consumerValues 1] : Fin 4 → K) i ∈ S := by
    repeat' first
      | apply vec_cons_mem
      | apply vec_nil_fun
      | exact S.sub_mem hc (r1 _)
      | exact S.sub_mem hc (r3 _)
  unfold copyResidual
  exact S.sub_mem (S.mul_mem (S.mul_mem (d 0) (d 1))
      (S.add_mem (S.mul_mem hh (S.mul_mem (d 2) (d 3)))
        (S.add_mem (S.mul_mem (r4 0) (d 3)) (S.mul_mem (r4 1) (d 2)))))
    (S.mul_mem (S.mul_mem (d 2) (d 3))
      (S.add_mem (S.mul_mem (r2 0) (d 1)) (S.mul_mem (r2 1) (d 0))))

theorem copyEvaluate_mem (openings : Fin 16 → K) (ho : ∀ i, openings i ∈ S) (h1 : K)
    (hh1 : h1 ∈ S) (sels : CopySelectors K) (hh : ∀ i, sels.high i ∈ S)
    (hl : ∀ i, sels.low i ∈ S) (lam chi : K) (hlam : lam ∈ S) (hchi : chi ∈ S)
    (n : Nat) (v : Variant) :
    (copyEvaluateWithSelectors openings h1 sels lam chi n v).1 ∈ S := by
  unfold copyEvaluateWithSelectors
  try dsimp only
  have hp := copyPatternValues_mem openings ho lam hlam
  have hrow : ∀ (l : List CopyLink) (init : CopyRowExtension K), RowIn (S := S) init →
      RowIn (S := S) (l.foldl (fun row link =>
        let weight := copyLinkWeight link n v
        let producer := copyAccumulateEndpoint row.producerValues row.producerWeights
          link.producer link.tag weight (copyPatternValuesLiteral openings lam) sels
        let consumer := copyAccumulateEndpoint row.consumerValues row.consumerWeights
          link.consumer link.tag weight (copyPatternValuesLiteral openings lam) sels
        (⟨producer.1, producer.2, consumer.1, consumer.2⟩ : CopyRowExtension K)) init) := by
    intro l
    induction l with
    | nil => intro init h; exact h
    | cons link xs ih =>
      intro init h
      rw [List.foldl_cons]
      apply ih
      obtain ⟨h1', h2', h3', h4'⟩ := h
      have hwt := R0Z.K4Values.copyLinkWeight_mem S link n v
      have hP := copyAccumulate_mem _ _ h1' h2' link.producer link.tag _ hwt _ hp sels hh hl
      have hC := copyAccumulate_mem _ _ h3' h4' link.consumer link.tag _ hwt _ hp sels hh hl
      exact ⟨hP.1, hP.2, hC.1, hC.2⟩
  have hinit : RowIn (S := S) (⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ : CopyRowExtension K) :=
    ⟨fun _ => S.zero_mem, fun _ => S.zero_mem, fun _ => S.zero_mem, fun _ => S.zero_mem⟩
  obtain ⟨r1, r2, r3, r4⟩ := hrow copyLinks _ hinit
  exact S.mul_mem (copyActive_mem sels hh hl) (copyResidual_mem _ ⟨r1, r2, r3, r4⟩ h1 chi hh1 hchi)

theorem copy_mem (pub : Public K) (lam chi : K) (hlam : lam ∈ S) (hchi : chi ∈ S)
    (o : Openings K) (hz : ∀ i, o.z i ∈ S) (h1 : K) (hh1 : h1 ∈ S) (sel : Sel K)
    (hsel : ∀ k, sel k ∈ S) : ∀ r ∈ copyFamily.residuals pub lam chi o h1 sel, r ∈ S := by
  simp only [copyFamily, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true]
  exact copyEvaluate_mem o.z hz h1 hh1 (copySelectors sel) (g2High_mem sel hsel)
    (g2Low_mem sel hsel) lam chi hlam hchi _ _

end Copy

/-! ## The lanes and the terminal -/

theorem scalarLaneAt_mem {F : Subfield K} (hFS : ∀ x ∈ F, x ∈ S) (pub : Public K)
    (hpub : PublicBase F pub) (o : Openings K)
    (hz : ∀ i, o.z i ∈ S) (hs : ∀ i, o.succ i ∈ S) (hx : ∀ i, o.xor12 i ∈ S)
    (sel : Sel K) (hsel : ∀ k, sel k ∈ S) (i : Nat) : scalarLaneAt pub o sel i ∈ S := by
  have hsch := getD_mem S _ (schedule_mem pub o sel hz hsel)
  have hocc := getD_mem S _ (occupancy_mem pub o sel hz hsel)
  have hpath := getD_mem S _ (path_mem pub o sel hz hs hsel)
  have hval := getD_mem S _ (value_mem pub o sel hz hs hx hsel)
  have hdig := getD_mem S _ (digest_mem pub o sel hz hsel hFS hpub)
  have hass := getD_mem S _ (asset_mem pub o sel hz hsel hFS hpub)
  unfold scalarLaneAt
  split_ifs
  · exact S.add_mem (hsch _) (hocc _)
  · exact hsch _
  · exact hpath _
  · exact hval _
  · exact hdig _
  · exact hass _
  · exact S.zero_mem

theorem laneAt_mem {F : Subfield K} (hFS : ∀ x ∈ F, x ∈ S) (B : PackBasis F)
    (hi : B.i ∈ S) (hu : B.u ∈ S) (pub : Public K) (hpub : PublicBase F pub)
    (lam chi : K) (hlam : lam ∈ S) (hchi : chi ∈ S) (o : Openings K)
    (hz : ∀ i, o.z i ∈ S) (hs : ∀ i, o.succ i ∈ S) (hx : ∀ i, o.xor12 i ∈ S)
    (h1 : K) (hh1 : h1 ∈ S) (sel : Sel K) (hsel : ∀ k, sel k ∈ S) (i : Fin 29) :
    laneAt pub lam chi B o h1 sel i ∈ S := by
  unfold laneAt
  split_ifs
  · exact getD_mem S _ (poseidonPacked_mem B hi hu pub o sel hz hs hx hsel) _
  · exact pack4_mem B hi hu _ (fun j => scalarLaneAt_mem S hFS pub hpub o hz hs hx sel hsel _)
  · exact getD_mem S _ (copy_mem pub lam chi hlam hchi o hz h1 hh1 sel hsel) _

/-- The terminal lies in any subfield containing `F`, `B.i`, `B.u`, the
challenges, `zc`, the claims and the point. -/
theorem terminalValue_mem {F : Subfield K} (hFS : ∀ x ∈ F, x ∈ S) (B : PackBasis F)
    (hi : B.i ∈ S) (hu : B.u ∈ S) (pub : Public K) (hpub : PublicBase F pub)
    (lam chi θ μ : K) (hlam : lam ∈ S) (hchi : chi ∈ S) (hθ : θ ∈ S) (hμ : μ ∈ S)
    (zc : Fin 10 → K) (hzc : ∀ i, zc i ∈ S) (y : Fin 3 → Fin 29 → K) (hy : ∀ j c, y j c ∈ S)
    (α : Fin 10 → K) (hα : ∀ i, α i ∈ S) :
    terminalValue pub lam chi θ μ zc B y α ∈ S := by
  have hsel : ∀ k, selAt α k ∈ S := fun k =>
    R0Z.K4Values.eqWeight_mem S _ (fun b => hα _) k
  have hlane := laneAt_mem S hFS B hi hu pub hpub lam chi hlam hchi
    ⟨fun c => y 0 (Fin.castLE (by omega) c), fun c => y 1 (Fin.castLE (by omega) c),
      fun c => y 2 (Fin.castLE (by omega) c)⟩
    (fun _ => hy _ _) (fun _ => hy _ _) (fun _ => hy _ _) (y 0 26) (hy _ _) (selAt α) hsel
  have heq : eqValue zc α ∈ S := by
    unfold eqValue
    exact prod_mem fun c _ => S.add_mem (S.add_mem (S.sub_mem (S.sub_mem S.one_mem (hzc c)) (hα c))
      (S.mul_mem (hzc c) (hα c))) (S.mul_mem (hzc c) (hα c))
  have hact : activeAt α ∈ S :=
    copyActive_mem (copySelectors (selAt α)) (g2High_mem _ hsel) (g2Low_mem _ hsel)
  unfold terminalValue
  try dsimp only
  exact S.add_mem (S.add_mem (S.mul_mem heq (sum_mem fun i _ => S.mul_mem (S.pow_mem hθ _) (hlane i)))
    (S.mul_mem hμ (hy _ _))) (S.mul_mem (S.mul_mem hμ hμ) (S.mul_mem (S.sub_mem S.one_mem hact) (hy _ _)))

/-- J2b: `TerminalClosed` on `K₄` from `SemK4` and `PublicBase`. -/
theorem terminalClosed {F : Subfield K} (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (pub : Public K) (ch : R0Z.HonestView.Challenges K)
    (hsem : ∀ i, ch.sem i ∈ R0Z.K4.K4 B hB) (hpub : PublicBase F pub) :
    R0Z.K4Values.TerminalClosed (R0Z.K4.K4 B hB) pub B ch := by
  intro y a hy ha
  exact terminalValue_mem _ (fun x hx => R0Z.K4.F_le_K4 B hB hx) B (R0Z.K4.i_mem_K4 B hB)
    (R0Z.K4.u_mem_K4 B hB) pub hpub _ _ _ _ (hsem 0) (hsem 1) (hsem 2) (hsem 13)
    (R0Z.HonestView.zc ch) (fun i => hsem _) y hy a ha

#print axioms terminalClosed
#print axioms foldl_mem
#print axioms getD_mem
#print axioms schedule_mem
#print axioms occupancy_mem
#print axioms path_mem
#print axioms value_mem
#print axioms digest_mem
#print axioms asset_mem
#print axioms poseidonPacked_mem
#print axioms copy_mem
#print axioms laneAt_mem
#print axioms terminalValue_mem

end R0Z.TerminalClosed

end
