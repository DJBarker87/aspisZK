import R0P.Path

/-! G2, source T = pair_forest_semantic_terminal.rs at
 e4d68a70d3f6beb215c9f6dd418f4a2a3740c809. Scalar source slots 0–31 only,
 before packing and before the separate occupancy contributions. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]
attribute [local irreducible] g2High g2Low g2SumHigh

/-- T:218–239, initial_variant_selectors, same tuple and operation order. -/
def scheduleVariantSelectors (v : Variant) (h27 h28 h29 : K) : K × K × K × K :=
  match v with
  | .privateTransfer => (h27, 0, h27+h28, h29)
  | .withdrawal => (0, (h27+h28)+h29, 0, 0)

/-- T:156–164,246: one accumulator over ranges 4..25 then 33..57. -/
def scheduleNodes (sel : Sel K) : K :=
  ((List.ofFn (fun i : Fin 21 => g2High sel ⟨4+i.val, by omega⟩)) ++
    (List.ofFn (fun i : Fin 24 => g2High sel ⟨33+i.val, by omega⟩))).foldl (· + ·) 0

theorem schedule_nodes_row (b : Fin 1024) :
    scheduleNodes (rowSel (K := K) b) =
      (if 4 ≤ b.val/16 ∧ b.val/16 < 25 then 1 else 0) +
      (if 33 ≤ b.val/16 ∧ b.val/16 < 57 then 1 else 0) := by
  have he : scheduleNodes (rowSel (K := K) b) =
      g2SumHigh (rowSel b) 4 21 (by omega) + g2SumHigh (rowSel b) 33 24 (by omega) := by
    simp only [scheduleNodes, g2SumHigh, g2_fold_add, List.sum_append, zero_add]
  rw [he, g2_sum_high_row, g2_sum_high_row]

/-- T:241–282: literal initial array, including its two subtracting writes.
RATE=8 (poseidon2.rs:57); domains are spend.rs:14–16 casts. -/
def scheduleInitial (v : Variant) (o : Openings K) (sel : Sel K) : Fin 16 → K :=
  let high := g2High sel
  let low := g2Low sel
  let nodes := scheduleNodes sel
  let firstCommon := ((high 0 + high 1) + high 25) + high 30
  let (transferFirst, fixed, _, _) := scheduleVariantSelectors v (high 27) (high 28) (high 29)
  let fullInitial := low 0 * ((firstCommon + transferFirst) + fixed)
  let rateInitial := low 0 * nodes
  let initial := fun lane : Fin 16 =>
    if lane.val < 8 then (fullInitial+rateInitial)*o.z lane else fullInitial*o.z lane
  let noteFirst := (high 1+high 30)+transferFirst
  let domain := (high 0*(0x4153_0001 : K)+noteFirst*(0x4153_0003 : K))+high 25*(0x4153_0002 : K)
  let length := (high 0*(8 : K)+noteFirst*(18 : K))+high 25*(16 : K)
  fun lane => if lane = 8 then initial lane - low 0*domain
    else if lane = 9 then initial lane - low 0*length else initial lane

/-- T:315–334: absorption_lanes_literal (the production non-factor path). -/
def scheduleAbsorptionLiteral (low fixed chunkTwo chunkEight nodes : K)
    (o : Fin 16 → K) : Fin 16 → K :=
  fun lane =>
    let blocks := if lane.val < 2 then fixed else if lane.val < 8 then fixed+chunkTwo
      else ((fixed+chunkTwo)+chunkEight)+nodes
    low*blocks*o lane

/-- T:284–312: literal absorption selector setup and call. -/
def scheduleAbsorption (v : Variant) (o : Openings K) (sel : Sel K) : Fin 16 → K :=
  let high := g2High sel
  let nodes := scheduleNodes sel
  let (_, fixed, privateEight, privateTwo) := scheduleVariantSelectors v (high 27) (high 28) (high 29)
  let chunkEight := ((((((high 0+high 1)+high 2)+high 25)+high 26)+high 30)+high 31)
  let chunkTwo := high 3+high 32
  let chunkEight := chunkEight+privateEight
  let chunkTwo := chunkTwo+privateTwo
  scheduleAbsorptionLiteral (g2Low sel 12) fixed chunkTwo chunkEight nodes o.z

/-- T:382–391, scalar arrays in initial-then-absorption order. -/
def scheduleFamily : Family K where
  residuals := fun pub o sel => List.ofFn (scheduleInitial pub.variant o sel) ++
    List.ofFn (scheduleAbsorption pub.variant o sel)

/-- T:246–280, simplified row catalogue used only in the theorem. -/
abbrev ScheduleFull (v : Variant) (h : Nat) : Prop :=
  h=0 ∨ h=1 ∨ h=25 ∨ h=30 ∨ h=27 ∨ (v = .withdrawal ∧ (h=28 ∨ h=29))

/-- T:246, the two node ranges. -/
abbrev ScheduleNode (h : Nat) : Prop := (4 ≤ h ∧ h < 25) ∨ (33 ≤ h ∧ h < 57)

/-- T:270–282, prescribed initial domain and length, a row-equation term. -/
def scheduleTarget (v : Variant) (h : Nat) (lane : Fin 16) : K :=
  if lane=8 then
    if h=0 then 0x4153_0001 else if h=1 ∨ h=30 ∨ (v = .privateTransfer ∧ h=27)
      then 0x4153_0003 else if h=25 then 0x4153_0002 else 0
  else if lane=9 then
    if h=0 then 8 else if h=1 ∨ h=30 ∨ (v = .privateTransfer ∧ h=27)
      then 18 else if h=25 then 16 else 0
  else 0

/-- T:284–334, exact per-lane absorption support, used only in lemmas. -/
abbrev ScheduleAbsorbs (v : Variant) (h lane : Nat) : Prop :=
  if lane < 2 then v = .withdrawal ∧ (h=27 ∨ h=28 ∨ h=29)
  else if lane < 8 then h=3 ∨ h=32 ∨ h=29 ∨ (v = .withdrawal ∧ (h=27 ∨ h=28))
  else h < 57

attribute [local irreducible] scheduleInitial scheduleAbsorption scheduleNodes scheduleFamily

private theorem schedule_low_zero (b : Fin 1024) :
    g2Low (rowSel (K := K) b) 0 = if b.val % 16 = 0 then 1 else 0 := by
  rw [g2_low_row]
  change (if 0 = b.val % 16 then (1 : K) else 0) = _
  by_cases hm : b.val % 16 = 0
  · rw [if_pos hm.symm, if_pos hm]
  · have hne : ¬ 0 = b.val % 16 := by intro he; exact hm he.symm
    rw [if_neg hne, if_neg hm]

private theorem schedule_low_twelve (b : Fin 1024) :
    g2Low (rowSel (K := K) b) 12 = if b.val % 16 = 12 then 1 else 0 := by
  rw [g2_low_row]
  change (if (12 : Nat) = b.val % 16 then (1 : K) else 0) = _
  by_cases hm : b.val % 16 = 12
  · rw [if_pos hm.symm, if_pos hm]
  · have hne : ¬ (12 : Nat) = b.val % 16 := by intro he; exact hm he.symm
    rw [if_neg hne, if_neg hm]

private theorem schedule_node_high_zero (b : Fin 1024)
    (hn : ScheduleNode (b.val/16)) (i : Fin 64) (hi : ¬ ScheduleNode i.val) :
    g2High (rowSel (K := K) b) i = 0 := by
  rw [g2_high_row, if_neg]
  intro he
  exact hi (he ▸ hn)

private theorem schedule_node_nodes_one (b : Fin 1024)
    (hn : ScheduleNode (b.val/16)) : scheduleNodes (rowSel (K := K) b) = 1 := by
  rw [schedule_nodes_row]
  rcases hn with hn | hn
  · rw [if_pos hn, if_neg (by omega), add_zero]
  · rw [if_neg (by omega), if_pos hn, zero_add]

private theorem schedule_initial_block_0 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=0) :
    scheduleInitial v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 0 then
        if ScheduleFull v (b.val/16) then A (c.castAdd 13) b - scheduleTarget v (b.val/16) c
        else if ScheduleNode (b.val/16) ∧ c.val < 8 then A (c.castAdd 13) b else 0
      else 0 := by
  have h0 : g2High (rowSel (K := K) b) 0 = 1 := by
    rw [g2_high_row]
    norm_num [hb]
  have h1 : g2High (rowSel (K := K) b) 1 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h25 : g2High (rowSel (K := K) b) 25 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h27 : g2High (rowSel (K := K) b) 27 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h28 : g2High (rowSel (K := K) b) 28 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h29 : g2High (rowSel (K := K) b) 29 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h30 : g2High (rowSel (K := K) b) 30 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have hnodes : scheduleNodes (rowSel (K := K) b) = 0 := by
    rw [schedule_nodes_row]
    norm_num [hb]
  have hlow := schedule_low_zero (K := K) b
  cases v <;> by_cases hl : b.val % 16 = 0 <;>
    by_cases h8 : c = 8 <;> by_cases h9 : c = 9
  all_goals
    simp [scheduleInitial, scheduleVariantSelectors, h0, h1, h25, h27, h28, h29,
      h30, hnodes, hlow, hl, h8, h9, hb, ScheduleFull,
      scheduleTarget, rowOpenings, Fin.castLE, Fin.castAdd]

private theorem schedule_initial_block_1 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=1) :
    scheduleInitial v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 0 then
        if ScheduleFull v (b.val/16) then A (c.castAdd 13) b - scheduleTarget v (b.val/16) c
        else if ScheduleNode (b.val/16) ∧ c.val < 8 then A (c.castAdd 13) b else 0
      else 0 := by
  have h0 : g2High (rowSel (K := K) b) 0 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h1 : g2High (rowSel (K := K) b) 1 = 1 := by
    rw [g2_high_row]
    norm_num [hb]
  have h25 : g2High (rowSel (K := K) b) 25 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h27 : g2High (rowSel (K := K) b) 27 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h28 : g2High (rowSel (K := K) b) 28 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h29 : g2High (rowSel (K := K) b) 29 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h30 : g2High (rowSel (K := K) b) 30 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have hnodes : scheduleNodes (rowSel (K := K) b) = 0 := by
    rw [schedule_nodes_row]
    norm_num [hb]
  have hlow := schedule_low_zero (K := K) b
  cases v <;> by_cases hl : b.val % 16 = 0 <;>
    by_cases h8 : c = 8 <;> by_cases h9 : c = 9
  all_goals
    simp [scheduleInitial, scheduleVariantSelectors, h0, h1, h25, h27, h28, h29,
      h30, hnodes, hlow, hl, h8, h9, hb, ScheduleFull,
      scheduleTarget, rowOpenings, Fin.castLE, Fin.castAdd]

private theorem schedule_initial_block_25 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=25) :
    scheduleInitial v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 0 then
        if ScheduleFull v (b.val/16) then A (c.castAdd 13) b - scheduleTarget v (b.val/16) c
        else if ScheduleNode (b.val/16) ∧ c.val < 8 then A (c.castAdd 13) b else 0
      else 0 := by
  have h0 : g2High (rowSel (K := K) b) 0 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h1 : g2High (rowSel (K := K) b) 1 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h25 : g2High (rowSel (K := K) b) 25 = 1 := by
    rw [g2_high_row]
    norm_num [hb]
  have h27 : g2High (rowSel (K := K) b) 27 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h28 : g2High (rowSel (K := K) b) 28 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h29 : g2High (rowSel (K := K) b) 29 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h30 : g2High (rowSel (K := K) b) 30 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have hnodes : scheduleNodes (rowSel (K := K) b) = 0 := by
    rw [schedule_nodes_row]
    norm_num [hb]
  have hlow := schedule_low_zero (K := K) b
  cases v <;> by_cases hl : b.val % 16 = 0 <;>
    by_cases h8 : c = 8 <;> by_cases h9 : c = 9
  all_goals
    simp [scheduleInitial, scheduleVariantSelectors, h0, h1, h25, h27, h28, h29,
      h30, hnodes, hlow, hl, h8, h9, hb, ScheduleFull,
      scheduleTarget, rowOpenings, Fin.castLE, Fin.castAdd]

private theorem schedule_initial_block_27 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=27) :
    scheduleInitial v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 0 then
        if ScheduleFull v (b.val/16) then A (c.castAdd 13) b - scheduleTarget v (b.val/16) c
        else if ScheduleNode (b.val/16) ∧ c.val < 8 then A (c.castAdd 13) b else 0
      else 0 := by
  have h0 : g2High (rowSel (K := K) b) 0 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h1 : g2High (rowSel (K := K) b) 1 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h25 : g2High (rowSel (K := K) b) 25 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h27 : g2High (rowSel (K := K) b) 27 = 1 := by
    rw [g2_high_row]
    norm_num [hb]
  have h28 : g2High (rowSel (K := K) b) 28 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h29 : g2High (rowSel (K := K) b) 29 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h30 : g2High (rowSel (K := K) b) 30 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have hnodes : scheduleNodes (rowSel (K := K) b) = 0 := by
    rw [schedule_nodes_row]
    norm_num [hb]
  have hlow := schedule_low_zero (K := K) b
  cases v <;> by_cases hl : b.val % 16 = 0 <;>
    by_cases h8 : c = 8 <;> by_cases h9 : c = 9
  all_goals
    simp [scheduleInitial, scheduleVariantSelectors, h0, h1, h25, h27, h28, h29,
      h30, hnodes, hlow, hl, h8, h9, hb, ScheduleFull,
      scheduleTarget, rowOpenings, Fin.castLE, Fin.castAdd]

private theorem schedule_initial_block_28 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=28) :
    scheduleInitial v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 0 then
        if ScheduleFull v (b.val/16) then A (c.castAdd 13) b - scheduleTarget v (b.val/16) c
        else if ScheduleNode (b.val/16) ∧ c.val < 8 then A (c.castAdd 13) b else 0
      else 0 := by
  have h0 : g2High (rowSel (K := K) b) 0 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h1 : g2High (rowSel (K := K) b) 1 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h25 : g2High (rowSel (K := K) b) 25 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h27 : g2High (rowSel (K := K) b) 27 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h28 : g2High (rowSel (K := K) b) 28 = 1 := by
    rw [g2_high_row]
    norm_num [hb]
  have h29 : g2High (rowSel (K := K) b) 29 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h30 : g2High (rowSel (K := K) b) 30 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have hnodes : scheduleNodes (rowSel (K := K) b) = 0 := by
    rw [schedule_nodes_row]
    norm_num [hb]
  have hlow := schedule_low_zero (K := K) b
  cases v <;> by_cases hl : b.val % 16 = 0 <;>
    by_cases h8 : c = 8 <;> by_cases h9 : c = 9
  all_goals
    simp [scheduleInitial, scheduleVariantSelectors, h0, h1, h25, h27, h28, h29,
      h30, hnodes, hlow, hl, h8, h9, hb, ScheduleFull, ScheduleNode,
      scheduleTarget, rowOpenings, Fin.castLE, Fin.castAdd]

private theorem schedule_initial_block_29 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=29) :
    scheduleInitial v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 0 then
        if ScheduleFull v (b.val/16) then A (c.castAdd 13) b - scheduleTarget v (b.val/16) c
        else if ScheduleNode (b.val/16) ∧ c.val < 8 then A (c.castAdd 13) b else 0
      else 0 := by
  have h0 : g2High (rowSel (K := K) b) 0 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h1 : g2High (rowSel (K := K) b) 1 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h25 : g2High (rowSel (K := K) b) 25 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h27 : g2High (rowSel (K := K) b) 27 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h28 : g2High (rowSel (K := K) b) 28 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h29 : g2High (rowSel (K := K) b) 29 = 1 := by
    rw [g2_high_row]
    norm_num [hb]
  have h30 : g2High (rowSel (K := K) b) 30 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have hnodes : scheduleNodes (rowSel (K := K) b) = 0 := by
    rw [schedule_nodes_row]
    norm_num [hb]
  have hlow := schedule_low_zero (K := K) b
  cases v <;> by_cases hl : b.val % 16 = 0 <;>
    by_cases h8 : c = 8 <;> by_cases h9 : c = 9
  all_goals
    simp [scheduleInitial, scheduleVariantSelectors, h0, h1, h25, h27, h28, h29,
      h30, hnodes, hlow, hl, h8, h9, hb, ScheduleFull, ScheduleNode,
      scheduleTarget, rowOpenings, Fin.castLE, Fin.castAdd]

private theorem schedule_initial_block_30 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=30) :
    scheduleInitial v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 0 then
        if ScheduleFull v (b.val/16) then A (c.castAdd 13) b - scheduleTarget v (b.val/16) c
        else if ScheduleNode (b.val/16) ∧ c.val < 8 then A (c.castAdd 13) b else 0
      else 0 := by
  have h0 : g2High (rowSel (K := K) b) 0 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h1 : g2High (rowSel (K := K) b) 1 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h25 : g2High (rowSel (K := K) b) 25 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h27 : g2High (rowSel (K := K) b) 27 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h28 : g2High (rowSel (K := K) b) 28 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h29 : g2High (rowSel (K := K) b) 29 = 0 := by
    rw [g2_high_row]
    norm_num [hb]
  have h30 : g2High (rowSel (K := K) b) 30 = 1 := by
    rw [g2_high_row]
    norm_num [hb]
  have hnodes : scheduleNodes (rowSel (K := K) b) = 0 := by
    rw [schedule_nodes_row]
    norm_num [hb]
  have hlow := schedule_low_zero (K := K) b
  cases v <;> by_cases hl : b.val % 16 = 0 <;>
    by_cases h8 : c = 8 <;> by_cases h9 : c = 9
  all_goals
    simp [scheduleInitial, scheduleVariantSelectors, h0, h1, h25, h27, h28, h29,
      h30, hnodes, hlow, hl, h8, h9, hb, ScheduleFull,
      scheduleTarget, rowOpenings, Fin.castLE, Fin.castAdd]

private theorem schedule_initial_node (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hn : ScheduleNode (b.val/16)) :
    scheduleInitial v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 0 then
        if ScheduleFull v (b.val/16) then A (c.castAdd 13) b - scheduleTarget v (b.val/16) c
        else if ScheduleNode (b.val/16) ∧ c.val < 8 then A (c.castAdd 13) b else 0
      else 0 := by
  have h0 := schedule_node_high_zero (K := K) b hn (0 : Fin 64) (by norm_num [ScheduleNode])
  have h1 := schedule_node_high_zero (K := K) b hn (1 : Fin 64) (by norm_num [ScheduleNode])
  have h25 := schedule_node_high_zero (K := K) b hn (25 : Fin 64) (by norm_num [ScheduleNode])
  have h27 := schedule_node_high_zero (K := K) b hn (27 : Fin 64) (by norm_num [ScheduleNode])
  have h28 := schedule_node_high_zero (K := K) b hn (28 : Fin 64) (by norm_num [ScheduleNode])
  have h29 := schedule_node_high_zero (K := K) b hn (29 : Fin 64) (by norm_num [ScheduleNode])
  have h30 := schedule_node_high_zero (K := K) b hn (30 : Fin 64) (by norm_num [ScheduleNode])
  have hnodes := schedule_node_nodes_one (K := K) b hn
  have hlow := schedule_low_zero (K := K) b
  have hf : ¬ ScheduleFull v (b.val/16) := by
    unfold ScheduleFull ScheduleNode at *; omega
  simp only [if_neg hf]
  cases v <;> simp only [scheduleInitial, scheduleVariantSelectors, h0, h1, h25, h27, h28, h29, h30, hnodes, zero_add, add_zero, zero_mul,
    mul_zero, sub_zero, ite_self, hlow]
  all_goals
    by_cases hl : b.val%16 = 0
    · by_cases hc : c.val < 8
      · have hnc : ScheduleNode (b.val/16) ∧ c.val < 8 := ⟨hn, hc⟩
        simp only [if_pos hl, if_pos hnc, if_pos hc, one_mul, rowOpenings]
        rfl
      · have hnc : ¬ (ScheduleNode (b.val/16) ∧ c.val < 8) := by tauto
        simp only [if_pos hl, if_neg hc, if_neg hnc]
    · simp only [if_neg hl, zero_mul, ite_self]

private theorem schedule_initial_off (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16)
    (hn : ¬ ScheduleNode (b.val/16)) (hb : b.val/16≠0 ∧ b.val/16≠1 ∧ b.val/16≠25 ∧ b.val/16≠27 ∧ b.val/16≠28 ∧ b.val/16≠29 ∧ b.val/16≠30) :
    scheduleInitial v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 0 then
        if ScheduleFull v (b.val/16) then A (c.castAdd 13) b - scheduleTarget v (b.val/16) c
        else if ScheduleNode (b.val/16) ∧ c.val < 8 then A (c.castAdd 13) b else 0
      else 0 := by
  have h0 : g2High (rowSel (K := K) b) 0 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (0 = b.val/16); omega
  have h1 : g2High (rowSel (K := K) b) 1 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (1 = b.val/16); omega
  have h25 : g2High (rowSel (K := K) b) 25 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (25 = b.val/16); omega
  have h27 : g2High (rowSel (K := K) b) 27 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (27 = b.val/16); omega
  have h28 : g2High (rowSel (K := K) b) 28 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (28 = b.val/16); omega
  have h29 : g2High (rowSel (K := K) b) 29 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (29 = b.val/16); omega
  have h30 : g2High (rowSel (K := K) b) 30 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (30 = b.val/16); omega
  have hnodes : scheduleNodes (rowSel (K := K) b) = 0 := by
    rw [schedule_nodes_row, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h)), zero_add]
  have hlow := schedule_low_zero (K := K) b
  have hf : ¬ ScheduleFull v (b.val/16) := by unfold ScheduleFull; omega
  have hnc : ¬ (ScheduleNode (b.val/16) ∧ c.val < 8) := by tauto
  simp only [if_neg hf, if_neg hnc, ite_self]
  cases v <;> simp only [scheduleInitial, scheduleVariantSelectors, h0, h1, h25, h27, h28, h29, h30, hnodes, hlow, add_zero,
    zero_mul, mul_zero, sub_zero, ite_self]

theorem schedule_initial_row (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) :
    scheduleInitial v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 0 then
        if ScheduleFull v (b.val/16) then A (c.castAdd 13) b - scheduleTarget v (b.val/16) c
        else if ScheduleNode (b.val/16) ∧ c.val < 8 then A (c.castAdd 13) b else 0
      else 0 := by
  by_cases hn : ScheduleNode (b.val/16)
  · exact schedule_initial_node v A b c hn
  · have hh : b.val/16=0 ∨ b.val/16=1 ∨ b.val/16=25 ∨ b.val/16=27 ∨ b.val/16=28 ∨ b.val/16=29 ∨ b.val/16=30 ∨ (b.val/16≠0 ∧ b.val/16≠1 ∧ b.val/16≠25 ∧ b.val/16≠27 ∧ b.val/16≠28 ∧ b.val/16≠29 ∧ b.val/16≠30) := by omega
    rcases hh with hh | hh | hh | hh | hh | hh | hh | hh
    · exact schedule_initial_block_0 v A b c hh
    · exact schedule_initial_block_1 v A b c hh
    · exact schedule_initial_block_25 v A b c hh
    · exact schedule_initial_block_27 v A b c hh
    · exact schedule_initial_block_28 v A b c hh
    · exact schedule_initial_block_29 v A b c hh
    · exact schedule_initial_block_30 v A b c hh
    · exact schedule_initial_off v A b c hn hh

private theorem schedule_absorption_block_0 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=0) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_1 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=1) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_2 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=2) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_3 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=3) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_25 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=25) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_26 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=26) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_27 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=27) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_28 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=28) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_29 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=29) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_30 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=30) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_31 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=31) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_block_32 (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hb : b.val/16=32) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have hlow := schedule_low_twelve (K := K) b
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
          rowOpenings, hb, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, g2_high_row, hlow, schedule_nodes_row, ScheduleAbsorbs,
            rowOpenings, hb, hc2, hc8]

private theorem schedule_absorption_node (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) (hn : ScheduleNode (b.val/16)) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have h0 := schedule_node_high_zero (K := K) b hn (0 : Fin 64) (by norm_num [ScheduleNode])
  have h1 := schedule_node_high_zero (K := K) b hn (1 : Fin 64) (by norm_num [ScheduleNode])
  have h2 := schedule_node_high_zero (K := K) b hn (2 : Fin 64) (by norm_num [ScheduleNode])
  have h3 := schedule_node_high_zero (K := K) b hn (3 : Fin 64) (by norm_num [ScheduleNode])
  have h25 := schedule_node_high_zero (K := K) b hn (25 : Fin 64) (by norm_num [ScheduleNode])
  have h26 := schedule_node_high_zero (K := K) b hn (26 : Fin 64) (by norm_num [ScheduleNode])
  have h27 := schedule_node_high_zero (K := K) b hn (27 : Fin 64) (by norm_num [ScheduleNode])
  have h28 := schedule_node_high_zero (K := K) b hn (28 : Fin 64) (by norm_num [ScheduleNode])
  have h29 := schedule_node_high_zero (K := K) b hn (29 : Fin 64) (by norm_num [ScheduleNode])
  have h30 := schedule_node_high_zero (K := K) b hn (30 : Fin 64) (by norm_num [ScheduleNode])
  have h31 := schedule_node_high_zero (K := K) b hn (31 : Fin 64) (by norm_num [ScheduleNode])
  have h32 := schedule_node_high_zero (K := K) b hn (32 : Fin 64) (by norm_num [ScheduleNode])
  have hnodes := schedule_node_nodes_one (K := K) b hn
  have hlow := schedule_low_twelve (K := K) b
  have hnlt : b.val / 16 < 57 := by rcases hn with hn | hn <;> omega
  have he3 : b.val / 16 ≠ 3 := by rcases hn with hn | hn <;> omega
  have he27 : b.val / 16 ≠ 27 := by rcases hn with hn | hn <;> omega
  have he28 : b.val / 16 ≠ 28 := by rcases hn with hn | hn <;> omega
  have he29 : b.val / 16 ≠ 29 := by rcases hn with hn | hn <;> omega
  have he32 : b.val / 16 ≠ 32 := by rcases hn with hn | hn <;> omega
  cases v with
  | privateTransfer =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, h0, h1, h2, h3, h25, h26, h27, h28, h29, h30,
          h31, h32, hnodes, hlow, ScheduleAbsorbs, he27, he28, he29,
          rowOpenings, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, h0, h1, h2, h3, h25, h26, h27, h28, h29, h30,
            h31, h32, hnodes, hlow, ScheduleAbsorbs, he3, he27, he28, he29,
            he32, rowOpenings, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, h0, h1, h2, h3, h25, h26, h27, h28, h29, h30,
            h31, h32, hnodes, hlow, ScheduleAbsorbs, hnlt,
            rowOpenings, hc2, hc8]
  | withdrawal =>
      by_cases hc2 : c.val < 2
      · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
          scheduleVariantSelectors, h0, h1, h2, h3, h25, h26, h27, h28, h29, h30,
          h31, h32, hnodes, hlow, ScheduleAbsorbs, he27, he28, he29,
          rowOpenings, hc2]
      · by_cases hc8 : c.val < 8
        · simp [Fin.castLE, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, h0, h1, h2, h3, h25, h26, h27, h28, h29, h30,
            h31, h32, hnodes, hlow, ScheduleAbsorbs, he3, he27, he28, he29,
            he32, rowOpenings, hc2, hc8]
        · simp [Fin.castLE, Fin.castAdd, scheduleAbsorption, scheduleAbsorptionLiteral,
            scheduleVariantSelectors, h0, h1, h2, h3, h25, h26, h27, h28, h29, h30,
            h31, h32, hnodes, hlow, ScheduleAbsorbs, hnlt,
            rowOpenings, hc2, hc8]

private theorem schedule_absorption_off (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16)
    (hn : ¬ ScheduleNode (b.val/16)) (hb : b.val/16≠0 ∧ b.val/16≠1 ∧ b.val/16≠2 ∧ b.val/16≠3 ∧ b.val/16≠25 ∧ b.val/16≠26 ∧ b.val/16≠27 ∧ b.val/16≠28 ∧ b.val/16≠29 ∧ b.val/16≠30 ∧ b.val/16≠31 ∧ b.val/16≠32) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  have h0 : g2High (rowSel (K := K) b) 0 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (0 = b.val/16); omega
  have h1 : g2High (rowSel (K := K) b) 1 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (1 = b.val/16); omega
  have h2 : g2High (rowSel (K := K) b) 2 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (2 = b.val/16); omega
  have h3 : g2High (rowSel (K := K) b) 3 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (3 = b.val/16); omega
  have h25 : g2High (rowSel (K := K) b) 25 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (25 = b.val/16); omega
  have h26 : g2High (rowSel (K := K) b) 26 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (26 = b.val/16); omega
  have h27 : g2High (rowSel (K := K) b) 27 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (27 = b.val/16); omega
  have h28 : g2High (rowSel (K := K) b) 28 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (28 = b.val/16); omega
  have h29 : g2High (rowSel (K := K) b) 29 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (29 = b.val/16); omega
  have h30 : g2High (rowSel (K := K) b) 30 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (30 = b.val/16); omega
  have h31 : g2High (rowSel (K := K) b) 31 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (31 = b.val/16); omega
  have h32 : g2High (rowSel (K := K) b) 32 = 0 := by
    rw [g2_high_row, if_neg]; change ¬ (32 = b.val/16); omega
  have hnodes : scheduleNodes (rowSel (K := K) b) = 0 := by
    rw [schedule_nodes_row, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h)), zero_add]
  have hbig : 57 ≤ b.val/16 := by unfold ScheduleNode at hn; omega
  have ha : ¬ ScheduleAbsorbs v (b.val/16) c.val := by
    unfold ScheduleAbsorbs; split_ifs <;> omega
  have hal : ¬ (b.val%16=12 ∧ ScheduleAbsorbs v (b.val/16) c.val) := by tauto
  rw [if_neg hal]
  cases v <;> simp only [scheduleAbsorption, scheduleAbsorptionLiteral, scheduleVariantSelectors, h0, h1, h2, h3, h25, h26, h27, h28, h29, h30, h31, h32, hnodes, add_zero,
    zero_mul, mul_zero, ite_self]

theorem schedule_absorption_row (v : Variant) (A : Trace K) (b : Fin 1024) (c : Fin 16) :
    scheduleAbsorption v (rowOpenings A b) (rowSel b) c =
      if b.val%16 = 12 ∧ ScheduleAbsorbs v (b.val/16) c.val then A (c.castAdd 13) b else 0 := by
  by_cases hn : ScheduleNode (b.val/16)
  · exact schedule_absorption_node v A b c hn
  · have hh : b.val/16=0 ∨ b.val/16=1 ∨ b.val/16=2 ∨ b.val/16=3 ∨ b.val/16=25 ∨ b.val/16=26 ∨ b.val/16=27 ∨ b.val/16=28 ∨ b.val/16=29 ∨ b.val/16=30 ∨ b.val/16=31 ∨ b.val/16=32 ∨ (b.val/16≠0 ∧ b.val/16≠1 ∧ b.val/16≠2 ∧ b.val/16≠3 ∧ b.val/16≠25 ∧ b.val/16≠26 ∧ b.val/16≠27 ∧ b.val/16≠28 ∧ b.val/16≠29 ∧ b.val/16≠30 ∧ b.val/16≠31 ∧ b.val/16≠32) := by omega
    rcases hh with hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh
    · exact schedule_absorption_block_0 v A b c hh
    · exact schedule_absorption_block_1 v A b c hh
    · exact schedule_absorption_block_2 v A b c hh
    · exact schedule_absorption_block_3 v A b c hh
    · exact schedule_absorption_block_25 v A b c hh
    · exact schedule_absorption_block_26 v A b c hh
    · exact schedule_absorption_block_27 v A b c hh
    · exact schedule_absorption_block_28 v A b c hh
    · exact schedule_absorption_block_29 v A b c hh
    · exact schedule_absorption_block_30 v A b c hh
    · exact schedule_absorption_block_31 v A b c hh
    · exact schedule_absorption_block_32 v A b c hh
    · exact schedule_absorption_off v A b c hn hh

/-- Every emitted lane, including all prescribed zero cells, on the exact
selected rows. The block h is b/16; initial rows have b%16=0 and absorption
rows have b%16=12. No condition is imposed off these selector supports. -/
theorem schedule_holds_iff (pub : Public K) (A : Trace K) :
    Holds scheduleFamily pub A ↔
      (∀ b : Fin 1024, b.val%16=0 → ScheduleFull pub.variant (b.val/16) →
        ∀ c : Fin 16, A (c.castAdd 13) b = scheduleTarget pub.variant (b.val/16) c) ∧
      (∀ b : Fin 1024, b.val%16=0 → ScheduleNode (b.val/16) →
        ∀ c : Fin 8, A (c.castAdd 21) b = 0) ∧
      (∀ b : Fin 1024, b.val%16=12 → ∀ c : Fin 16,
        ScheduleAbsorbs pub.variant (b.val/16) c.val → A (c.castAdd 13) b = 0) := by
  simp only [Holds, scheduleFamily, List.forall_mem_append, List.forall_mem_ofFn_iff,
    schedule_initial_row, schedule_absorption_row]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro b hb hf c
      simpa only [if_pos hb, if_pos hf, sub_eq_zero] using (h b).1 c
    · intro b hb hn c
      have hf : ¬ ScheduleFull pub.variant (b.val/16) := by
        unfold ScheduleFull ScheduleNode at *; omega
      have hh := (h b).1 (c.castAdd 8)
      have hnc : ScheduleNode (b.val/16) ∧ (c.castAdd 8).val < 8 := ⟨hn, c.isLt⟩
      rw [if_pos hb, if_neg hf, if_pos hnc] at hh
      convert hh using 1; rfl
    · intro b hb c hc
      have hbc : b.val%16=12 ∧ ScheduleAbsorbs pub.variant (b.val/16) c.val := ⟨hb, hc⟩
      simpa only [if_pos hbc] using (h b).2 c
  · rintro ⟨hf, hn, ha⟩ b
    constructor
    · intro c
      by_cases hb : b.val%16=0
      · rw [if_pos hb]
        by_cases hh : ScheduleFull pub.variant (b.val/16)
        · rw [if_pos hh, hf b hb hh c, sub_self]
        · rw [if_neg hh]
          split_ifs with hc
          · exact hn b hb hc.1 ⟨c.val, hc.2⟩
          · rfl
      · rw [if_neg hb]
    · intro c
      split_ifs with hc
      · exact ha b hc.1 c hc.2
      · rfl

#print axioms schedule_node_high_zero
#print axioms schedule_node_nodes_one
#print axioms schedule_low_zero
#print axioms schedule_low_twelve
#print axioms schedule_initial_block_0
#print axioms schedule_initial_block_1
#print axioms schedule_initial_block_25
#print axioms schedule_initial_block_27
#print axioms schedule_initial_block_28
#print axioms schedule_initial_block_29
#print axioms schedule_initial_block_30
#print axioms schedule_initial_node
#print axioms schedule_initial_off
#print axioms schedule_absorption_block_0
#print axioms schedule_absorption_block_1
#print axioms schedule_absorption_block_2
#print axioms schedule_absorption_block_3
#print axioms schedule_absorption_block_25
#print axioms schedule_absorption_block_26
#print axioms schedule_absorption_block_27
#print axioms schedule_absorption_block_28
#print axioms schedule_absorption_block_29
#print axioms schedule_absorption_block_30
#print axioms schedule_absorption_block_31
#print axioms schedule_absorption_block_32
#print axioms schedule_absorption_node
#print axioms schedule_absorption_off
#print axioms schedule_nodes_row
#print axioms schedule_initial_row
#print axioms schedule_absorption_row
#print axioms schedule_holds_iff
end R0P
