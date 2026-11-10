import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_p13
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le at' K Lane frontierLoop decodeLane)

/-! ## 12. Simulation of the reference after the header guard.
Plan: the code of NCV_Reference.decode_lane_ref after the header guards is copied, stage by stage,
into zT0..zT5 (each stage calls the next); `ref_pass` checks the copy against the compiled
definition (by rewriting and `rfl`), and sim5..sim1 relate each stage to the corresponding
stage S5..S2 of the transcription. -/

abbrev RL : Type := core.result.Result NCV_Reference.Lane Unit
abbrev Dg : Type := Std.Array U32 8#usize

/-- field-wise relation between the transcription's lane and the reference lane -/
@[reducible] def LRel (l : Lane Dg) (r : NCV_Reference.Lane) : Prop :=
  l.bump = bt r.bump ∧ l.master = r.master.val.map bt ∧ l.laneId = bt r.lane_id ∧
  l.nextLeafIndex = r.next_leaf_index.val ∧ l.root = r.root ∧ l.frontier = r.frontier.val

/-- `none` goes with `Err ()`, `some l` with `Ok r` and `LRel l r` -/
@[reducible] def LCmp (o : Option (Lane Dg)) (r : RL) : Prop :=
  match o, r with
  | none, core.result.Result.Err _ => True
  | some l, core.result.Result.Ok r => LRel l r
  | _, _ => False

theorem lcmp_nn : LCmp none (core.result.Result.Err ()) := trivial

/-! ### the copied stages (verbatim from the compiled decode_lane_ref) -/

def zT5 (b : Slice U8) (i2 : U8) (master : Array U8 32#usize) (tree : Slice U8) (nli : U64)
    (val : Std.Array U32 8#usize) : Result RL := do
  let r1 ← NCV_Reference.decode_frontier tree nli
  let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf1 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    if nli = 0#u64
    then
      let a ← Array.index_usize NCV_Reference.EMPTY 20#usize
      let b6 ← NCV_Reference.eq_digest val a
      if b6
      then
        let i9 ← Slice.index_usize b 72#usize
        ok (core.result.Result.Ok
          { bump := i9, master, lane_id := i2, next_leaf_index := nli, root := val,
            frontier := val1 })
      else ok (core.result.Result.Err ())
    else
      let i9 ← Slice.index_usize b 72#usize
      ok (core.result.Result.Ok
        { bump := i9, master, lane_id := i2, next_leaf_index := nli, root := val,
          frontier := val1 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      NCV_Reference.Lane (core.convert.FromSame Unit) residual

def zT4 (b : Slice U8) (i2 : U8) (master : Array U8 32#usize) (tree : Slice U8) (nli : U64) :
    Result RL := do
  let r ← NCV_Reference.digest tree 16#usize
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val => zT5 b i2 master tree nli val
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      NCV_Reference.Lane (core.convert.FromSame Unit) residual

def zT3 (b : Slice U8) (i2 : U8) (master : Array U8 32#usize) (tree : Slice U8) : Result RL := do
  let nli ← NCV_Reference.word64 tree 8#usize
  if nli > 1048576#u64
  then ok (core.result.Result.Err ())
  else zT4 b i2 master tree nli

def zTc (b : Slice U8) (i2 : U8) (master : Array U8 32#usize) (tree : Slice U8) : Result RL := do
  let s6 ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) tree
      { «end» := 4#usize }
  let s7 ← lift (Array.to_slice (Array.make 4#usize [ 65#u8, 83#u8, 80#u8, 84#u8 ]))
  let b5 ← NCV_Reference.equal s6 s7
  if b5
  then
    let i5 ← Slice.index_usize tree 4#usize
    if i5 != 1#u8
    then ok (core.result.Result.Err ())
    else
      let i6 ← Slice.index_usize tree 5#usize
      if i6 != 20#u8
      then ok (core.result.Result.Err ())
      else
        let i7 ← Slice.index_usize tree 6#usize
        if i7 != 3#u8
        then ok (core.result.Result.Err ())
        else
          let i8 ← Slice.index_usize tree 7#usize
          if i8 != 1#u8
          then ok (core.result.Result.Err ())
          else zT3 b i2 master tree
  else ok (core.result.Result.Err ())

def zT1 (b : Slice U8) (i2 : U8) (master : Array U8 32#usize) : Result RL := do
  let tree ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) b
      { start := 80#usize }
  zTc b i2 master tree

def zT0 (b : Slice U8) (i2 : U8) (master : Array U8 32#usize) : Result RL := do
  let s5 ← lift (Array.to_slice master)
  let b4 ← NCV_Reference.zero s5
  if b4
  then ok (core.result.Result.Err ())
  else zT1 b i2 master

/-! ### generic condition lemmas (stated over a type with DecidableEq, as S5 is) -/

theorem condF {α : Type} [DecidableEq α] (n : Nat) (x e : α) (h : n ≠ 0 ∨ x = e) :
    (n == 0 && x != e) = false := by
  rcases h with h | h
  · simp [h]
  · simp [h]

theorem condT {α : Type} [DecidableEq α] (n : Nat) (x e : α) (h : n = 0 ∧ x ≠ e) :
    (n == 0 && x != e) = true := by
  obtain ⟨h1, h2⟩ := h
  simp [h1, h2]

/-! ### sim5 -/

theorem lrel_mk (b : Slice U8) (master : Array U8 32#usize) (ML : List UInt8)
    (hM : master.val.map bt = ML) (nli : U64) (val : Dg) (fr : List Dg) (G : FArr)
    (hGv : G.val = fr) :
    LCmp (some { bump := at' (bytesOf b) 72, master := ML, laneId := at' (bytesOf b) 5,
                 nextLeafIndex := nli.val, root := val, frontier := fr })
      (core.result.Result.Ok { bump := g b 72, master := master, lane_id := g b 5,
                               next_leaf_index := nli, root := val, frontier := G }) := by
  show LRel _ _
  exact ⟨at_g b 72, hM.symm, at_g b 5, rfl, rfl, hGv.symm⟩

theorem emp20 : ∃ a : Dg, Array.index_usize NCV_Reference.EMPTY 20#usize = ok a ∧
    a = K0.emptyRoots K0.treeDepth := by
  refine ⟨_, idx_arrG NCV_Reference.EMPTY 20#usize (by rw [empty_len]; simp), ?_⟩
  first
    | exact (empty_get 20 (by omega)).symm
    | (have v20 : (20#usize).val = 20 := by simp
       simp only [v20]
       exact (empty_get 20 (by omega)).symm)

theorem sim5 (b : Slice U8) (hb : b.val.length = 768) (master : Array U8 32#usize)
    (ML : List UInt8) (hM : master.val.map bt = ML) (tree : Slice U8)
    (htr : tree.val = b.val.drop 80) (nli : U64) (val : Dg) :
    ∃ r, zT5 b (g b 5) master tree nli val = ok r ∧
      LCmp (S5 K0 (bytesOf b) ML (bytesOf tree) nli.val val) r := by
  have hlen : 688 ≤ tree.val.length := by rw [htr, List.length_drop]; omega
  have v72 : (72#usize).val = 72 := by simp
  have g72 := idx_g b 72#usize (by rw [v72]; omega)
  rw [v72] at g72
  have hfe := frontier_eq tree hlen nli
  rcases hfl : frontierLoop K0 (bytesOf tree) nli.val 20 0 with _ | fr
  · rw [hfl] at hfe
    have hfe' : NCV_Reference.decode_frontier tree nli = ok (core.result.Result.Err ()) := hfe
    refine ⟨core.result.Result.Err (), ?_, ?_⟩
    · unfold zT5
      simp only [hfe', bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, core.convert.FromSame]
      try rfl
    · rw [S5_fnone K0 (bytesOf b) ML (bytesOf tree) nli.val val (by exact hfl)]
      exact lcmp_nn
  · rw [hfl] at hfe
    have hfe' : ∃ G : FArr, NCV_Reference.decode_frontier tree nli =
        ok (core.result.Result.Ok G) ∧ G.val = fr := hfe
    obtain ⟨G, hG, hGv⟩ := hfe'
    by_cases hz : nli = 0#u64
    · have hn0 : nli.val = 0 := by simp [hz]
      obtain ⟨a, h20, hae⟩ := emp20
      have hq := eq_digest_eq val a
      by_cases hr : val = K0.emptyRoots K0.treeDepth
      · have hc := condF nli.val val (K0.emptyRoots K0.treeDepth) (Or.inr hr)
        have hdt : decide (val.val = a.val) = true :=
          decide_eq_true (by rw [hae, hr])
        refine ⟨core.result.Result.Ok { bump := g b 72, master := master, lane_id := g b 5, next_leaf_index := nli, root := val, frontier := G }, ?_, ?_⟩
        · unfold zT5
          simp only [hG, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, eq_true hz,
            if_true, h20, hq, hdt, g72]
          try rfl
        · rw [S5_ok K0 (bytesOf b) ML (bytesOf tree) nli.val val fr (by exact hfl) hc]
          exact lrel_mk b master ML hM nli val fr G hGv
      · have hc := condT nli.val val (K0.emptyRoots K0.treeDepth) ⟨hn0, hr⟩
        have hdf : decide (val.val = a.val) = false :=
          decide_eq_false (fun h => hr (by rw [hae] at h; exact Subtype.ext h))
        refine ⟨core.result.Result.Err (), ?_, ?_⟩
        · unfold zT5
          simp only [hG, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, eq_true hz,
            if_true, h20, hq, hdf, Bool.false_eq_true, if_false]
          try rfl
        · rw [S5_bad K0 (bytesOf b) ML (bytesOf tree) nli.val val fr (by exact hfl) hc]
          exact lcmp_nn
    · have hn0 : nli.val ≠ 0 := fun h => hz (UScalar.eq_of_val_eq (by simp [h]))
      have hc := condF nli.val val (K0.emptyRoots K0.treeDepth) (Or.inl hn0)
      refine ⟨core.result.Result.Ok { bump := g b 72, master := master, lane_id := g b 5, next_leaf_index := nli, root := val, frontier := G }, ?_, ?_⟩
      · unfold zT5
        simp only [hG, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch, eq_false hz,
          if_false, g72]
        try rfl
      · rw [S5_ok K0 (bytesOf b) ML (bytesOf tree) nli.val val fr (by exact hfl) hc]
        exact lrel_mk b master ML hM nli val fr G hGv

#print axioms sim5

/-! ### sim4 -/

theorem sim4 (b : Slice U8) (hb : b.val.length = 768) (master : Array U8 32#usize)
    (ML : List UInt8) (hM : master.val.map bt = ML) (tree : Slice U8)
    (htr : tree.val = b.val.drop 80) (nli : U64) :
    ∃ r, zT4 b (g b 5) master tree nli = ok r ∧
      LCmp (S4 K0 (bytesOf b) ML (bytesOf tree) nli.val) r := by
  have v16 : (16#usize).val = 16 := by simp
  have hs : (16#usize).val + 32 ≤ tree.val.length := by
    rw [htr, List.length_drop, v16]; omega
  have hdig := digest_eq tree 16#usize hs
  have h16 : sl (bytesOf tree) 16 48 =
      sl (bytesOf tree) (16#usize).val ((16#usize).val + 32) := by simp
  rw [← h16] at hdig
  cases hd : decDig (sl (bytesOf tree) 16 48) with
  | none =>
    rw [hd] at hdig
    have hdig' : NCV_Reference.digest tree 16#usize = ok (core.result.Result.Err ()) := hdig
    refine ⟨core.result.Result.Err (), ?_, ?_⟩
    · unfold zT4
      simp only [hdig', bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, core.convert.FromSame]
      try rfl
    · rw [S4_none K0 (bytesOf b) ML (bytesOf tree) nli.val (by exact hd)]
      exact lcmp_nn
  | some val =>
    rw [hd] at hdig
    have hdig' : NCV_Reference.digest tree 16#usize = ok (core.result.Result.Ok val) := hdig
    obtain ⟨r, hr, hc⟩ := sim5 b hb master ML hM tree htr nli val
    refine ⟨r, ?_, ?_⟩
    · unfold zT4
      simp only [hdig', bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
      exact hr
    · rw [S4_some K0 (bytesOf b) ML (bytesOf tree) nli.val val (by exact hd)]
      exact hc

#print axioms sim4

/-! ### sim3 -/

theorem sim3 (b : Slice U8) (hb : b.val.length = 768) (master : Array U8 32#usize)
    (ML : List UInt8) (hM : master.val.map bt = ML) (tree : Slice U8)
    (htr : tree.val = b.val.drop 80) :
    ∃ r, zT3 b (g b 5) master tree = ok r ∧
      LCmp (S3 K0 (bytesOf b) ML (bytesOf tree)) r := by
  have v8 : (8#usize).val = 8 := by simp
  have hs : (8#usize).val + 8 ≤ tree.val.length := by
    rw [htr, List.length_drop, v8]; omega
  obtain ⟨w, hw, hwv⟩ := word64_eq tree 8#usize hs
  have hwv' : w.val = le (sl (bytesOf tree) 8 16) := by
    first | (rw [hwv, v8]; rfl) | rw [hwv, v8]
  have hgt : (1048576#u64 < w) ↔ 1048576 < w.val := by
    constructor <;> intro h <;> scalar_tac
  by_cases hc : 1048576 < w.val
  · refine ⟨core.result.Result.Err (), ?_, ?_⟩
    · unfold zT3
      simp only [hw, bind_tc_ok, hgt.2 hc, if_true]
      try rfl
    · rw [S3_bad K0 (bytesOf b) ML (bytesOf tree) (by show 1048576 < _; omega)]
      exact lcmp_nn
  · have hn : ¬ (1048576#u64 < w) := fun h => hc (hgt.1 h)
    obtain ⟨r, hr, hcm⟩ := sim4 b hb master ML hM tree htr w
    refine ⟨r, ?_, ?_⟩
    · unfold zT3
      simp only [hw, bind_tc_ok, hn, if_false]
      exact hr
    · rw [S3_ok K0 (bytesOf b) ML (bytesOf tree) (by show ¬ 1048576 < _; omega), ← hwv']
      exact hcm

#print axioms sim3

/-! ### tree guards: TreeOK and the reference side -/

def TreeOK (tree : Slice U8) : Prop :=
  slg tree.val 0 4 = tmag ∧ g tree 4 = 1#u8 ∧ g tree 5 = 20#u8 ∧ g tree 6 = 3#u8 ∧
    g tree 7 = 1#u8

theorem treeBad_false_iff (tree : Slice U8) : treeBad K0 (bytesOf tree) = false ↔ TreeOK tree := by
  have a1 : (sl (bytesOf tree) 0 4 != K0.treeStateMagic) = false ↔ slg tree.val 0 4 = tmag := by
    rw [sl_slg]; exact bne_blit _ _ _ lit_tmagic
  have a2 : (at' (bytesOf tree) 4 != K0.treeStateVersion) = false ↔ g tree 4 = 1#u8 := by
    rw [at_g]; exact bne_bt _ _ _ (by first | rfl | decide | simp [bt, K0])
  have a3 : (at' (bytesOf tree) 5 != UInt8.ofNat K0.treeDepth) = false ↔ g tree 5 = 20#u8 := by
    rw [at_g]; exact bne_bt _ _ _ (by first | rfl | decide | simp [bt, K0])
  have a4 : (at' (bytesOf tree) 6 != K0.treeHashVersion) = false ↔ g tree 6 = 3#u8 := by
    rw [at_g]; exact bne_bt _ _ _ (by first | rfl | decide | simp [bt, K0])
  have a5 : (at' (bytesOf tree) 7 != K0.digestEncodingVersion) = false ↔ g tree 7 = 1#u8 := by
    rw [at_g]; exact bne_bt _ _ _ (by first | rfl | decide | simp [bt, K0])
  unfold treeBad TreeOK
  simp only [Bool.or_eq_false_iff, a1, a2, a3, a4, a5, and_assoc]

#print axioms treeBad_false_iff

theorem tree_prep (tree : Slice U8) (hlen : tree.val.length = 688) :
    ∃ s : Slice U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) tree
        { «end» := 4#usize } = ok s ∧
      NCV_Reference.equal s (Array.to_slice (Array.make 4#usize [ 65#u8, 83#u8, 80#u8, 84#u8 ])) =
        ok (decide (slg tree.val 0 4 = tmag)) ∧
      tree.index_usize 4#usize = ok (g tree 4) ∧ tree.index_usize 5#usize = ok (g tree 5) ∧
      tree.index_usize 6#usize = ok (g tree 6) ∧ tree.index_usize 7#usize = ok (g tree 7) := by
  have v4 : (4#usize).val = 4 := by simp
  have v5 : (5#usize).val = 5 := by simp
  have v6 : (6#usize).val = 6 := by simp
  have v7 : (7#usize).val = 7 := by simp
  obtain ⟨s, hs, hsv⟩ := idx_to tree 4#usize (by rw [v4]; omega)
  rw [v4] at hsv
  have g4 := idx_g tree 4#usize (by rw [v4]; omega)
  have g5 := idx_g tree 5#usize (by rw [v5]; omega)
  have g6 := idx_g tree 6#usize (by rw [v6]; omega)
  have g7 := idx_g tree 7#usize (by rw [v7]; omega)
  rw [v4] at g4
  rw [v5] at g5
  rw [v6] at g6
  rw [v7] at g7
  have e1 : NCV_Reference.equal s (Array.to_slice (Array.make 4#usize [ 65#u8, 83#u8, 80#u8, 84#u8 ])) =
      ok (decide (slg tree.val 0 4 = tmag)) := by
    rw [equal_eq, hsv]; rfl
  exact ⟨s, hs, e1, g4, g5, g6, g7⟩

theorem ref_tree_bad (b : Slice U8) (i2 : U8) (master : Array U8 32#usize) (tree : Slice U8)
    (hlen : tree.val.length = 688) (h : ¬ TreeOK tree) :
    zTc b i2 master tree = ok (core.result.Result.Err ()) := by
  unfold TreeOK at h
  obtain ⟨s, hs, e1, g4, g5, g6, g7⟩ := tree_prep tree hlen
  by_cases p1 : slg tree.val 0 4 = tmag
  swap
  · have d1 : decide (slg tree.val 0 4 = tmag) = false := by simp [p1]
    unfold zTc
    simp only [Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, d1]
  have d1t : decide (slg tree.val 0 4 = tmag) = true := by simp [p1]
  by_cases p2 : g tree 4 = 1#u8
  swap
  · have n2 : (g tree 4 != 1#u8) = true := bne_iff_ne.2 p2
    unfold zTc
    simp only [Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, d1t, if_true, g4, n2]
  by_cases p3 : g tree 5 = 20#u8
  swap
  · have n3 : (g tree 5 != 20#u8) = true := bne_iff_ne.2 p3
    unfold zTc
    simp only [Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, d1t, if_true, g4, g5,
      bne_eq_false_iff_eq.2 p2, n3]
  by_cases p4 : g tree 6 = 3#u8
  swap
  · have n4 : (g tree 6 != 3#u8) = true := bne_iff_ne.2 p4
    unfold zTc
    simp only [Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, d1t, if_true, g4, g5, g6,
      bne_eq_false_iff_eq.2 p2, bne_eq_false_iff_eq.2 p3, n4]
  have p5 : g tree 7 ≠ 1#u8 := fun hh => h ⟨p1, p2, p3, p4, hh⟩
  have n5 : (g tree 7 != 1#u8) = true := bne_iff_ne.2 p5
  unfold zTc
  simp only [Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, d1t, if_true, g4, g5, g6, g7,
    bne_eq_false_iff_eq.2 p2, bne_eq_false_iff_eq.2 p3, bne_eq_false_iff_eq.2 p4, n5]

theorem ref_tree_ok (b : Slice U8) (i2 : U8) (master : Array U8 32#usize) (tree : Slice U8)
    (hlen : tree.val.length = 688) (h : TreeOK tree) :
    zTc b i2 master tree = zT3 b i2 master tree := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := h
  obtain ⟨s, hs, e1, g4, g5, g6, g7⟩ := tree_prep tree hlen
  have d1t : decide (slg tree.val 0 4 = tmag) = true := by simp [p1]
  unfold zTc
  simp only [Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, d1t, if_true, g4, g5, g6, g7,
    bne_eq_false_iff_eq.2 p2, bne_eq_false_iff_eq.2 p3, bne_eq_false_iff_eq.2 p4,
    bne_eq_false_iff_eq.2 p5]

#print axioms ref_tree_bad
#print axioms ref_tree_ok

/-! ### sim1 -/

theorem sim1 (b : Slice U8) (hb : b.val.length = 768) (master : Array U8 32#usize)
    (ML : List UInt8) (hM : master.val.map bt = ML) :
    ∃ r, zT1 b (g b 5) master = ok r ∧ LCmp (S2 K0 (bytesOf b) ML) r := by
  have v80 : (80#usize).val = 80 := by simp
  obtain ⟨tree, ht, htr⟩ := idx_from b 80#usize (by rw [v80]; omega)
  rw [v80] at htr
  have hlen : tree.val.length = 688 := by rw [htr, List.length_drop]; omega
  have hTb : (bytesOf b).drop K0.headerBytes = bytesOf tree := by
    show (bytesOf b).drop 80 = _
    unfold bytesOf
    rw [htr]
    first | exact (List.map_drop _ _ _).symm | simp [List.map_drop]
  have hz1 : zT1 b (g b 5) master = zTc b (g b 5) master tree := by
    unfold zT1
    simp only [ht, bind_tc_ok]
  by_cases hT : TreeOK tree
  · obtain ⟨r, hr, hc⟩ := sim3 b hb master ML hM tree htr
    have hbad := (treeBad_false_iff tree).2 hT
    refine ⟨r, ?_, ?_⟩
    · rw [hz1, ref_tree_ok b (g b 5) master tree hlen hT]
      exact hr
    · rw [S2_ok K0 (bytesOf b) ML (by rw [hTb]; exact hbad), hTb]
      exact hc
  · have hbad : treeBad K0 (bytesOf tree) = true := by
      cases hh : treeBad K0 (bytesOf tree)
      · exact absurd ((treeBad_false_iff tree).1 hh) hT
      · rfl
    refine ⟨core.result.Result.Err (), ?_, ?_⟩
    · rw [hz1]
      exact ref_tree_bad b (g b 5) master tree hlen hT
    · rw [S2_bad K0 (bytesOf b) ML (by rw [hTb]; exact hbad)]
      exact lcmp_nn

#print axioms sim1

/-! ### the master zero test, the pass-through from the header, and the composition -/

theorem zs_iff (m : List U8) (hm : m.length = 32) : Zs m ↔ m.map bt = List.replicate 32 0 := by
  constructor
  · intro h
    have hall : ∀ x ∈ m.map bt, x = (0 : UInt8) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      rw [h y hy, bt_zero]
    first
      | exact List.eq_replicate_iff.2 ⟨by simp [hm], hall⟩
      | exact List.eq_replicate.2 ⟨by simp [hm], hall⟩
  · intro h x hx
    have hm' : bt x ∈ m.map bt := List.mem_map.2 ⟨x, hx, rfl⟩
    rw [h] at hm'
    have h0 := List.eq_of_mem_replicate hm'
    exact bt_inj x 0#u8 (h0.trans bt_zero.symm)

theorem ref_pass (b : Slice U8) (h : HdrOK b) :
    NCV_Reference.decode_lane_ref b =
      (do let master ← NCV_Reference.bytes32 b 40#usize; zT0 b (g b 5) master) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := h
  have hl := hl_eq b p0
  have v4 : (4#usize).val = 4 := by simp
  have v5 : (5#usize).val = 5 := by simp
  have v6 : (6#usize).val = 6 := by simp
  have v7 : (7#usize).val = 7 := by simp
  have v8 : (8#usize).val = 8 := by simp
  have v40 : (40#usize).val = 40 := by simp
  have v73 : (73#usize).val = 73 := by simp
  have v80 : (80#usize).val = 80 := by simp
  obtain ⟨s, hs, hsv⟩ := idx_to b 4#usize (by rw [v4]; omega)
  rw [v4] at hsv
  have g4 := idx_g b 4#usize (by rw [v4]; omega)
  have g5 := idx_g b 5#usize (by rw [v5]; omega)
  have g6 := idx_g b 6#usize (by rw [v6]; omega)
  have g7 := idx_g b 7#usize (by rw [v7]; omega)
  rw [v4] at g4
  rw [v5] at g5
  rw [v6] at g6
  rw [v7] at g7
  have e1 : NCV_Reference.equal s (Array.to_slice (Array.make 4#usize [65#u8, 83#u8, 76#u8, 56#u8])) =
      ok (decide (slg b.val 0 4 = mag)) := by
    rw [equal_eq, hsv]; rfl
  have d1t : decide (slg b.val 0 4 = mag) = true := by simp [p1]
  obtain ⟨s2, hs2, hs2v⟩ := idx_range b 8#usize 40#usize (by rw [v8, v40]; omega) (by rw [v40]; omega)
  rw [v8, v40] at hs2v
  have e2 : NCV_Reference.equal s2 (Array.to_slice NCV_Reference.BINDING) =
      ok (decide (slg b.val 8 40 = NCV_Reference.BINDING.val)) := by
    rw [equal_eq, hs2v]; rfl
  obtain ⟨s4, hs4, hs4v⟩ := idx_range b 73#usize 80#usize (by rw [v73, v80]; omega) (by rw [v80]; omega)
  rw [v73, v80] at hs4v
  have z4 : NCV_Reference.zero s4 = ok (decide (Zs (slg b.val 73 80))) := by
    rw [zero_eq, hs4v]; rfl
  have d4t : decide (Zs (slg b.val 73 80)) = true := by simp [p7]
  have d2 : decide (slg b.val 8 40 = NCV_Reference.BINDING.val) = true := by simp [p6]
  have n3 : ¬ g b 5 ≥ 8#u8 := by scalar_tac
  unfold NCV_Reference.decode_lane_ref
  simp only [hl, Bool.false_eq_true, if_false, bind_tc_ok, hs, lift, e1, d1t, if_true, g4, g5, g6, g7,
    bne_eq_false_iff_eq.2 p2, n3, bne_eq_false_iff_eq.2 p4, bne_eq_false_iff_eq.2 p5, hs2, e2, d2,
    hs4, z4, d4t]
  try rfl

#print axioms ref_pass

/-- THE EQUALITY: on every input the reference returns, and the transcription agrees with it. -/
theorem decode_lane_ref_eq (b : Slice U8) :
    ∃ r, NCV_Reference.decode_lane_ref b = ok r ∧ LCmp (decodeLane K0 (bytesOf b)) r := by
  by_cases h : HdrOK b
  · have hb : b.val.length = 768 := h.1
    rw [dl_ok K0 (bytesOf b) ((hdrBad_false_iff b).2 h)]
    have v40 : (40#usize).val = 40 := by simp
    obtain ⟨master, hm, hmv⟩ := bytes32_eq b 40#usize (by rw [v40]; omega)
    rw [v40] at hmv
    have hM : master.val.map bt = sl (bytesOf b) 40 72 := by
      first | (rw [hmv, sl_slg]; rfl) | rw [hmv, sl_slg]
    have hmlen : master.val.length = 32 := by
      have := master.property; simpa using this
    have hz0 : NCV_Reference.zero (Array.to_slice master) = ok (decide (Zs master.val)) :=
      zero_eq _
    have hrp : NCV_Reference.decode_lane_ref b = zT0 b (g b 5) master := by
      rw [ref_pass b h]
      simp only [hm, bind_tc_ok]
    by_cases hzm : Zs master.val
    · have hz1 : NCV_Reference.zero (Array.to_slice master) = ok true := by
        rw [hz0]; simp [hzm]
      have hbeq : (sl (bytesOf b) 40 72 == List.replicate 32 0) = true :=
        beq_iff_eq.2 (by rw [← hM]; exact (zs_iff _ hmlen).1 hzm)
      refine ⟨core.result.Result.Err (), ?_, ?_⟩
      · rw [hrp]
        unfold zT0
        simp only [lift, bind_tc_ok, hz1, if_true]
      · rw [S1_bad K0 (bytesOf b) hbeq]
        exact lcmp_nn
    · have hz1 : NCV_Reference.zero (Array.to_slice master) = ok false := by
        rw [hz0]; simp [hzm]
      have hbeq : (sl (bytesOf b) 40 72 == List.replicate 32 0) = false := by
        cases hh : (sl (bytesOf b) 40 72 == List.replicate 32 0)
        · rfl
        · exact absurd ((zs_iff _ hmlen).2 (by rw [hM]; exact beq_iff_eq.1 hh)) hzm
      obtain ⟨r, hr, hc⟩ := sim1 b hb master (sl (bytesOf b) 40 72) hM
      refine ⟨r, ?_, ?_⟩
      · rw [hrp]
        unfold zT0
        simp only [lift, bind_tc_ok, hz1, Bool.false_eq_true, if_false]
        exact hr
      · rw [S1_ok K0 (bytesOf b) hbeq]
        exact hc
  · have hbad : hdrBad K0 (bytesOf b) = true := by
      cases hh : hdrBad K0 (bytesOf b)
      · exact absurd ((hdrBad_false_iff b).1 hh) h
      · rfl
    refine ⟨core.result.Result.Err (), ref_hdr_bad b h, ?_⟩
    rw [dl_bad K0 (bytesOf b) hbad]
    exact lcmp_nn

#print axioms decode_lane_ref_eq

end PCVY_Op50
