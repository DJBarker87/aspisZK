import R1Z.LayoutR1PBin

/-! BINARY format (copy of `LayoutR1P2` over `Fin 2` children). The commitment layout, part 2 (DESIGN-R1-REAL §3): the Merkle index
algebra (children are unique, levels separate leaves, nodes and roots), the
pair table `fresh_or_sep`, and the opened reads with `hidden`. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.LayoutR1PBin
open R0Z.FsStatement R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1PBin

/-! ### Index algebra -/

theorem nodeIdx_ext {n n' : NodeIdx} : n = n' ↔ n.1 = n'.1 ∧ n.2.val = n'.2.val := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · obtain ⟨d, i⟩ := n
    obtain ⟨d', i'⟩ := n'
    rintro ⟨h1, h2⟩
    simp only at h1 h2
    subst h1
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
    exact Fin.ext h2

theorem qNode_inj {T T' : Fin 3} {n n' : NodeIdx} : qNode T n = qNode T' n' ↔ T = T' ∧ n = n' := by
  simp [qNode]

theorem childQ_cases (T : Fin 3) (n : NodeIdx) (j : Fin 2) :
    (n.1.val = 0 ∧ ∃ u : Fib, u.val = 2 * n.2.val + j.val ∧ childQ T n j = qLeaf T u) ∨
    (∃ n' : NodeIdx, n.1.val = n'.1.val + 1 ∧ n'.2.val = 2 * n.2.val + j.val ∧
      childQ T n j = qNode T n') := by
  obtain ⟨⟨d, hd⟩, i⟩ := n
  cases d with
  | zero => exact Or.inl ⟨rfl, _, rfl, rfl⟩
  | succ d => exact Or.inr ⟨_, rfl, rfl, rfl⟩

theorem childQ_ne_bind (T : Fin 3) (n : NodeIdx) (j : Fin 2) (b : Fin 2) : childQ T n j ≠ qBind b := by
  rcases childQ_cases T n j with ⟨_, u, _, h⟩ | ⟨n', _, _, h⟩ <;> rw [h] <;> simp [qLeaf, qNode, qBind]

theorem childQ_ne_seed (T : Fin 3) (n : NodeIdx) (j : Fin 2) (i : Fin 3) : childQ T n j ≠ qSeed i := by
  rcases childQ_cases T n j with ⟨_, u, _, h⟩ | ⟨n', _, _, h⟩ <;> rw [h] <;> simp [qLeaf, qNode, qSeed]

theorem childQ_ne_salt (T : Fin 3) (n : NodeIdx) (j : Fin 2) (T' : Fin 3) (u : Fib) :
    childQ T n j ≠ qSalt T' u := by
  rcases childQ_cases T n j with ⟨_, v, _, h⟩ | ⟨n', _, _, h⟩ <;> rw [h] <;> simp [qLeaf, qNode, qSalt]

theorem childQ_eq_leaf (T : Fin 3) (n : NodeIdx) (j : Fin 2) (T' : Fin 3) (u : Fib)
    (h : childQ T n j = qLeaf T' u) : T = T' ∧ n.1.val = 0 ∧ u.val = 2 * n.2.val + j.val := by
  rcases childQ_cases T n j with ⟨h0, v, hv, e⟩ | ⟨n', _, _, e⟩
  · rw [e] at h
    simp only [qLeaf, Sum.inr.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, h0, hv⟩
  · rw [e] at h
    simp [qLeaf, qNode] at h

theorem childQ_eq_node (T : Fin 3) (n : NodeIdx) (j : Fin 2) (T' : Fin 3) (m : NodeIdx)
    (h : childQ T n j = qNode T' m) :
    T = T' ∧ n.1.val = m.1.val + 1 ∧ m.2.val = 2 * n.2.val + j.val := by
  rcases childQ_cases T n j with ⟨_, v, _, e⟩ | ⟨n', h1, h2, e⟩
  · rw [e] at h
    simp [qLeaf, qNode] at h
  · rw [e, qNode_inj] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, h1, h2⟩

theorem childQ_inj (T T' : Fin 3) (n n' : NodeIdx) (j j' : Fin 2)
    (h : childQ T n j = childQ T' n' j') : T = T' ∧ n = n' ∧ j = j' := by
  rcases childQ_cases T' n' j' with ⟨h0, u, hu, e⟩ | ⟨m, h1, h2, e⟩
  · rw [e] at h
    obtain ⟨hT, hn0, hu'⟩ := childQ_eq_leaf T n j T' u h
    refine ⟨hT, nodeIdx_ext.mpr ⟨Fin.ext (by omega), by omega⟩, Fin.ext (by have := j.isLt; have := j'.isLt; omega)⟩
  · rw [e] at h
    obtain ⟨hT, hn1, hm⟩ := childQ_eq_node T n j T' m h
    refine ⟨hT, nodeIdx_ext.mpr ⟨Fin.ext (by omega), by have := j.isLt; have := j'.isLt; omega⟩,
      Fin.ext (by have := j.isLt; have := j'.isLt; omega)⟩

theorem childQ_ne_rootChild (T : Fin 3) (n : NodeIdx) (j : Fin 2) (T' : Fin 3) (j' : Fin 2) :
    childQ T n j ≠ rootChild T' j' := by
  intro h
  unfold rootChild at h
  obtain ⟨_, h1, _⟩ := childQ_eq_node T n j T' _ h
  have := n.1.isLt
  simp only at h1
  omega

theorem rootChild_inj (T T' : Fin 3) (j j' : Fin 2) (h : rootChild T j = rootChild T' j') :
    T = T' ∧ j = j' := by
  unfold rootChild at h
  rw [qNode_inj, nodeIdx_ext] at h
  exact ⟨h.1, Fin.ext h.2.2⟩

/-! ### Byte separation -/

theorem le32_inj (a b : ℕ) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : le32 a = le32 b) : a = b := by
  simp only [le32, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have e0 := congrArg UInt8.toNat h0
  have e1 := congrArg UInt8.toNat h1
  have e2 := congrArg UInt8.toNat h2
  have e3 := congrArg UInt8.toNat h3
  simp only [Nat.toUInt8, UInt8.toNat_ofNat] at e0 e1 e2 e3
  norm_num at ha hb e0 e1 e2 e3
  omega

theorem le64_inj (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : le64 a = le64 b) : a = b := by
  simp only [le64, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e0 := congrArg UInt8.toNat h0
  have e1 := congrArg UInt8.toNat h1
  have e2 := congrArg UInt8.toNat h2
  have e3 := congrArg UInt8.toNat h3
  have e4 := congrArg UInt8.toNat h4
  have e5 := congrArg UInt8.toNat h5
  have e6 := congrArg UInt8.toNat h6
  have e7 := congrArg UInt8.toNat h7
  simp only [Nat.toUInt8, UInt8.toNat_ofNat] at e0 e1 e2 e3 e4 e5 e6 e7
  norm_num at ha hb e0 e1 e2 e3 e4 e5 e6 e7
  omega

theorem treeTag_inj (T T' : Fin 3) (h : treeTag T = treeTag T') : T = T' := by
  revert h
  revert T T'
  decide

theorem cancel_mid (p x x' y y' : List UInt8) (hl : x.length = x'.length)
    (h : p ++ x ++ y = p ++ x' ++ y') : x = x' := by
  rw [List.append_assoc, List.append_assoc] at h
  exact (List.append_inj (List.append_cancel_left h) hl).1

section Sep
variable {E₁ E₂ : ℕ}

theorem sep_seed (pub : List UInt8) (vtag : UInt8) (lv : Fin 3 → Fib → List UInt8) (sec : SecP)
    (d : OracleAnswer) (rest : RIdx → OracleAnswer) :
    gram (E₁ := E₁) (E₂ := E₂) pub vtag lv sec d rest (.inr (.inr (qSeed 0))) ≠
      gram (E₁ := E₁) (E₂ := E₂) pub vtag lv sec d rest (.inr (.inr (qSeed 1))) := by
  intro h
  have h' := congrArg (fun l : List UInt8 => l[18]?) h
  simp only [gram, qSeed, show (0 : Fin 3).val = 0 from rfl, show (1 : Fin 3).val = 1 from rfl,
    if_true, show ¬ ((1 : ℕ) = 0) from by decide, if_false, List.append_assoc] at h'
  rw [List.getElem?_append_left (by decide), List.getElem?_append_left (by decide)] at h'
  exact absurd h' (by decide)

theorem sep_salt (pub : List UInt8) (vtag : UInt8) (lv : Fin 3 → Fib → List UInt8) (sec : SecP)
    (d : OracleAnswer) (rest : RIdx → OracleAnswer) (T T' : Fin 3) (u u' : Fib)
    (hne : (T, u) ≠ (T', u')) :
    gram (E₁ := E₁) (E₂ := E₂) pub vtag lv sec d rest (.inr (.inr (qSalt T u))) ≠
      gram (E₁ := E₁) (E₂ := E₂) pub vtag lv sec d rest (.inr (.inr (qSalt T' u'))) := by
  intro h
  simp only [gram, qSalt] at h
  have e : ∀ (TT : Fin 3) (uu : Fib), dLeafSalt ++ ans (rest (qBind 1)) ++ ans (sec 0).1 ++ [treeTag TT] ++
      le32 uu.val ++ ans (sec 2).1 =
      (dLeafSalt ++ ans (rest (qBind 1)) ++ ans (sec 0).1) ++ ([treeTag TT] ++ le32 uu.val) ++ ans (sec 2).1 := by
    intro TT uu
    simp only [List.append_assoc]
  rw [e, e] at h
  have hm := cancel_mid _ _ _ _ _ (by simp [le32]) h
  simp only [List.singleton_append, List.cons.injEq] at hm
  have hT := treeTag_inj T T' hm.1
  have hu := le32_inj u.val u'.val (lt_of_lt_of_le u.isLt (by norm_num))
    (lt_of_lt_of_le u'.isLt (by norm_num)) hm.2
  exact hne (by rw [hT, Fin.ext hu])

theorem sep_exp1 (pub : List UInt8) (vtag : UInt8) (lv : Fin 3 → Fib → List UInt8) (sec : SecP)
    (d : OracleAnswer) (rest : RIdx → OracleAnswer) (hE : E₁ ≤ 2 ^ 64) (c c' : Fin E₁) (hne : c ≠ c') :
    gram (E₁ := E₁) (E₂ := E₂) pub vtag lv sec d rest (.inr (.inl (.inl c))) ≠
      gram (E₁ := E₁) (E₂ := E₂) pub vtag lv sec d rest (.inr (.inl (.inl c'))) := by
  intro h
  simp only [gram] at h
  exact hne (Fin.ext (le64_inj _ _ (lt_of_lt_of_le c.isLt hE) (lt_of_lt_of_le c'.isLt hE)
    (List.append_cancel_left h)))

theorem sep_exp2 (pub : List UInt8) (vtag : UInt8) (lv : Fin 3 → Fib → List UInt8) (sec : SecP)
    (d : OracleAnswer) (rest : RIdx → OracleAnswer) (hE : E₂ ≤ 2 ^ 64) (c c' : Fin E₂) (hne : c ≠ c') :
    gram (E₁ := E₁) (E₂ := E₂) pub vtag lv sec d rest (.inr (.inl (.inr c))) ≠
      gram (E₁ := E₁) (E₂ := E₂) pub vtag lv sec d rest (.inr (.inl (.inr c'))) := by
  intro h
  simp only [gram] at h
  exact hne (Fin.ext (le64_inj _ _ (lt_of_lt_of_le c.isLt hE) (lt_of_lt_of_le c'.isLt hE)
    (List.append_cancel_left h)))

end Sep

#print axioms nodeIdx_ext
#print axioms childQ_inj
#print axioms childQ_ne_rootChild
#print axioms le32_inj
#print axioms le64_inj
#print axioms treeTag_inj
#print axioms sep_seed
#print axioms sep_salt
#print axioms sep_exp1
#print axioms sep_exp2
#print axioms qNode_inj
#print axioms childQ_cases
#print axioms childQ_ne_bind
#print axioms childQ_ne_seed
#print axioms childQ_ne_salt
#print axioms childQ_eq_leaf
#print axioms childQ_eq_node
#print axioms rootChild_inj
#print axioms cancel_mid
end R1Z.LayoutR1PBin
