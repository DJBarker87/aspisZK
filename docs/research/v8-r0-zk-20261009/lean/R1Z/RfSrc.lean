import R0Z.PureRounds

/-! D49.4 C2: RF-src (zf1/DESIGN-P-CERT.txt §0 "Sources", §2.3), Lean side.

The checker's source vectors are named by a lane and a source index.  Here
they are defined as Lean objects exactly as the Rust builds them, and their
membership facts are proved.

* Mask-lane sources (z4/z9.rs:957-1027, `Lanes::raw/row_of/bal`): lane `li`,
  index `i` is row `r = i / per_row + 1`, tower limb `k = i % per_row`
  (`per_row` = 1 for the mask-only lanes m0..m9, 4 for G and D).  As a mask
  tape this is the unit tape at `(c, r)` (mask-only), `(r, k)` in the G slot,
  or `(r, k)` in the D slot.  `pureTrace_*Src` prove that the resulting trace
  word is the Rust balanced word `x_k·e_r` if `r` is copy-active and
  `x_k·(e_r − e_0)` if it is copy-inactive (`balWord 0 r x_k`), in its own
  lane, and zero in every other lane.
* `gSrc_mem_Gonly`: the G sources lie in `PredicateR1.Gonly` (stated through
  its body, so that `PredicateR1` is not imported here).
* C1 lift sources (z9c.rs:224-246, `lift_src`/`lift_members`, c < 16): row
  `r ≠ 1023` eligible for lane `c`; the lane word is `e_r − [r inactive] e_1023`
  (`balWord 1023 r 1`).  `c1Src_mem_Vsem`: it lies in `PredicateR1.Vsem c`.
* H1 lift sources (same lines, c = 16): copy-inactive row `r ≥ 1`, limb `k`;
  the lane word is `x_k (e_r − e_0)`.  `h1Src_mem_Ph1`: it lies in
  `PredicateR1.Ph1 B`.

The per-entry side conditions (eligibility, inactivity, `r ≠ 0`, `r ≠ 1023`)
are decidable facts about one index that the checker tests; that the Rust
`eligible`/`inactive` tables compute the Lean predicates is a C3 item. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.RfSrc

open R0P R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.PureRounds

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### The balanced word -/

/-- The Rust balanced source word: `x` at row `r`, and `−x` at the dependent
row `d` when `r` is copy-inactive. -/
def balWord (d r : Fin 1024) (x : K) : Fin 1024 → K := fun s =>
  if s = r then x else if s = d ∧ r ∈ copyInactiveRows then -x else 0

/-- Balancing a single-row word at a different dependent row. -/
theorem balance_single (d r : Fin 1024) (hr : r ≠ d) (x : K) :
    balance d (fun s => if s = r then x else 0) = balWord d r x := by
  funext s
  unfold balance balWord
  by_cases hs : s = d
  · subst hs
    have hsr : ¬ s = r := fun h => hr h.symm
    rw [if_pos rfl, if_neg hsr, Finset.sum_ite_eq']
    by_cases hm : r ∈ copyInactiveRows
    · have hm' : r ∈ copyInactiveRows.erase s := Finset.mem_erase.2 ⟨hr, hm⟩
      rw [if_pos hm', if_pos ⟨rfl, hm⟩]
    · have hm' : r ∉ copyInactiveRows.erase s := fun h => hm (Finset.mem_of_mem_erase h)
      rw [if_neg hm', if_neg (fun h => hm h.2), neg_zero]
  · rw [if_neg hs]
    by_cases hsr : s = r
    · dsimp only
      rw [if_pos hsr, if_pos hsr]
    · dsimp only
      rw [if_neg hsr, if_neg hsr, if_neg (fun h => hs h.1)]

/-! ### Mask-lane sources (tapes) -/

/-- Mask-only lane `c`, row `r` (Rust `Lanes::raw`, li = c < 10). -/
def maskOnlySrc (c : Fin 10) (r : Fin 1024) : M K F :=
  (fun p => if p = (c, r) then 1 else 0, 0, 0)

/-- G lane, row `r`, tower limb `k` (Rust `Lanes::raw`, li = 10). -/
def gSrc (r : Fin 1024) (k : Fin 4) : M K F :=
  (0, fun p => if p = (r, k) then 1 else 0, 0)

/-- D lane, row `r`, tower limb `k` (Rust `Lanes::raw`, li = 11). -/
def dSrc (r : Fin 1024) (k : Fin 4) : M K F :=
  (0, 0, fun p => if p = (r, k) then 1 else 0)

/-- Rust `row_of` for a mask-only lane: source `i` is row `i + 1`. -/
def maskOnlyRow (i : Fin 1023) : Fin 1024 := ⟨i.val + 1, by omega⟩

/-- Rust `row_of` for a K₄ lane: source `i` is row `i/4 + 1`, limb `i % 4`. -/
def extRow (i : Fin 4092) : Fin 1024 := ⟨i.val / 4 + 1, by omega⟩

def extLimb (i : Fin 4092) : Fin 4 := ⟨i.val % 4, by omega⟩

theorem maskOnlyRow_ne_zero (i : Fin 1023) : maskOnlyRow i ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp only [maskOnlyRow, Fin.val_zero] at this
  omega

theorem extRow_ne_zero (i : Fin 4092) : extRow i ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp only [extRow, Fin.val_zero] at this
  omega

/-- The F-valued indicator, read in `K`. -/
theorem coe_indicator {α : Type} [DecidableEq α] (a b : α) :
    (((if a = b then 1 else 0 : F)) : K) = if a = b then 1 else 0 := by
  split_ifs <;> simp

/-- `pack4` of a one-limb indicator is the tower basis element. -/
theorem pack4_single (B : PackBasis F) (k : Fin 4) :
    pack4 B (fun l : Fin 4 => if l = k then (1 : K) else 0) = R0P.Mask.towerBasis B k := by
  fin_cases k <;> simp [pack4, R0P.Mask.towerBasis]

/-- Mask-only source trace word. -/
theorem pureTrace_maskOnlySrc (B : PackBasis F) (c : Fin 10) (r : Fin 1024) (hr : r ≠ 0) :
    pureTrace B (maskOnlySrc (K := K) (F := F) c r) ⟨16 + c.val, by omega⟩ =
      balWord 0 r 1 := by
  rw [pureTrace_maskOnly_word, ← balance_single 0 r hr]
  unfold maskOnlyColumns
  congr 1
  funext s
  change ((if ((c, s) : Fin 10 × Fin 1024) = (c, r) then 1 else 0 : F) : K) = _
  rw [coe_indicator]
  by_cases h : s = r
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun e => h (Prod.ext_iff.1 e).2), if_neg h]

theorem pureTrace_maskOnlySrc_other (B : PackBasis F) (c : Fin 10) (r : Fin 1024)
    (l : Fin 29) (hl : l ≠ ⟨16 + c.val, by omega⟩) :
    pureTrace B (maskOnlySrc (K := K) (F := F) c r) l = 0 := by
  refine pureTrace_maskOnly_support B _ c ?_ rfl rfl l hl
  intro i hi s
  change (if ((i, s) : Fin 10 × Fin 1024) = (c, r) then 1 else 0 : F) = 0
  rw [if_neg (fun e => hi (Prod.ext_iff.1 e).1)]

/-- G source trace word (lane 27). -/
theorem pureTrace_gSrc (B : PackBasis F) (r : Fin 1024) (k : Fin 4) (hr : r ≠ 0) :
    pureTrace B (gSrc (K := K) (F := F) r k) 27 = balWord 0 r (R0P.Mask.towerBasis B k) := by
  rw [pureTrace_G_word, ← balance_single 0 r hr]
  congr 1
  funext s
  change pack4 B (fun l => ((if ((s, l) : Fin 1024 × Fin 4) = (r, k) then 1 else 0 : F) : K)) = _
  simp only [coe_indicator]
  by_cases h : s = r
  · subst h
    rw [if_pos rfl, ← pack4_single B k]
    congr 1
    funext l
    by_cases hl : l = k
    · rw [if_pos (by rw [hl]), if_pos hl]
    · rw [if_neg (fun e => hl (Prod.ext_iff.1 e).2), if_neg hl]
  · rw [if_neg h]
    simp [pack4, Prod.ext_iff, h]

theorem pureTrace_gSrc_other (B : PackBasis F) (r : Fin 1024) (k : Fin 4) (l : Fin 29)
    (hl : l ≠ 27) : pureTrace B (gSrc (K := K) (F := F) r k) l = 0 :=
  pureTrace_G_support B _ rfl rfl l hl

/-- D source trace word (lane 28). -/
theorem pureTrace_dSrc (B : PackBasis F) (r : Fin 1024) (k : Fin 4) (hr : r ≠ 0) :
    pureTrace B (dSrc (K := K) (F := F) r k) 28 = balWord 0 r (R0P.Mask.towerBasis B k) := by
  rw [pureTrace_D_word, ← balance_single 0 r hr]
  unfold dWord
  congr 1
  funext s
  change pack4 B (fun l => ((if ((s, l) : Fin 1024 × Fin 4) = (r, k) then 1 else 0 : F) : K)) = _
  simp only [coe_indicator]
  by_cases h : s = r
  · subst h
    rw [if_pos rfl, ← pack4_single B k]
    congr 1
    funext l
    by_cases hl : l = k
    · rw [if_pos (by rw [hl]), if_pos hl]
    · rw [if_neg (fun e => hl (Prod.ext_iff.1 e).2), if_neg hl]
  · rw [if_neg h]
    simp [pack4, Prod.ext_iff, h]

theorem pureTrace_dSrc_other (B : PackBasis F) (r : Fin 1024) (k : Fin 4) (l : Fin 29)
    (hl : l ≠ 28) : pureTrace B (dSrc (K := K) (F := F) r k) l = 0 :=
  pureTrace_D_support B _ rfl rfl l hl

/-! ### RF-src: membership -/

/-- The G sources lie in `PredicateR1.Gonly` (its body). -/
theorem gSrc_mem_Gonly (r : Fin 1024) (k : Fin 4) :
    gSrc (K := K) (F := F) r k ∈
      LinearMap.ker (LinearMap.fst F (Fin 10 × Fin 1024 → F) (ExtTape F × ExtTape F)) ⊓
        LinearMap.ker ((LinearMap.snd F (ExtTape F) (ExtTape F)).comp
          (LinearMap.snd F (Fin 10 × Fin 1024 → F) (ExtTape F × ExtTape F))) :=
  Submodule.mem_inf.2 ⟨rfl, rfl⟩

/-- C1 lift source of lane `c` at row `r` (z9c.rs:224-228). -/
def c1Src (r : Fin 1024) : Fin 1024 → K := balWord 1023 r 1

/-- The C1 lift sources lie in `PredicateR1.Vsem c` (its body). -/
theorem c1Src_mem_Vsem (c : Fin 29) (hc : c.val < 16) (r : Fin 1024) (he : eligible c r)
    (hr : r ≠ 1023) :
    c1Src (K := K) r ∈ LinearMap.range ((LinearMap.proj c : Trace K →ₗ[F] (Fin 1024 → K)).comp
      (R0Z.JointTrace.eligibleLinear (K := K) (F := F))) := by
  let cell : EligibleCell := ⟨(c, r), he⟩
  refine ⟨fun e => if e = cell then 1 else 0, ?_⟩
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  have hw : (fun s' => semanticNoise (Sum.elim (fun e : EligibleCell => if e = cell then (1 : F) else 0) 0) c s') =
      fun s' => if s' = r then (1 : K) else 0 := by
    funext s'
    unfold semanticNoise
    by_cases hs : s' = r
    · rw [hs, dif_pos he, if_pos rfl]
      show (((if cell = cell then 1 else 0 : F)) : K) = 1
      simp
    · rw [if_neg hs]
      by_cases he' : eligible c s'
      · rw [dif_pos he']
        have hne : ¬ ((⟨(c, s'), he'⟩ : EligibleCell) = cell) :=
          fun e => hs (Prod.ext_iff.1 (congrArg Subtype.val e)).2
        show (((if (⟨(c, s'), he'⟩ : EligibleCell) = cell then 1 else 0 : F)) : K) = 0
        simp only [if_neg hne, ZeroMemClass.coe_zero]
      · rw [dif_neg he']
  funext s
  rw [R0Z.JointTrace.eligibleLinear_apply, if_pos hc, hw, balance_single 1023 r hr, c1Src]

/-- `balanceAff` evaluated at a tape is `balance` of the evaluated family
(as in `MaskLayout.applyAff_eq_base_add`). -/
theorem balanceAff_apply (d : Fin 1024) (f : Fin 1024 → AffTape K F →ₗ[F] K) (s : Fin 1024)
    (p : AffTape K F) : balanceAff d f s p = balance d (fun u => f u p) s := by
  simp only [balanceAff, balance]
  split_ifs <;> simp only [LinearMap.neg_apply, LinearMap.sum_apply]

/-- H1 lift source at copy-inactive row `r`, limb `k` (z9c.rs:229-233). -/
def h1Src (B : PackBasis F) (r : Fin 1024) (k : Fin 4) : Fin 1024 → K :=
  balWord 0 r (R0P.Mask.towerBasis B k)

/-- The H1 lift sources lie in `PredicateR1.Ph1 B` (its body). -/
theorem h1Src_mem_Ph1 (B : PackBasis F) (r : Fin 1024) (k : Fin 4) (hr : r ≠ 0)
    (hi : r ∈ copyInactiveRows) :
    h1Src B r k ∈ LinearMap.range ((LinearMap.proj 26 : Trace K →ₗ[F] (Fin 1024 → K)).comp
      ((R0Z.JointTrace.tapeLinear B).comp
        (inrN.comp (LinearMap.inl F (ExtTape F) (EligibleNoise K F))))) := by
  let h0 : ExtTape F := fun p => if p = (r, k) then 1 else 0
  refine ⟨h0, ?_⟩
  have hna : ¬ CopyActiveRow r := (R0Z.TerminalEligible.mem_inactive r).1 hi
  have he (s' : Fin 1024) (p : AffTape K F) :
      extensionAff B 1 s' p = pack4 B (fun limb => (p (.inr (1, s', limb)) : K)) := by
    simp only [extensionAff, readAff, pack4, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  have e0 : R0Z.JointTrace.tapeLinear B (inrN (LinearMap.inl F (ExtTape F) (EligibleNoise K F) h0)) =
      traceLinear B (aff (inrN (LinearMap.inl F (ExtTape F) (EligibleNoise K F) h0))) := by
    simp only [R0Z.JointTrace.tapeLinear, LinearMap.add_apply, LinearMap.comp_apply]
    have hz0 : (LinearMap.snd F (ExtTape F) (EligibleNoise K F))
        ((LinearMap.snd F (M K F) (N K F)) (inrN (LinearMap.inl F (ExtTape F) (EligibleNoise K F) h0))) = 0 := rfl
    rw [hz0, map_zero, zero_add]
  have hw (s' : Fin 1024) :
      (if CopyActiveRow s' then (0 : AffTape K F →ₗ[F] K) else extensionAff B 1 s')
        (aff (inrN (LinearMap.inl F (ExtTape F) (EligibleNoise K F) h0))) =
      if s' = r then R0P.Mask.towerBasis B k else 0 := by
    by_cases hs : s' = r
    · rw [hs, if_neg hna, if_pos rfl, he, ← pack4_single B k]
      show pack4 B (fun l => ((if ((r, l) : Fin 1024 × Fin 4) = (r, k) then 1 else 0 : F) : K)) = _
      simp only [coe_indicator]
      congr 1
      funext l
      by_cases hl : l = k
      · rw [if_pos (by rw [hl]), if_pos hl]
      · rw [if_neg (fun e => hl (Prod.ext_iff.1 e).2), if_neg hl]
    · rw [if_neg hs]
      by_cases ha : CopyActiveRow s'
      · rw [if_pos ha, LinearMap.zero_apply]
      · rw [if_neg ha, he]
        show pack4 B (fun l => ((if ((s', l) : Fin 1024 × Fin 4) = (r, k) then 1 else 0 : F) : K)) = 0
        simp only [coe_indicator]
        simp [pack4, Prod.ext_iff, hs]
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  rw [e0, h1Src, ← balance_single 0 r hr]
  funext s
  show balanceAff 0 (fun s => if CopyActiveRow s then 0 else extensionAff B 1 s) s
      (aff (inrN (LinearMap.inl F (ExtTape F) (EligibleNoise K F) h0))) = _
  rw [balanceAff_apply]
  have hf : (fun u => (if CopyActiveRow u then (0 : AffTape K F →ₗ[F] K) else extensionAff B 1 u)
      (aff (inrN (LinearMap.inl F (ExtTape F) (EligibleNoise K F) h0)))) =
      fun u => if u = r then R0P.Mask.towerBasis B k else 0 := funext hw
  rw [hf]

#print axioms balance_single
#print axioms maskOnlyRow_ne_zero
#print axioms extRow_ne_zero
#print axioms pack4_single
#print axioms pureTrace_maskOnlySrc
#print axioms pureTrace_maskOnlySrc_other
#print axioms pureTrace_gSrc
#print axioms pureTrace_gSrc_other
#print axioms pureTrace_dSrc
#print axioms pureTrace_dSrc_other
#print axioms gSrc_mem_Gonly
#print axioms c1Src_mem_Vsem
#print axioms balanceAff_apply
#print axioms h1Src_mem_Ph1

end R1Z.RfSrc

end
