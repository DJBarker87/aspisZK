import S9SideOneTailRootV1
import S9ConcreteQMMulAcceptedRootV1
import S9ArrayWriteScheduleRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S9SideOneMeaningRootV1
open AspisR1S9HelperP6
abbrev S := field.WideExact
abbrev Q := field.QM31
abbrev A := Array S (4#usize)
local notation "C" => AspisR1S9CurrentFieldOpsV1.Canonical
local notation "D" => AspisR1S9CurrentFieldOpsV1.decode
local notation "CQ" => S9ConcreteArithmeticAcceptedRootV1.CanonicalQ
local notation "DQ" => S9ConcreteArithmeticAcceptedRootV1.decodeQ
local notation "emb" => algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM AspisWideTower.WideExact
local notation "cell" => S9ArrayWriteScheduleRootV1.cells

private theorem read_cell (a : A) (i : Usize) (x : S)
    (hi : i.val < 4) (h : Array.index_usize a i = .ok x) :
    cell a ⟨i.val,hi⟩ = x := by
  obtain ⟨r,hr,hv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec a i (by simpa [a.property] using hi))
  have heq : r = x := Result.ok.inj (hr.symm.trans h)
  exact hv.symm.trans heq

/-- Exact accepted second-branch products, canonical written values and full
array frame, with arithmetic interpreted by the selected concrete operations. -/
theorem sideOneTail_success_exact
    (old ap1 : A) (low all first2 : S) (q4 q16 : Q) (out : A)
    (hlow : C low) (hall : C all) (hfirst2 : C first2)
    (hq4 : CQ q4) (hq16 : CQ q16)
    (hold : ∀ x, Array.index_usize old 1#usize = .ok x → C x)
    (hap1 : ∀ i x, Array.index_usize ap1 i = .ok x → C x)
    (h : S9SideOneTailRootV1.sideOneTail old ap1 low all first2 q4 q16 = .ok out) :
    ∃ (i : Usize) (last : S),
      Array.index_usize weights.PERM 3#usize = .ok i ∧
      Array.index_usize ap1 i = .ok last ∧
      C (cell out 1) ∧ C (cell out 2) ∧ C (cell out 3) ∧
      ∀ j : Fin 4, D (cell out j) =
        if j.val = 0 then D (cell old j)
        else if j.val = 1 then D (cell old 1) + D low *
          (D last * AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER)
        else if j.val = 2 then (D low * D all) * emb (DQ q4)
        else (D low * D first2) * (emb (DQ q16) * emb (DQ q4)) := by
  obtain ⟨vold,i,last,scaled,prod,added,a,pall,v2,b,pfirst,q3,v3,
      hread,hi,hlast,hscaled,hprod,hadded,ha,hpall,hv2,hb,hpfirst,hq3,hv3,hout⟩ :=
    S9SideOneTailRootV1.sideOneTail_success_children
      old ap1 low all first2 q4 q16 out h
  have hcOld := hold vold hread
  have hcLast := hap1 i last hlast
  obtain ⟨hcScaled,hdScaled⟩ := S9ConcreteArithmeticAcceptedRootV1.wideMulM31_success
    last scaled weights.QUARTER hcLast hscaled
  obtain ⟨hcProd,hdProd⟩ := S9ConcreteArithmeticAcceptedRootV1.wideMul_success
    low scaled prod hlow hcScaled hprod
  obtain ⟨hcAdded,hdAdded⟩ := S9ConcreteArithmeticAcceptedRootV1.wideAdd_success
    vold prod added hcOld hcProd hadded
  obtain ⟨hcPall,hdPall⟩ := S9ConcreteArithmeticAcceptedRootV1.wideMul_success
    low all pall hlow hall hpall
  obtain ⟨hcV2,hdV2⟩ := S9ConcreteArithmeticAcceptedRootV1.wideMulQM31_success
    pall v2 q4 hcPall hq4 hv2
  obtain ⟨hcPfirst,hdPfirst⟩ := S9ConcreteArithmeticAcceptedRootV1.wideMul_success
    low first2 pfirst hlow hfirst2 hpfirst
  obtain ⟨hcQ3,hdQ3⟩ := S9ConcreteQMMulAcceptedRootV1.qmMul_success
    q16 q4 q3 hq16 hq4 hq3
  obtain ⟨hcV3,hdV3⟩ := S9ConcreteArithmeticAcceptedRootV1.wideMulQM31_success
    pfirst v3 q3 hcPfirst hcQ3 hv3
  simp only [S9ConcreteArithmeticAcceptedRootV1.decode] at hdScaled hdProd hdAdded hdPall hdV2 hdPfirst hdV3
  have hcell1 : cell old 1 = vold := read_cell old 1#usize vold (by decide) hread
  have hcell (j : Fin 4) : cell out j =
      if j.val = 3 then v3 else if j.val = 2 then v2 else
      if j.val = 1 then added else cell old j := by
    rw [S9ArrayWriteScheduleRootV1.update_cells b out 3#usize v3 (by decide) hout j,
        S9ArrayWriteScheduleRootV1.update_cells a b 2#usize v2 (by decide) hb j,
        S9ArrayWriteScheduleRootV1.update_cells old a 1#usize added (by decide) ha j]
    rfl
  refine ⟨i,last,hi,hlast,?_,?_,?_,?_⟩
  · rw [hcell 1]; exact hcAdded
  · rw [hcell 2]; exact hcV2
  · rw [hcell 3]; exact hcV3
  · intro j
    rw [hcell j]
    change D (if j.val = 3 then v3 else if j.val = 2 then v2 else
      if j.val = 1 then added else cell old j) = _
    have hdAdded' : D added = D vold + D low *
        (D last * AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER) := by
      rw [hdAdded,hdProd,hdScaled]
    have hdV2' : D v2 = (D low * D all) * emb (DQ q4) := by
      rw [hdV2,hdPall]
    have hdV3' : D v3 = (D low * D first2) * (emb (DQ q16) * emb (DQ q4)) := by
      rw [hdV3,hdPfirst,hdQ3,map_mul]
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · simp [h0]
    · by_cases h1 : j.val = 1
      · simp [h0,h1,hdAdded',hcell1]
      · by_cases h2 : j.val = 2
        · simp [h0,h1,h2,hdV2']
        · have h3 : j.val = 3 := by omega
          simp [h0,h1,h2,h3,hdV3']

#print axioms sideOneTail_success_exact
end AspisR1.S9SideOneMeaningRootV1
