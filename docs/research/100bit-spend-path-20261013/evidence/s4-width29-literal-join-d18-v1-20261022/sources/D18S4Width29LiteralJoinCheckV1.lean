import S4LiteralCallbackValueRootV1
import AspisFormal.V6Width29CorrelatedAgreement

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1D18S4Width29LiteralJoinV1

open AspisR1FastDotsLiteralCallbackValueRootV1
open AspisR1FastDotsLiteralHeadSumRootV1
open AspisR1FastDotsTailFieldProductRootV1
open AspisR1FastDotsTailLiteralProductsRootV1

abbrev Ops := AspisR1FastDotsQueryValuesFourCallbackFieldResultV2.Ops
abbrev Wide := AspisR1FastDotsLiteralHeadSumRootV1.Wide
abbrev TowerWide := AspisR1FastDotsTailFieldProductRootV1.TowerWide
abbrev Contribution := AspisR1FastDotsActualTailBodyTraceRootV1.Contribution

private theorem list_range_sum_fin {K : Type} [AddCommMonoid K] :
    ∀ (n : Nat) (f : Nat → K),
      ((List.range' 0 n).map f).sum = ∑ i : Fin n, f i.val
  | 0, f => by simp
  | n + 1, f => by
      rw [List.range'_succ, List.map_cons, List.sum_cons,
        Fin.sum_univ_succ]
      simp only [Nat.zero_add]
      have hshift : List.range' 1 n = (List.range' 0 n).map Nat.succ := by
        rw [List.range'_eq_map_range, List.range'_eq_map_range]
        simp [List.range_eq_range', Nat.add_comm]
      rw [hshift, List.map_map]
      have hmap :
          ((List.range' 0 n).map (f ∘ Nat.succ)) =
            (List.range' 0 n).map (fun x => f (x + 1)) := by
        apply List.map_congr_left
        intro x hx
        simp [Function.comp_apply]
      rw [hmap]
      have hrec := list_range_sum_fin n (fun i => f (i + 1))
      simpa only [Fin.val_succ, Fin.val_zero, Nat.zero_add] using
        congrArg (fun x : K => f 0 + x) hrec

private theorem sum_fin3_values (f : Fin 3 → TowerWide) :
    (∑ i : Fin 3, f i) = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_assoc]

private theorem sum_fin29_split (f : Fin 29 → TowerWide) :
    (∑ i : Fin 29, f i) =
      (∑ i : Fin 26, f (Fin.castAdd 3 i)) +
        ∑ i : Fin 3, f (Fin.natAdd 26 i) := by
  simpa using (Fin.sum_univ_add (a := 26) (b := 3) f)

/-- A successful literal S4 callback equals the width-29 first-fold value
once its byte projections identify the 26 base-field terms and three
quadratic-field terms.  The two tail contributions are required in the
actual source order 26,27; the initial tail contribution is lane 28. -/
theorem literal_field_result_width29
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (value : Wide) (gamma : TowerWide)
    (word : Fin 29 → TowerWide)
    (hresult : LiteralFieldResult ops a g slot value)
    (hhead : ∀ (n : Nat) (hn : n < 26),
      headTermValue a g slot.val n =
        word ⟨n, by omega⟩ * gamma ^ n)
    (hwide28 : ∀ wide28 : Wide,
      Array.index_usize g 28#usize = .ok wide28 → wideDecoded wide28 = gamma ^ 28)
    (hfirst : ∀ wide28 q tailStart tail2 cs,
      AspisR1FastDotsHeadTailSharedWitnessRootV2.FirstQueryInput ops a slot q →
      Array.index_usize g 28#usize = .ok wide28 →
      AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace ops a g slot
        {start:=0#usize, «end»:=2#usize} tailStart tail2 cs →
      embedQM q = word ⟨28, by decide⟩)
    (htail : ∀ tailStart tail2 cs,
      AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace ops a g slot
        {start:=0#usize, «end»:=2#usize} tailStart tail2 cs →
      ∀ (c : Contribution) (hc : c ∈ cs) (hterm : c.term.val < 3),
        wideDecoded c.coefficient = gamma ^ (26 + c.term.val) ∧
        embedQM c.scalar = word ⟨26 + c.term.val, by omega⟩) :
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) =
      AspisV6Width29CorrelatedAgreement.width29Batch
        word gamma := by
  rcases hresult with ⟨wide28,q,tailStart,tail2,cs,hfirstQuery,hg28,hrun,
    haccepted,hdecode⟩
  have hindices : cs.map (fun c => c.term.val) = [0,1] := by
    have h := AspisR1FastDotsActualTailLoopTraceRootV1.actual_tail_trace_term_indices
      ops a g slot _ tailStart tail2 cs hrun
    change cs.map (fun c => c.term.val) = List.range' 0 2 at h
    exact h.trans (by decide)
  have hlength : cs.length = 2 := by
    have h := congrArg List.length hindices
    simpa using h
  have hshape : ∃ c0 c1, cs = [c0,c1] := by
    cases cs with
    | nil => simp only [List.length_nil] at hlength; omega
    | cons c0 rest =>
      cases rest with
      | nil => simp only [List.length_cons, List.length_nil] at hlength; omega
      | cons c1 rest =>
        cases rest with
        | nil => exact ⟨c0,c1,rfl⟩
        | cons c2 rest => simp only [List.length_cons] at hlength; omega
  rcases hshape with ⟨c0,c1,hcs⟩
  subst cs
  have hindices : [c0.term.val,c1.term.val] = [0,1] := by simpa using hindices
  rcases List.cons.inj hindices with ⟨hterm0,hrest⟩
  rcases List.cons.inj hrest with ⟨hterm1,_⟩
  have hc0 : wideDecoded c0.coefficient = gamma ^ 26 ∧
      embedQM c0.scalar = word ⟨26, by decide⟩ := by
    have h := htail tailStart tail2 [c0,c1] hrun c0 (by simp) (by omega)
    simpa [hterm0] using h
  have hc1 : wideDecoded c1.coefficient = gamma ^ 27 ∧
      embedQM c1.scalar = word ⟨27, by decide⟩ := by
    have h := htail tailStart tail2 [c0,c1] hrun c1 (by simp) (by omega)
    simpa [hterm1] using h
  have hfirstTerm : wideDecoded wide28 * embedQM q =
      word ⟨28, by decide⟩ * gamma ^ 28 := by
    rw [hfirst wide28 q tailStart tail2 [c0,c1] hfirstQuery hg28 hrun,
      hwide28 wide28 hg28]
    ring
  let term26 : TowerWide := word ⟨26, by decide⟩ * gamma ^ 26
  let term27 : TowerWide := word ⟨27, by decide⟩ * gamma ^ 27
  let term28 : TowerWide := word ⟨28, by decide⟩ * gamma ^ 28
  have htailSum :
      (((wide28,q)::[c0,c1].map (fun c => (c.coefficient,c.scalar))).map
        (fun p => wideDecoded p.1 * embedQM p.2)).sum = term28 + term26 + term27 := by
    simp only [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil]
    rw [hfirstTerm, hc0.1, hc0.2, hc1.1, hc1.2]
    simp only [term26, term27, term28]
    ring
  have hheadSum :
      ((List.range' 0 26).map (headTermValue a g slot.val)).sum =
      ∑ i : Fin 26, word (Fin.castAdd 3 i) * gamma ^ i.val := by
    rw [list_range_sum_fin]
    apply Finset.sum_congr rfl
    intro i hi
    have h := hhead i.val i.isLt
    change headTermValue a g slot.val i.val =
      word (Fin.castAdd 3 i) * gamma ^ i.val at h
    exact h
  have htailBatch :
      (∑ i : Fin 3, word (Fin.natAdd 26 i) * gamma ^ (26 + i.val)) =
        term26 + term27 + term28 := by
    rw [sum_fin3_values]
    simp [term26, term27, term28, Fin.natAdd, Fin.val_natAdd]
  have htotal :
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) =
      (∑ i : Fin 26, word (Fin.castAdd 3 i) * gamma ^ i.val) +
        ∑ i : Fin 3, word (Fin.natAdd 26 i) * gamma ^ (26 + i.val) := by
    calc
      _ = (∑ i : Fin 26, word (Fin.castAdd 3 i) * gamma ^ i.val) +
          (term28 + term26 + term27) := by rw [hdecode, hheadSum, htailSum]
      _ = (∑ i : Fin 26, word (Fin.castAdd 3 i) * gamma ^ i.val) +
          (term26 + term27 + term28) := by
        rw [show term28 + term26 + term27 = term26 + term27 + term28 by ring]
      _ = (∑ i : Fin 26, word (Fin.castAdd 3 i) * gamma ^ i.val) +
          (∑ i : Fin 3, word (Fin.natAdd 26 i) * gamma ^ (26 + i.val)) := by
        rw [← htailBatch]
  have hwidth :
      AspisV6Width29CorrelatedAgreement.width29Batch word gamma =
        (∑ i : Fin 26, word (Fin.castAdd 3 i) * gamma ^ i.val) +
          ∑ i : Fin 3, word (Fin.natAdd 26 i) * gamma ^ (26 + i.val) := by
    have hs := sum_fin29_split
      (f := fun lane => word lane * gamma ^ lane.val)
    simpa only [AspisV6Width29CorrelatedAgreement.width29Batch,
      Fin.val_castAdd, Fin.val_natAdd] using hs
  calc
    AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE value) =
      (∑ i : Fin 26, word (Fin.castAdd 3 i) * gamma ^ i.val) +
        ∑ i : Fin 3, word (Fin.natAdd 26 i) * gamma ^ (26 + i.val) := htotal
    _ = AspisV6Width29CorrelatedAgreement.width29Batch word gamma := hwidth.symm

end AspisR1D18S4Width29LiteralJoinV1

#print axioms AspisR1D18S4Width29LiteralJoinV1.literal_field_result_width29
