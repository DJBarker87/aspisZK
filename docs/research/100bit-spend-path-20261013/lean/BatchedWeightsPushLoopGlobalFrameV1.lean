import AspisR1BatchedWeightsPushBodyValueStepV3
import AspisR1BatchedWeightsSetCellFactsV1
import AspisR1BatchedAllPrefix
import AspisR1BatchedWeightsSetCellFactsV1
import OccupancyRangeTraversal
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP ControlFlow
namespace AspisR1BatchedWeightsPushLoopGlobalFrameV1
open AspisR1BatchedWeightsExtraction
open AspisR1BatchedWeightsPushBodyValueStepV3
abbrev BW := batched_weights.BatchedWeights
abbrev Range := core.ops.range.Range Usize
abbrev M := aspis_core.field.M31
abbrev Q := aspis_core.field.QM31

def rowAt (s : BW) (index : Usize) (hindex : index.val < s.raw.length) : Array Std.U64 4#usize :=
  s.raw.val[index.val]'(by simpa using hindex)
def cellAt (s : BW) (index : Usize) (hindex : index.val < s.raw.length)
    (k : Usize) (hk : k.val < 4) : Nat :=
  (rowAt s index hindex).val[k.val]'(by simpa [(rowAt s index hindex).property] using hk) |>.val
def limbAt (limbs : Array Std.U32 4#usize) (k : Usize) (hk : k.val < 4) : Nat :=
  (limbs.val[k.val]'(by simpa [limbs.property] using hk)).val
def expectedCell (initial : BW) (index : Usize) (hindex : index.val < initial.raw.length)
    (limbs : Array Std.U32 4#usize) (basis : M) (k : Usize) (hk : k.val < 4) : Nat :=
  cellAt initial index hindex k hk + limbAt limbs k hk * basis.val

def LoopInv (index : Usize) (initial : BW) (hindex : index.val < initial.raw.length)
    (limbs : Array Std.U32 4#usize) (basis : M) (s : Range × BW × M) : Prop :=
  s.1.end.val = 4 ∧ s.1.start.val ≤ 4 ∧ s.2.2 = basis ∧ s.2.1.terms = initial.terms ∧
  ∃ hs : index.val < s.2.1.raw.length,
    (∀ k : Usize, ∀ hk : k.val < 4,
      cellAt s.2.1 index hs k hk =
        if k.val < s.1.start.val then expectedCell initial index hindex limbs basis k hk
        else cellAt initial index hindex k hk) ∧
      s.2.1.raw.length = initial.raw.length ∧
      (∀ hlen : s.2.1.raw.length = initial.raw.length,
        ∀ r : Usize, ∀ hr : r.val < initial.raw.length, r.val ≠ index.val →
        s.2.1.raw.val[r.val]'(by simpa [hlen] using hr) =
          initial.raw.val[r.val]'hr)
def LoopPost (index : Usize) (initial : BW) (hindex : index.val < initial.raw.length)
    (limbs : Array Std.U32 4#usize) (basis : M) (out : BW) : Prop :=
  out.terms = initial.terms ∧ ∃ ho : index.val < out.raw.length,
    (∀ k : Usize, ∀ hk : k.val < 4,
      cellAt out index ho k hk = expectedCell initial index hindex limbs basis k hk) ∧
    out.raw.length = initial.raw.length ∧
    (∀ hlen : out.raw.length = initial.raw.length,
      ∀ r : Usize, ∀ hr : r.val < initial.raw.length, r.val ≠ index.val →
        out.raw.val[r.val]'(by simpa [hlen] using hr) = initial.raw.val[r.val]'hr)

private theorem limbAt_make (power : Q) (k : Usize) (hk : k.val < 4) :
    limbAt (Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]) k hk =
      ((Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]).val[k.val]'
        (by simpa [Array.make] using hk)).val := by rfl

/-- Exact four-coordinate result of the generated push loop.  Invariant tracks
processed-prefix updates and untouched suffix, so each body call inherits the
actual cadence bound on the selected cell. -/
theorem push_loop_all_prefix
    (index : Usize) (initial : BW) (power : Q) (basis : M)
    (hindex : index.val < initial.raw.length)
    (ha0 : ∀ k : Usize, ∀ hk : k.val < 4,
      cellAt initial index hindex k hk <
        2^34 + (initial.terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P) :
    ∃ out : BW,
      batched_weights.BatchedWeights.push_loop
        ({ start := 0#usize, «end» := 4#usize } : Range)
        initial index basis
        (Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]) = .ok out ∧
      LoopPost index initial hindex
        (Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]) basis out := by
  let limbs := Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]
  let iter0 : Range := { start := 0#usize, «end» := 4#usize }
  let body := fun s : Range × BW × M =>
    batched_weights.BatchedWeights.push_loop.body index limbs s.1 s.2.1 s.2.2
  have hwp : WP.spec (loop body (iter0, initial, basis))
      (LoopPost index initial hindex limbs basis) := by
    refine loop.spec_decr_nat (fun s : Range × BW × M => 4 - s.1.start.val)
      (LoopInv index initial hindex limbs basis) (LoopPost index initial hindex limbs basis)
      body (iter0, initial, basis) ?_ ?_
    · rintro ⟨iter, s, b⟩ ⟨hend, hstart, hbasisEq, hterms, ⟨hs, hcells, hlen, hframe⟩⟩
      change b = basis at hbasisEq
      subst b
      by_cases hlt : iter.start.val < iter.end.val
      · obtain ⟨iterNext, hnext, hstartNext, hendNext, hbound⟩ :=
          AspisR1.OccupancyRangeTraversal.next_step iter hlt
        let j := iter.start
        have hj : j.val < 4 := by simpa [hend] using hlt
        have hindexS : index.val < s.raw.length := hs
        have hrawSel : ∀ old : Array Std.U64 4#usize,
            old = s.raw.val[index.val]'(by simpa using hindexS) →
            (old.val[j.val]'(by simpa [old.property] using hj)).val <
              2^34 + (initial.terms.val % 4) * AspisR1BatchedAllPrefix.cap := by
          intro old hold
          have hcell := hcells j hj
          have hnot : ¬ j.val < iter.start.val := by dsimp [j]; omega
          simp only [hnot, ite_false] at hcell
          have hread : (old.val[j.val]'(by simpa [old.property] using hj)).val =
              cellAt initial index hindex j hj := by
            simpa [cellAt, rowAt, hold, hindexS] using hcell
          rw [hread]
          exact ha0 j hj
        obtain ⟨product, sum, updated, old, back, hprod, hsum, hold, hback, hset, hbody⟩ :=
          AspisR1BatchedWeightsPushBodyValueStepV3.push_body_step_power_value
            index iter s power basis j iterNext initial.terms
            (by simpa [j] using hnext) hj ha hb hc hd hbasis hindexS hrawSel
        have hiter1 : iterNext.start.val = iter.start.val + 1 := by simpa [j] using hstartNext
        have hiterEnd : iterNext.end.val = 4 := by rw [hendNext]; exact hend
        let s' : BW := { s with raw := back updated }
        have hs' : index.val < s'.raw.length := by
          simpa [s', hback, alloc.vec.Vec.set, List.length_set] using hindexS
        have hcells' : ∀ k : Usize, ∀ hk : k.val < 4,
            cellAt s' index hs' k hk =
              if k.val < iterNext.start.val then expectedCell initial index hindex limbs basis k hk
              else cellAt initial index hindex k hk := by
          intro k hk
          have hnew : cellAt s' index hs' k hk =
              (updated.val[k.val]'(by simpa [updated.property] using hk)).val := by
            simp [cellAt, rowAt, s', hback, alloc.vec.Vec.set, List.getElem_set_self]
          by_cases heq : k.val = j.val
          · have hkj : k = j := by
              exact UScalar.eq_of_val_eq heq
            subst k
            have hprev : (old.val[j.val]'(by simpa [old.property] using hj)).val =
                cellAt initial index hindex j hj := by
              have hc0 := hcells j hj
              have hnot : ¬ j.val < iter.start.val := by dsimp [j]; omega
              simp only [hnot, ite_false] at hc0
              simpa [cellAt, rowAt, hold, hindexS] using hc0
            have hprod' : product.val = limbAt limbs j hj * basis.val := by
              simpa [limbAt, limbs] using hprod
            have hsum' : sum.val = cellAt initial index hindex j hj + limbAt limbs j hj * basis.val := by
              rw [hprev, hprod'] at hsum
              exact hsum
            have hsetSelf : (updated.val[j.val]'(by simpa [updated.property] using hj)).val = sum.val := by
              simpa [hset] using AspisR1BatchedWeightsSetCellFactsV1.array_set_cell old j hj sum
            have hltNext : j.val < iterNext.start.val := by rw [hiter1]; dsimp [j]; omega
            rw [hnew, if_pos hltNext, hsetSelf]
            simpa [expectedCell] using hsum'
          · have hframe : (updated.val[k.val]'(by simpa [updated.property] using hk)).val =
                (old.val[k.val]'(by simpa [old.property] using hk)).val := by
              have hne : j.val ≠ k.val := by omega
              have hOld : k.val < old.val.length := by simpa [old.property] using hk
              have hSet : k.val < (old.val.set j.val sum).length := by
                simpa [List.length_set] using hOld
              have hData : (old.val.set j.val sum)[k.val]'hSet =
                  old.val[k.val]'(by simpa [old.property] using hk) :=
                List.getElem_set_ne hne hSet
              rw [hset]
              change ((old.val.set j.val sum)[k.val]'hSet).val =
                (old.val[k.val]'(by simpa [old.property] using hk)).val
              exact congrArg UScalar.val hData
            have hcur : (old.val[k.val]'(by simpa [old.property] using hk)).val =
                if k.val < iter.start.val then expectedCell initial index hindex limbs basis k hk
                else cellAt initial index hindex k hk := by
              simpa [cellAt, rowAt, hold, hindexS] using hcells k hk
            rw [hnew, hframe, hcur]
            by_cases hbefore : k.val < iter.start.val
            · have hbefore' : k.val < iterNext.start.val := by rw [hiter1]; omega
              simp [hbefore, hbefore']
            · have hafter' : iterNext.start.val ≤ k.val := by
                rw [hiter1]
                have hjVal : j.val = iter.start.val := rfl
                have hneq : k.val ≠ iter.start.val := by
                  intro hEq
                  apply heq
                  rw [hEq, hjVal]
                omega
              simp [hbefore, hafter']
        have hstartLt : iter.start.val < 4 := by
          have hendEq : iter.end.val = 4 := by simpa using hend
          omega
        have hlen' : s'.raw.length = initial.raw.length := by
          simp [s', hback, alloc.vec.Vec.set, List.length_set, hlen]
        have hframe' : ∀ hlen' : s'.raw.length = initial.raw.length,
            ∀ r : Usize, ∀ hr : r.val < initial.raw.length,
            r.val ≠ index.val →
            s'.raw.val[r.val]'(by simpa [hlen'] using hr) =
              initial.raw.val[r.val]'hr := by
          intro hlen' r hr hne
          have hrs : r.val < s.raw.length := by simpa [hlen] using hr
          have hsetFrame := AspisR1BatchedWeightsSetCellFactsV1.vec_set_frame
            s.raw index r hs hrs (Ne.symm hne) updated
          have hrs' : r.val < s'.raw.length := by
            change r.val < s'.raw.length
            rw [hlen']
            exact hr
          have hrow : s'.raw.val[r.val]'hrs' =
              s.raw.val[r.val]'(by simpa using hrs) := by
            simpa [s', hback, List.length_set] using hsetFrame
          calc
            s'.raw.val[r.val]'hrs' =
                s.raw.val[r.val]'(by simpa using hrs) := hrow
          _ = initial.raw.val[r.val]'hr := hframe hlen r hr hne
        have hinv' : LoopInv index initial hindex limbs basis (iterNext, s', basis) := by
          refine ⟨hiterEnd, ?_, rfl, hterms, hs', hcells', hlen', hframe'⟩
          rw [hiter1]
          omega
        have hcont : body (iter, s, basis) = .ok (.cont (iterNext, s', basis)) := by
          simpa [body, s', j] using hbody
        rw [hcont, WP.spec_ok]
        change LoopInv index initial hindex limbs basis (iterNext, s', basis) ∧
          4 - iterNext.start.val < 4 - iter.start.val
        exact ⟨hinv', by rw [hiter1]; omega⟩
      · have hge : iter.start.val ≥ iter.end.val := Nat.le_of_not_gt hlt
        have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hge
        have hdone : body (iter, s, basis) = .ok (.done s) := by
          simp [body, batched_weights.BatchedWeights.push_loop.body, hnext]
        rw [hdone, WP.spec_ok]
        change LoopPost index initial hindex limbs basis s
        have hstartEq : iter.start.val = 4 := by
          change iter.start.val ≤ 4 at hstart
          change iter.end.val = 4 at hend
          change iter.start.val ≥ iter.end.val at hge
          omega
        refine ⟨hterms, ⟨hs, ?_⟩⟩
        refine ⟨?_, hlen, hframe⟩
        intro k hk
        have hklt : k.val < iter.start.val := by omega
        have hfinal := hcells k hk
        simp only [hstartEq, hk, ite_true] at hfinal
        simpa [expectedCell] using hfinal
    · refine ⟨by change (4#usize).val = 4; decide,
        by change (0#usize).val ≤ 4; decide, rfl, rfl, hindex, ?_⟩
      constructor
      · intro k hk
        have hstartZero : iter0.start.val = 0 := by decide
        simp [hstartZero, cellAt, rowAt]
      · constructor
        · rfl
        · intro hlen r hr hne
          rfl
  obtain ⟨out, hout, hpost⟩ := WP.spec_imp_exists hwp
  refine ⟨out, ?_, hpost⟩
  simpa [body, batched_weights.BatchedWeights.push_loop, iter0, limbs] using hout
#print axioms push_loop_all_prefix
end AspisR1BatchedWeightsPushLoopGlobalFrameV1
