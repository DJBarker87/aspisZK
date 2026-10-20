import AspisR1GroupedPairCut.Funs
import AspisR1GroupedPairCut.Proofs.S3GroupedPairLoop0BodyBind
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisR1GroupedPairCut.Proofs

abbrev CoeffArray := Array field.WideExact 12#usize

def DecodedArrayMeaning {E : Type} (decode : field.WideExact → E)
    (a : CoeffArray) (f : Fin 12 → E) : Prop :=
  ∀ k : Fin 12, decode (a.val[k.val]'(by
    have hp := a.property
    change a.val.length = 12 at hp
    omega)) = f k

/-- The exact value effect of an in-bounds generated array update, expressed
pointwise so the loop invariant can be stated independently of `Array.set`. -/
theorem decoded_meaning_set {E : Type} (decode : field.WideExact → E)
    (a : CoeffArray) (idx : Std.Usize) (v : field.WideExact)
    (f : Fin 12 → E) (hmeaning : DecodedArrayMeaning decode a f)
    (hidx : idx.val < 12) :
    DecodedArrayMeaning decode (a.set idx v)
      (fun k => if k.val = idx.val then decode v else f k) := by
  cases a with
  | mk xs hxs =>
    intro k
    have hn : xs.length = 12 := by simpa using hxs
    have hidxList : idx.val < xs.length := by omega
    have hkList : k.val < xs.length := by omega
    change decode ((xs.set idx.val v)[k.val]'(by simpa [List.length_set, hxs])) = _
    rw [List.getElem_set (h := by simpa [List.length_set] using hkList)]
    by_cases hk : k.val = idx.val
    · simp [hk]
    · have hm := hmeaning k
      change decode (xs[k.val]'(by simpa using hkList)) = f k at hm
      have hne : idx.val ≠ k.val := fun h => hk h.symm
      rw [if_neg hne]
      change decode (xs[k.val]'(by simpa using hkList)) =
        (if k.val = idx.val then decode v else f k)
      rw [if_neg hk]
      exact hm

/-- A successful generated first-loop body preserves the pointwise semantic
coefficient meaning, updating exactly the selected group by the decoded input. -/
theorem grouped_pair_loop0_body_meaning {E : Type}
    (decode : field.WideExact → E) (addE : E → E → E)
    (ops : weights.WideExactOps)
    (coeff : Array field.WideExact 64#usize)
    (iter : core.ops.range.Range Std.Usize)
    (coefficients : CoeffArray)
    (j : Std.Usize) (iterNext : core.ops.range.Range Std.Usize)
    (groupByte : Std.U8) (group : Std.Usize)
    (oldCoeff inputCoeff newCoeff : field.WideExact)
    (updated : CoeffArray) (inputValue : E)
    (f : Fin 12 → E) (inputModel : Fin 64 → E)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j, iterNext))
    (hgroup : Array.index_usize weights.S2_INACTIVE_GROUPS j = .ok groupByte)
    (hcast : lift (UScalar.cast .Usize groupByte) = .ok group)
    (hold : Array.index_usize coefficients group = .ok oldCoeff)
    (hin : Array.index_usize coeff j = .ok inputCoeff)
    (hadd : ops.add oldCoeff inputCoeff = .ok newCoeff)
    (hupdate : Array.update coefficients group newCoeff = .ok updated)
    (hgroupBound : group.val < 12)
    (hj : j.val < 64)
    (hmeaning : DecodedArrayMeaning decode coefficients f)
    (holdMeaning : decode oldCoeff = f ⟨group.val, hgroupBound⟩)
    (hinMeaning : decode inputCoeff = inputValue)
    (hinputModel : inputModel ⟨j.val, hj⟩ = inputValue)
    (haddMeaning : decode newCoeff = addE (decode oldCoeff) (decode inputCoeff)) :
    weights.s2_grouped_inactive_pair_loop0.body ops coeff iter coefficients =
        .ok (.cont (iterNext, updated)) ∧
      DecodedArrayMeaning decode updated
        (fun k => if k.val = group.val then
          addE (f ⟨group.val, hgroupBound⟩) (inputModel ⟨j.val, hj⟩) else f k) := by
  have hlen : group.val < coefficients.length := by
    simpa [coefficients.property] using hgroupBound
  obtain ⟨updated', hspec, hset⟩ := WP.spec_imp_exists
    (Array.update_spec coefficients group newCoeff hlen)
  have hlinked : updated = updated' := Result.ok.inj (hupdate.symm.trans hspec)
  have hsetArray : updated' = coefficients.set group newCoeff := hset
  have hupdated : updated = coefficients.set group newCoeff := hlinked.trans hsetArray
  subst updated'
  subst updated
  constructor
  · exact grouped_pair_loop0_body_success ops coeff iter coefficients j iterNext
      groupByte group oldCoeff inputCoeff newCoeff (coefficients.set group newCoeff)
      hnext hgroup hcast hold hin hadd hupdate
  · have hset := decoded_meaning_set decode coefficients group newCoeff f hmeaning hgroupBound
    intro k
    have hkSet := hset k
    by_cases hkg : k.val = group.val
    · have heq : k = ⟨group.val, hgroupBound⟩ := Fin.ext hkg
      subst k
      have hnew : decode newCoeff =
          addE (f ⟨group.val, hgroupBound⟩) (inputModel ⟨j.val, hj⟩) := by
        calc
          decode newCoeff = addE (decode oldCoeff) (decode inputCoeff) := haddMeaning
          _ = addE (f ⟨group.val, hgroupBound⟩) (inputModel ⟨j.val, hj⟩) := by
            rw [holdMeaning, hinMeaning, ← hinputModel]
      simpa [hnew] using hkSet
    · simpa [hkg] using hkSet

/-- The generated 64-entry group table contains only the twelve legal
accumulator indices. -/
theorem grouped_pair_group_table_bound (j : Std.Usize) (hj : j.val < 64)
    (g : Std.U8)
    (h : Array.index_usize weights.S2_INACTIVE_GROUPS j = .ok g) :
    g.val < 12 := by
  have hlen : j.val < weights.S2_INACTIVE_GROUPS.length := by
    simpa [weights.S2_INACTIVE_GROUPS.property] using hj
  obtain ⟨x, hx, hvalue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec weights.S2_INACTIVE_GROUPS j hlen)
  have hxg : x = g := Result.ok.inj (hx.symm.trans h)
  have hselected : g = weights.S2_INACTIVE_GROUPS.val[j.val]'hlen := by
    calc
      g = x := hxg.symm
      _ = weights.S2_INACTIVE_GROUPS.val[j.val]'hlen := hvalue
  have hall : ∀ x ∈ weights.S2_INACTIVE_GROUPS.val, x.val < 12 := by
    simp [weights.S2_INACTIVE_GROUPS, Array.make]
  rw [hselected]
  exact hall _ (List.getElem_mem hlen)

end AspisR1GroupedPairCut.Proofs
#print axioms AspisR1GroupedPairCut.Proofs.decoded_meaning_set
#print axioms AspisR1GroupedPairCut.Proofs.grouped_pair_loop0_body_meaning
#print axioms AspisR1GroupedPairCut.Proofs.grouped_pair_group_table_bound
