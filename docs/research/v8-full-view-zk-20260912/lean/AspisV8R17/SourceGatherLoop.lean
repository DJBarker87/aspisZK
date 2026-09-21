import AspisV8R17.ScatterDual

/-! Accumulator shape of opening_weights::xt, using the retained bounded
bit-index schedule. Fuel failure is explicit; concrete calls discharge it. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [CommRing F]

def gatherIndexLoop (half : F) (w : ℕ → F) :
    ℕ → ℕ → ℕ → F → F → Option F
  | 0, _, _, _, _ => none
  | fuel+1, row, bit, scale, acc =>
      if row &&& (2^bit) != 0 then
        let next := row ^^^ (2^bit)
        let nextScale := scale*half
        gatherIndexLoop half w fuel next (bit+1) nextScale (acc+w next*nextScale)
      else some (acc+w (row ||| (2^bit))*scale)

theorem gatherIndexLoop_weighted (half : F) (w : ℕ → F)
    (fuel row bit : ℕ) (scale acc : F) :
    gatherIndexLoop half w fuel row bit scale acc =
      (weightedIndexLoop half fuel row bit scale).map
        (fun es => acc+(es.map fun e => e.2*w e.1).sum) := by
  induction fuel generalizing row bit scale acc with
  | zero => rfl
  | succ fuel ih =>
    simp only [gatherIndexLoop, weightedIndexLoop]
    split
    · rw [ih]
      cases weightedIndexLoop half fuel (row ^^^ 2^bit) (bit+1) (scale*half) with
      | none => rfl
      | some es =>
        simp only [Option.map_some, List.map_cons, List.sum_cons]
        congr 1
        ring
    · simp [mul_comm]

theorem sourceGather_loop (half : F) (n i : ℕ)
    (bounded : scheduleBounded n = true) (hi : i<n) (w : ℕ → F) :
    gatherIndexLoop half w 10 i 0 1 0 = some (sourceGather half w i) := by
  obtain ⟨es, he, _⟩ := weighted_schedule_bounds half n i bounded hi
  simp [gatherIndexLoop_weighted, sourceGather, he]

theorem sourceGather_loop512 (half : F) (i : ℕ) (hi : i<512) (w : ℕ → F) :
    gatherIndexLoop half w 10 i 0 1 0 = some (sourceGather half w i) :=
  sourceGather_loop half 512 i schedule512_bounded hi w

theorem sourceGather_loop513 (half : F) (i : ℕ) (hi : i<513) (w : ℕ → F) :
    gatherIndexLoop half w 10 i 0 1 0 = some (sourceGather half w i) :=
  sourceGather_loop half 513 i schedule513_bounded hi w

/-- The intermediate 513 coordinates are retained in the double operation.
The reverse pass gathers 514 to 513 and then 513 to 512. -/
theorem source_double_scatter_gather_dot (half : F) (q w : ℕ → F) :
    (∑ r ∈ Finset.range 514, w r *
      scatterValue (sourceEdges half 513) (scatterValue (sourceEdges half 512) q) r) =
      ∑ i ∈ Finset.range 512, sourceGather half (sourceGather half w) i * q i := by
  rw [source_scatter_gather_dot half 513 schedule513_bounded,
    source_scatter_gather_dot half 512 schedule512_bounded]

#print axioms gatherIndexLoop_weighted
#print axioms sourceGather_loop
#print axioms sourceGather_loop512
#print axioms sourceGather_loop513
#print axioms source_double_scatter_gather_dot
end AspisV8R17
