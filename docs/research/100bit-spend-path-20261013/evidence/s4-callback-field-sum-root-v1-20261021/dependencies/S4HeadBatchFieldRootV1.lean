import S4HeadFieldAlgebraRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsHeadBatchFieldRootV1
open AspisR1FastDotsHeadFieldAlgebraRootV1
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev TowerWide := AspisR1FastDotsTailFieldProductRootV1.TowerWide
abbrev rawBatchLists := AspisR1FastDotsOuterFoldTraceV2.rawBatchLists
abbrev fullSum := AspisR1.FastDotFoldedBatches.fullSum

def headBatchResidues (ds : List (List Contribution)) : TowerWide :=
  decodeNat8 (fun j=>fullSum (rawBatchLists ds j) % AspisV8R17.RawReducer.P)

theorem full_sum_flatten (ds : List (List Contribution)) (j : Fin 8) :
    fullSum (rawBatchLists ds j) =
      (ds.flatten.map (fun c=>c.product j)).sum := by
  induction ds with
  | nil => rfl
  | cons cs ds ih =>
    simp only [rawBatchLists,List.map_cons,fullSum,List.flatten_cons,
      List.map_append,List.sum_append]
    exact congrArg (fun n=>(cs.map (fun c=>c.product j)).sum+n) ih

theorem head_residues_decode_flatten (ds : List (List Contribution)) :
    headBatchResidues ds = (ds.flatten.map contributionDecoded).sum := by
  have hmod : headBatchResidues ds =
      decodeNat8 (fun j=>fullSum (rawBatchLists ds j)) := by
    apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
      apply QuadraticAlgebra.ext <;>
      simp [headBatchResidues,decodeNat8,AspisV8R17.QM31WordTower.embedQ,
        AspisV8R17.QM31WordTower.embedC,ZMod.natCast_mod]
  rw [hmod]
  have hfun : (fun j=>fullSum (rawBatchLists ds j)) =
      (fun j=>(ds.flatten.map (fun c=>c.product j)).sum) := by
    funext j
    exact full_sum_flatten ds j
  rw [hfun,decodeNat8_sum]
  rfl

theorem term_trace_to_limbs
    {ops : Ops} {a : Array Std.U8 608#usize} {g : Array Wide 29#usize} {slot : Usize}
    {iter : core.ops.range.Range Usize} {sums out : Array Std.U64 8#usize}
    {cs : List Contribution}
    (h : AspisR1FastDotsActualTermTraceRootV1.ActualTermTrace
      ops a g slot iter sums out cs) :
    ∀ c ∈ cs, AspisR1EbyKPushWideToQ.toLimbs c.wide = .ok c.coeff := by
  induction h with
  | done => intro c hc; cases hc
  | step c tail hbody hmatch hvalue htail ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hfirst | hrest
    · subst x
      exact hmatch.2.2.2.2.2
    · exact ih x hrest

theorem exact_trace_to_limbs
    {ops : Ops} {a : Array Std.U8 608#usize} {g : Array Wide 29#usize} {slot : Usize}
    {it : AspisR1FastDotsOuterFoldTraceV2.StepBy}
    {limbs out : Array Std.U64 8#usize} {ds : List (List Contribution)} {starts : List Nat}
    (h : AspisR1FastDotsOuterFoldTraceV2.ExactTrace
      ops a g slot it limbs out ds starts) :
    ∀ c ∈ ds.flatten, AspisR1EbyKPushWideToQ.toLimbs c.wide = .ok c.coeff := by
  induction h with
  | stop => intro c hc; cases hc
  | step hstep4 hnextStep4 hstart hcursor hend hbody hbatch htail ih =>
    intro c hc
    simp only [List.flatten_cons,List.mem_append] at hc
    rcases hc with hfirst | hrest
    · exact term_trace_to_limbs hbatch.sourceTrace c hfirst
    · exact ih c hrest

/-- Source read/limb correspondence is derived from the same exact head
trace; the final field sum uses precisely those parsed/read contributions. -/
theorem exact_trace_head_field_sum
    {ops : Ops} {a : Array Std.U8 608#usize} {g : Array Wide 29#usize} {slot : Usize}
    {it : AspisR1FastDotsOuterFoldTraceV2.StepBy}
    {limbs out : Array Std.U64 8#usize} {ds : List (List Contribution)} {starts : List Nat}
    (h : AspisR1FastDotsOuterFoldTraceV2.ExactTrace
      ops a g slot it limbs out ds starts) :
    headBatchResidues ds = (ds.flatten.map sourceProduct).sum := by
  rw [head_residues_decode_flatten]
  have hmaps : ds.flatten.map contributionDecoded = ds.flatten.map sourceProduct := by
    apply List.map_congr_left
    intro c hc
    exact actual_contribution_decodes c (exact_trace_to_limbs h c hc)
  rw [hmaps]

#print axioms full_sum_flatten
#print axioms head_residues_decode_flatten
#print axioms term_trace_to_limbs
#print axioms exact_trace_to_limbs
#print axioms exact_trace_head_field_sum
end AspisR1FastDotsHeadBatchFieldRootV1
