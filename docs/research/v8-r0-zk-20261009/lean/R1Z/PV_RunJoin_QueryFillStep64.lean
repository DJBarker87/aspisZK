import R1Z.PV_RunJoin_QueryMatrixTotal64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryFillStep64
attribute [local irreducible] PV_RunJoin_WeightInstalled46.selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_FibreFillThread43 (Matrix)
open PV_RunJoin_QueryMatrixTotal64 (put)
variable [ExternalTypes] [ExternalFuns]

def Domain (c : host_commitment.Commitment) : Prop :=
  c.lanes.length≤29 ∧ ∃ enough : c.lanes.length≤c.words.length,
  (∀ lane∈c.lanes.val, lane.val<29) ∧
  (∀ (j : Nat) (h : j<c.lanes.length),
    1048576≤PV_RunJoin_QueryWordTotal64.length (c.words.val[j]'(Nat.lt_of_lt_of_le h enough)))

def step (c : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex)
    (values : Matrix) (j : Usize) : Result Matrix := do
  let lane ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize) c.lanes j
  let word ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice host_commitment.Word) c.words j
  let row ← host_commitment.opening_lane_values word u
  let x0 ← Array.index_usize row 0#usize
  let values ← put values 0#usize lane x0
  let x1 ← Array.index_usize row 1#usize
  let values ← put values 1#usize lane x1
  let x2 ← Array.index_usize row 2#usize
  let values ← put values 2#usize lane x2
  let x3 ← Array.index_usize row 3#usize
  put values 3#usize lane x3

theorem pair_bind {A B C : Type} (r : Result (A × B)) (f : A → B → Result C) :
    (do let (a,b) ← r;f a b)=(do let p ← r;f p.1 p.2) := by
  apply congrArg (Aeneas.Std.bind r)
  funext p
  cases p
  rfl

theorem factor (c : host_commitment.Commitment) (u : aspis_core.r0.domain.FibreIndex)
    (values : Matrix) (j : Usize) :
    PV_RunJoin_FibreFillThread43.step c u values j=step c u values j := by
  simp only [PV_RunJoin_FibreFillThread43.step,step,put,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry,pair_bind]

end R1Z.PV_RunJoin_QueryFillStep64
namespace R1Z.PV_RunJoin_QueryFillStep64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_FibreFillThread43 (Matrix)
open PV_RunJoin_QueryMatrixTotal64 (put)

theorem total (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (c : host_commitment.Commitment) (domain : Domain c)
    (u : aspis_core.r0.domain.FibreIndex) (bound : u.val<262144)
    (values : Matrix) (j : Usize) (more : j.val<c.lanes.length) :
    ∃ next, @PV_RunJoin_FibreFillThread43.step (types base) (selected base heap box ops)
      c u values j=ok next := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  let lane := c.lanes.val[j.val]'more
  have wordsBound : j.val<c.words.length := Nat.lt_of_lt_of_le more domain.2.choose
  let word := c.words.val[j.val]'wordsBound
  have hl := PV_RunJoin_QueryAccess64.read c.lanes j more
  have hw := PV_RunJoin_QueryAccess64.read c.words j wordsBound
  have laneBound : lane.val<29 := domain.2.choose_spec.1 lane (List.getElem_mem more)
  have wordSize : 1048576≤PV_RunJoin_QueryWordTotal64.length word :=
    domain.2.choose_spec.2 j.val more
  obtain ⟨row,hrow⟩ := PV_RunJoin_QueryLaneTotal64.complete base heap box ops word wordSize u bound
  obtain ⟨x0,h0⟩ : ∃ x, Array.index_usize row 0#usize=ok x :=
    ⟨_,ProverCommitArrayIndex25.array_index_usize_ok row 0#usize (by decide)⟩
  obtain ⟨x1,h1⟩ : ∃ x, Array.index_usize row 1#usize=ok x :=
    ⟨_,ProverCommitArrayIndex25.array_index_usize_ok row 1#usize (by decide)⟩
  obtain ⟨x2,h2⟩ : ∃ x, Array.index_usize row 2#usize=ok x :=
    ⟨_,ProverCommitArrayIndex25.array_index_usize_ok row 2#usize (by decide)⟩
  obtain ⟨x3,h3⟩ : ∃ x, Array.index_usize row 3#usize=ok x :=
    ⟨_,ProverCommitArrayIndex25.array_index_usize_ok row 3#usize (by decide)⟩
  obtain ⟨v0,hv0⟩ := PV_RunJoin_QueryMatrixTotal64.total values 0#usize lane x0 (by decide) laneBound
  obtain ⟨v1,hv1⟩ := PV_RunJoin_QueryMatrixTotal64.total v0 1#usize lane x1 (by decide) laneBound
  obtain ⟨v2,hv2⟩ := PV_RunJoin_QueryMatrixTotal64.total v1 2#usize lane x2 (by decide) laneBound
  obtain ⟨v3,hv3⟩ := PV_RunJoin_QueryMatrixTotal64.total v2 3#usize lane x3 (by decide) laneBound
  refine ⟨v3,?_⟩
  dsimp only [lane,word] at hrow hv0 hv1 hv2 hv3
  rw [factor]
  simp only [step,hl,hw,bind_tc_ok,hrow,h0,h1,h2,h3,hv0,hv1,hv2,hv3]

#print axioms Domain
#print axioms step
#print axioms pair_bind
#print axioms factor
#print axioms total
end R1Z.PV_RunJoin_QueryFillStep64
