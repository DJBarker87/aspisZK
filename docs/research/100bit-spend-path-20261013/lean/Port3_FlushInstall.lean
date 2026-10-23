import Port3_QueryInstall
import S8JoinFinishField

/-! Explicit carrier transport of the retained mutable finish extraction.
The local source/reference certificate is S8Kani2FinishReferenceJoin;
query-produced raw length and field meaning are separate caller obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_FlushInstall
open Aeneas Aeneas.Std Result
abbrev K := VTop_Stages.aspis_core.field.QM31
abbrev BW := VTop_Stages.verifier.BatchedWeights

def toOwned (x : K) : S8OwnedP6ValueModel.Q := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromMutable (x : S8Kani2MutableValue.F.Q) : K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toWeights (s : Slice K) : S8OwnedP6Finish.Weights := ⟨s.val.map toOwned,by simpa using s.property⟩
def fromSlice (s : S8Kani2MutableExtraction.batched_weights.FinishSlice) : Slice K :=
  ⟨s.val.map fromMutable,by simpa using s.property⟩

def flush (b : BW) (old : Slice K) : Result (Slice K) := do
  let out ← S8Kani2MutableExtraction.batched_weights.BatchedWeights.finish
    (⟨b.raw,b.terms⟩ : S8Kani2MutableValue.F.BW)
    (S8Kani2FinishReferenceJoin.toSlice (toWeights old))
  ok (fromSlice out)

def install (base : VTop_Stages.Ops) (reserved : Bool)
    (aops : AspisR1Stage2.AccumulateOps) (qops : AspisR1Stage2.QueryOps) : VTop_Stages.Ops :=
  {Port3_QueryInstall.install base reserved aops qops with op9 := flush}

/-- Full mutable finish result; no successful-return premise or raw bound.
Only the actual destination/raw length relation is needed. -/
theorem flush_exact (b : BW) (old : Slice K)
    (lengths : old.val.length ≤ b.raw.val.length) :
    flush b old = ok (fromSlice
      ⟨(S8JoinFinishExact.output b.raw (toWeights old)).val.map S8Kani2FinishReferenceJoin.toFinish,
        by simpa using (S8JoinFinishExact.output b.raw (toWeights old)).property⟩) := by
  obtain ⟨out,run,cells⟩ := S8JoinFinishExact.mutable_exact b.raw (toWeights old) b.terms
    (by simpa [toWeights] using lengths)
  have same : out = ⟨(S8JoinFinishExact.output b.raw (toWeights old)).val.map
      S8Kani2FinishReferenceJoin.toFinish,by simpa using
        (S8JoinFinishExact.output b.raw (toWeights old)).property⟩ := Subtype.ext cells
  simp only [flush,run,bind_tc_ok,same]

theorem accepted_contents (b : BW) (old out : Slice K)
    (lengths : old.val.length ≤ b.raw.val.length) (success : flush b old = ok out) :
    out.val = ((b.raw.val.take old.val.length).map
      (fun row => fromMutable (S8Kani2FinishReferenceJoin.toFinish
        (S8OwnedP6Finish.modelValue row)))) ∧ out.val.length = old.val.length := by
  rw [flush_exact b old lengths] at success
  have same := Result.ok.inj success
  subst out
  constructor
  · simp only [fromSlice,S8JoinFinishExact.output,toWeights,alloc.vec.Vec.length,
      List.length_map,List.map_map]
    rfl
  · simp only [fromSlice,S8JoinFinishExact.output,toWeights,alloc.vec.Vec.length,
      List.length_map,List.length_take,Nat.min_eq_left lengths]

def Canonical (q : K) : Prop :=
  q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
  q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

theorem model_canonical (row : S8OwnedP6ValueModel.Row) :
    Canonical (fromMutable (S8Kani2FinishReferenceJoin.toFinish
      (S8OwnedP6Finish.modelValue row))) := by
  exact ⟨(S8OwnedP6Finish.modelValue_coordinates row 0).2,
    (S8OwnedP6Finish.modelValue_coordinates row 1).2,
    (S8OwnedP6Finish.modelValue_coordinates row 2).2,
    (S8OwnedP6Finish.modelValue_coordinates row 3).2⟩

theorem accepted_canonical (b : BW) (old out : Slice K)
    (lengths : old.val.length ≤ b.raw.val.length) (success : flush b old = ok out) :
    ∀ q ∈ out.val, Canonical q := by
  have contents := (accepted_contents b old out lengths success).1
  rw [contents]
  intro q member
  obtain ⟨row,_,rfl⟩ := List.mem_map.mp member
  exact model_canonical row

#print axioms flush_exact
#print axioms accepted_contents
#print axioms model_canonical
#print axioms accepted_canonical
end AspisR1.Port3_FlushInstall
end
