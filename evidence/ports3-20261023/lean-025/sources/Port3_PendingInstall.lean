import Port3_FlushInstall
import S7JoinQueryRows

/-! Success-conditioned constructor reference with fallible reservation.
Native adoption is the explicitly named Port3 pending P6 certificate; it is
not inferred from similarity of source roots. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_PendingInstall
open Aeneas Aeneas.Std Result
open Port3_FlushInstall (K BW)
abbrev Row := Array U64 4#usize

def row (q : K) : Row := Array.make 4#usize
  [core.convert.num.FromU64U32.from q.c0.a,
   core.convert.num.FromU64U32.from q.c0.b,
   core.convert.num.FromU64U32.from q.c1.a,
   core.convert.num.FromU64U32.from q.c1.b]

def raw (old : Slice K) : alloc.vec.Vec Row :=
  ⟨old.val.map row,by simpa using old.property⟩

def pending (reserved : Bool) (old : Slice K) :
    Result (core.result.Result BW VTop_Stages.verifier.Error) := do
  let allocation ← OraclePortStdAllocation.filled old.len (Array.repeat 4#usize 0#u64) reserved
  match allocation with
  | .error _ => ok (.Err .Allocation)
  | .ok _ => ok (.Ok ⟨raw old,0#usize⟩)

def install (base : VTop_Stages.Ops) (reserved : Bool)
    (aops : AspisR1Stage2.AccumulateOps) (qops : AspisR1Stage2.QueryOps) : VTop_Stages.Ops :=
  {Port3_FlushInstall.install base reserved aops qops with op10 := pending reserved}

theorem pending_exact (reserved : Bool) (old : Slice K) :
    pending reserved old = if reserved then ok (.Ok ⟨raw old,0#usize⟩) else ok (.Err .Allocation) := by
  cases reserved <;> simp [pending,OraclePortStdAllocation.filled_exact,OraclePortStdAllocation.filledSpec]

theorem accepted_fields (reserved : Bool) (old : Slice K) (state : BW)
    (accepted : pending reserved old = ok (.Ok state)) :
    reserved = true ∧ state.raw.val = old.val.map row ∧ state.terms = 0#usize ∧
      state.raw.val.length = old.val.length := by
  rw [pending_exact] at accepted
  cases reserved with
  | false => cases accepted
  | true =>
    have same := core.result.Result.Ok.inj (Result.ok.inj accepted)
    subst state
    exact ⟨rfl,rfl,rfl,List.length_map⟩

def owned (old : Slice K) : S8OwnedP6Finish.Weights := Port3_FlushInstall.toWeights old

theorem initial_raw (old : Slice K) :
    raw old = S7Kani3CallerTrace.initialRaw (owned old) := by
  apply Subtype.ext
  simp only [raw,S7Kani3CallerTrace.initialRaw,owned,Port3_FlushInstall.toWeights,List.map_map]
  apply List.map_congr_left
  intro q _
  rfl

theorem accepted_trace (reserved : Bool) (old : Slice K) (state : BW)
    (accepted : pending reserved old = ok (.Ok state)) :
    S7Kani3CallerTrace.PushTrace (owned old)
      (⟨state.raw,state.terms⟩ : S7Kani2AccumulatorLoop.BatchedWeights)
      (S7Kani3CallerTrace.initialSum (owned old)) := by
  obtain ⟨_,hr,ht,_⟩ := accepted_fields reserved old state accepted
  have he : state.raw = raw old := Subtype.ext hr
  rw [he,ht,initial_raw]
  exact .initial

theorem accepted_progress (reserved : Bool) (old : Slice K) (state : BW)
    (size : old.val.length = 64) (accepted : pending reserved old = ok (.Ok state)) :
    S7JoinRowsTrace.Progress 0 0
      (⟨state.raw,state.terms⟩ : S7Kani2AccumulatorLoop.BatchedWeights) := by
  obtain ⟨_,hr,ht,_⟩ := accepted_fields reserved old state accepted
  have he : state.raw = raw old := Subtype.ext hr
  rw [he,ht,initial_raw]
  exact S7JoinQueryRows.initial_progress (owned old) (by simpa [owned,Port3_FlushInstall.toWeights] using size)

#print axioms pending_exact
#print axioms accepted_fields
#print axioms initial_raw
#print axioms accepted_trace
#print axioms accepted_progress
end AspisR1.Port3_PendingInstall
end
