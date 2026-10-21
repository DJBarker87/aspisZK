import Stage2ContinuationQueryLoop

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsTx2PowersQuerySourceCutV1

abbrev Wide := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev Gamma := AspisR1Stage2.aspis_core.field.QM31
abbrev GArray := Array Wide 29#usize
abbrev QueryCall := AspisR1Stage2.QueryCall
abbrev QueryGeometry := AspisR1Stage2.verifier.QueryGeometry
abbrev Accumulator := AspisR1Stage2.verifier.Accumulator
abbrev BatchedWeights := AspisR1Stage2.verifier.BatchedWeights
abbrev QueryState := core.result.Result (Accumulator × BatchedWeights) AspisR1Stage2.verifier.Error

/-- Explicit operation boundary for the emitted `tx2_common` slice from the
    `weights.powers` bind through the initial `query_loop` call. The surrounding
    source arguments are captured by these typed operations. In particular,
    none of the intervening operations accepts or rewrites the powers array. -/
structure Ops where
  powers : Std.Usize → Gamma → Result GArray
  markCheckpoint : Result Unit
  readInactive : Result Unit
  readFoldedRoot : Result Unit
  batchMerkle : Result Unit
  markMerkle : Result Unit
  makeGeometry : Result QueryGeometry
  makePending : Result BatchedWeights

def tx2QueryPrefix (ops : Ops) (call : QueryCall)
    (proof : Slice Std.U8) (p : AspisR1Stage2.verifier.Prepared)
    (a : Accumulator) (gamma : Gamma)
    (obs : Option (AspisR1Stage2.verifier.Phase → Result Unit)) :
    Result QueryState := do
  let g ← ops.powers 29#usize gamma
  ops.markCheckpoint
  ops.readInactive
  ops.readFoldedRoot
  ops.batchMerkle
  ops.markMerkle
  let geometry ← ops.makeGeometry
  let pending ← ops.makePending
  AspisR1Stage2.verifier.candidate.query_loop call proof p a g obs geometry pending 22#usize

theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- Success of the source-shaped prefix retains the exact array returned by the
    `weights.powers 29 gamma` operation and proves that the emitted query-loop
    call succeeds on that same array. The intervening parser/authentication/
    geometry/pending boundaries remain explicit operations. -/
theorem tx2_query_prefix_success_same_g
    (ops : Ops) (call : QueryCall) (proof : Slice Std.U8)
    (p : AspisR1Stage2.verifier.Prepared) (a : Accumulator) (gamma : Gamma)
    (obs : Option (AspisR1Stage2.verifier.Phase → Result Unit))
    {out : QueryState} (h : tx2QueryPrefix ops call proof p a gamma obs = .ok out) :
    ∃ g : GArray, ops.powers 29#usize gamma = .ok g ∧
      ∃ geometry : QueryGeometry, ops.makeGeometry = .ok geometry ∧
      ∃ pending : BatchedWeights, ops.makePending = .ok pending ∧
        AspisR1Stage2.verifier.candidate.query_loop call proof p a g obs geometry pending 22#usize = .ok out := by
  unfold tx2QueryPrefix at h
  obtain ⟨g,hg,h⟩ := bind_ok_inv h
  obtain ⟨_,hmark,h⟩ := bind_ok_inv h
  obtain ⟨_,hinactive,h⟩ := bind_ok_inv h
  obtain ⟨_,hfolded,h⟩ := bind_ok_inv h
  obtain ⟨_,hmerkle,h⟩ := bind_ok_inv h
  obtain ⟨_,hmark2,h⟩ := bind_ok_inv h
  obtain ⟨geometry,hgeometry,h⟩ := bind_ok_inv h
  obtain ⟨pending,hpending,hloop⟩ := bind_ok_inv h
  exact ⟨g,hg,geometry,hgeometry,pending,hpending,hloop⟩

/-- A successful next=10 source prefix can be consumed by the existing
    emitted-loop theorem without changing its g parameter. This keeps the
    twelve query calls tied to the exact powers result from the same prefix. -/
theorem tx2_query_prefix_success_twelve_calls
    (ops : Ops) (call : QueryCall) (proof : Slice Std.U8)
    (p : AspisR1Stage2.verifier.Prepared) (a outAcc : Accumulator)
    (gamma : Gamma) (obs : Option (AspisR1Stage2.verifier.Phase → Result Unit))
    (bout : BatchedWeights) (start : a.next.val = 10)
    (advance : ∀ g geometry a0 a1 b0 b1,
      call proof p a0 g obs geometry b0 = .ok (.Ok (a1,b1)) →
      a1.next.val = a0.next.val + 1)
    (h : tx2QueryPrefix ops call proof p a gamma obs = .ok (.Ok (outAcc,bout))) :
    ∃ g : GArray, ops.powers 29#usize gamma = .ok g ∧
      ∃ geometry : QueryGeometry, ops.makeGeometry = .ok geometry ∧
        ∃ pending : BatchedWeights, ops.makePending = .ok pending ∧
          Stage2ContinuationLoop.Chain (fun a0 : Accumulator => a0.next.val)
            (Stage2ContinuationOwnedLoop.adapt (fun a0 b0 => call proof p a0 g obs geometry b0))
            a pending outAcc bout 12 := by
  obtain ⟨g,hg,geometry,hgeometry,pending,hpending,hloop⟩ :=
    tx2_query_prefix_success_same_g ops call proof p a gamma obs h
  have hchain := AspisR1Stage2.emitted_twelve_ordered_calls call proof p g obs geometry
    (by
      intro a0 a1 b0 b1 hc
      exact advance g geometry a0 a1 b0 b1 hc)
    a outAcc pending bout start hloop
  exact ⟨g,hg,geometry,hgeometry,pending,hpending,hchain⟩

#print axioms tx2_query_prefix_success_same_g
#print axioms tx2_query_prefix_success_twelve_calls

end AspisR1FastDotsTx2PowersQuerySourceCutV1
