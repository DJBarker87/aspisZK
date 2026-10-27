import R1Z.PV_RunJoin_ParentRoundTotal
import R1Z.PV_RunJoin_RoundTableFacts
import R1Z.PV_Src_ExternalCopy

/-! Assemble the actual threaded source permutation from finite source traces.
Only the actual node compressor's no-op callback is selected. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ParentPermutation
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort PV_Src_PortSboxStep
open PV_RunJoin_SourceRoundFold PV_RunJoin_ParentNoopRounds
open PV_RunJoin_RoundTableFacts PV_RunJoin_RoundTableTrace
open PV_RunJoin_ParentRoundTotal

def run (s : State) : Result State := do
  let e ← R0PoseidonCopy.external_linear s
  let a ← full initials e
  let b ← internal internals a
  full finals b

theorem source (s : State) :
    @poseidon2.permute_optimized_with_trace PV_Src_ExternalReference.dictionary Unit callback s () =
      run s := by
  letI : ExternalLinear := PV_Src_ExternalReference.dictionary
  obtain ⟨e,he,_⟩ := R0Z.PoseidonRefine.external_lift
    (K := ZMod 2147483647) s
  have hce : Canonical e := fun j =>
    R0Z.PoseidonRefine.external_canon s e he j.val j.isLt
  obtain ⟨a,ra,ia,ha,hpa,hca⟩ := full_total_threaded
    (fun i => poseidon2.Poseidon2RoundKind.ExternalInitial (UScalar.cast .U8 i))
    initials e s 0#u8 hce
  obtain ⟨b,rb,ib,hb,hpb,hcb⟩ := internal_total_threaded internals a ia ra hca
  have h0 := PV_RunJoin_SourceInitialRounds.source callback _ _
    (slice_trace poseidon2.EXTERNAL_INITIAL (by decide)) e s () 0#u8 hce initials_canonical
  have h1 := PV_RunJoin_SourceInternalRounds.source callback _ _
    (array_trace poseidon2.INTERNAL) a ia () ra hca internals_canonical
  have h2 := final_source (sliceIter poseidon2.EXTERNAL_FINAL) finals
    (slice_trace poseidon2.EXTERNAL_FINAL (by decide)) b ib rb hcb finals_canonical
  unfold poseidon2.permute_optimized_with_trace poseidon2.permute_optimized_with_trace_threaded
  simp only [PV_Src_ExternalReference.call_eq,PV_Src_ExternalCopy.source,he,bind_tc_ok]
  simp only [lift,bind_tc_ok,bind_assoc_eq,core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,BuilderForestStd.intoIter]
  change (do
    let p ← poseidon2.permute_optimized_with_trace_loop0 callback
      (sliceIter poseidon2.EXTERNAL_INITIAL) e () 0#u8 s
    let q ← poseidon2.permute_optimized_with_trace_loop1 callback
      (arrayIter poseidon2.INTERNAL) p.1 p.2.1 p.2.2.1 p.2.2.2
    let r ← poseidon2.permute_optimized_with_trace_loop2 callback
      (sliceIter poseidon2.EXTERNAL_FINAL) q.1 q.2.1 q.2.2.1 q.2.2.2
    ok r.1) = run s
  dsimp only [initials,internals] at ha hb hpa hpb
  rw [h0,ha]
  simp only [bind_tc_ok]
  rw [h1,hb]
  simp only [bind_tc_ok]
  rw [h2]
  simp only [run,initials,internals,he,bind_tc_ok,hpa,hpb]

#print axioms source
end R1Z.PV_RunJoin_ParentPermutation
