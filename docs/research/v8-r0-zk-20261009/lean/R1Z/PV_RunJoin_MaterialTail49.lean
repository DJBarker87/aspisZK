import R1Z.PV_RunJoin_MaterialContinuation49
import R1Z.PV_RunJoin_MaterialImage49
import R1Z.PV_RunJoin_PrepareTailAssociation48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MaterialTail49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (tr : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
    (y1 : alloc.vec.Vec U8) (gamma inactive kappa : W) (q w : Nat → Raw)
    (hq : ∀ j,j<1024 → canonical (q j)) (hw : ∀ j,j<1024 → canonical (w j))
    (request : Result PV_B2_F_AllocationTransport.Outcome) :
    ∃ (c0 : Nat → Raw) (bytes : alloc.vec.Vec U8) (hc0 : ∀ j,j<7 → canonical (c0 j)),
      @PV_RunJoin_MaterialContinuation49.run (types base) (selected base heap box ops)
        (PV_RunJoin_MaterialRun49.outcome request (ok (sourceArray 1024#usize w)))
        (@PV_RunJoin_PrepareTail48.run (types base) (selected base heap box ops) variant hash backend sem
          tr y1 gamma inactive kappa (Array.to_slice (array 1024#usize q)))=
        (do let event ← request
            match event with
            | .denied => ok (.Err .Allocation)
            | .supplied => @PV_RunJoin_PrepareTailAssociation48.retained (types base) (selected base heap box ops)
                variant hash backend sem tr y1 gamma inactive kappa bytes
                (Array.to_slice (array 1024#usize q)) (Array.to_slice (array 1024#usize w))
                (@prover.fold (types base) (@ProverRwP6BodyCandidate.selected (types base) ops))) ∧
      ProverCommitRoundScaled48.run 256 (sourceArray 1024#usize q) (sourceArray 1024#usize w)=
        ok (List.ofFn (fun i : Fin 7 => source (c0 i.val))) ∧
      bytes.val.map PV_RunJoin_WideImage43.byte=ProverCommitOpeningBytes49.stream 7 c0 hc0 := by
  obtain ⟨c0,bytes,hc0,heq,hmodel,hbytes⟩ := PV_RunJoin_PrepareTailAssociation48.complete
    base heap box ops variant hash backend sem tr y1 gamma inactive kappa q w hq hw
  refine ⟨c0,bytes,hc0,?_,hmodel,hbytes⟩
  rw [PV_RunJoin_MaterialContinuation49.complete]
  apply congrArg (Aeneas.Std.bind request)
  funext event
  cases event with
  | denied => rfl
  | supplied =>
    simp only [bind_tc_ok]
    rw [PV_RunJoin_MaterialImage49.complete]
    exact heq
#print axioms complete
end R1Z.PV_RunJoin_MaterialTail49
