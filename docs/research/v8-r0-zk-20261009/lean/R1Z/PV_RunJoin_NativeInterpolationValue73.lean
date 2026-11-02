import R1Z.PV_RunJoin_NativeInterpolation72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeInterpolationValue73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_FieldData34 (value canonical)
open PV_RunJoin_AccPolynomial38 (poly)
abbrev Q := aspis_core.field.QM31
abbrev K := AspisR1.ExtractedCurrentQM31Exact.QM31Exact

theorem nodes : Function.Injective (fun i : Fin 28 => (i.val : K)) := by
  intro i j h
  have base : (i.val : ZMod AspisCircleGroupOrder.P)=(j.val : ZMod AspisCircleGroupOrder.P) :=
    congrArg (fun q : K => q.re.re) h
  apply Fin.ext
  have hi : i.val<AspisCircleGroupOrder.P := lt_of_lt_of_le i.isLt (by decide)
  have hj : j.val<AspisCircleGroupOrder.P := lt_of_lt_of_le j.isLt (by decide)
  have hv := congrArg ZMod.val base
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using hv

theorem samples (input out : Nat → Q)
    (image : poly out=Lagrange.interpolate Finset.univ
      (fun j : Fin 28 => (j.val : K)) (fun j => value (input j.val))) (i : Fin 28) :
    (poly out).eval (i.val : K)=value (input i.val) := by
  rw [image]
  exact Lagrange.eval_interpolate_at_node (fun _ _ _ _ h => nodes h) (Finset.mem_univ i)

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (values : Array Q 28#usize) :
    ∃ out : Nat → Q,
      @host_sumcheck.interpolate (types base) (opsNative base heap box ops runtime world) values=
        ok (PV_RunJoin_MergeArray35.array out) ∧
      (∀ k,k<28 → canonical (out k)) ∧
      ∀ i : Fin 28,(poly out).eval (i.val : K)=value (PV_RunJoin_InterpolationInput72.cells values i.val) := by
  letI : ExternalTypes := types base
  rw [PV_RunJoin_NativeInterpolation72.dictionary]
  obtain ⟨out,ho,hc,image⟩ := PV_RunJoin_InterpolationComplete38.interpolate
    (residual base ops runtime world) (PV_RunJoin_InterpolationInput72.cells values)
  rw [PV_RunJoin_InterpolationInput72.complete] at ho
  exact ⟨out,ho,hc,samples _ out image⟩

#print axioms nodes
#print axioms samples
#print axioms complete
end R1Z.PV_RunJoin_NativeInterpolationValue73
