import Lean
import NFN_PhaseTransport
import NFS_NEV_RowLoop
import NFS_NEV_BasisProducer
import NFS_NEV_AccumulateTail
import NEI_AccumIndependentCounters

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_AccumulatePrefix
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody

theorem installs_commute (ops : Ops) :
    NBF_BasisInstall.install (NBF_RowInstall.install ops)=NBF_Accumulate.install ops := rfl

/-- Exact prefix including initialization, six-level basis production and all
64 rows. No successful prefix output is supplied as a hypothesis. -/
theorem association (ops : Ops) (a : NEV_AccumulateRaw.Accumulator) (node : U32)
    (b : NEV_AccumulateRaw.BatchedWeights) (width : a.weights.val.length=64)
    (raw : b.raw.val.length=64) (global : a.next.val<22) :
    (do let out ← NFS_NEV_AccumulateTail.rows a node b;ok (toWeights out)) =
      NBO_AccumulateAssociation.prefixRun ops (toAccumulator a) node (toWeights b) := by
  have rawWidth : alloc.vec.Vec.len a.weights=64#usize := UScalar.eq_of_val_eq width
  have modelWidth : alloc.vec.Vec.len (toAccumulator a).weights=64#usize := by
    apply UScalar.eq_of_val_eq
    change (mapVec toQ a.weights).val.length=64
    simpa only [mapVec,List.length_map] using width
  have source : NFS_NEV_AccumulateTail.rows a node b=
      (do let basis ← NFS_NEV_BasisProducer.source node
          NEV_AccumulateRaw.accumulate_batched_with_node_loop1
            {start:=0#usize,«end»:=64#usize} a.weights a.power a.next b 64#usize basis) := by
    unfold NFS_NEV_AccumulateTail.rows NFS_NEV_BasisProducer.source
    rw [rawWidth]
    simp only [NEV_AccumulateRaw.aspis_core.field.M31.ZERO,
      NEV_AccumulateRaw.aspis_core.field.M31.ONE,bind_tc_ok,bind_assoc_eq]
  have target : NBO_AccumulateAssociation.prefixRun ops (toAccumulator a) node (toWeights b)=
      (do let basis ← NBF_BasisDomain.source (NBF_RowInstall.install ops) node
          verifier.accumulate_batched_with_node_loop1 (NBF_Accumulate.install ops)
            {start:=0#usize,«end»:=64#usize} (mapVec toQ a.weights) (toQ a.power)
            a.next (toWeights b) 64#usize basis) := by
    unfold NBO_AccumulateAssociation.prefixRun NBF_BasisDomain.source
    rw [modelWidth]
    rw [installs_commute]
    rfl
  rw [source,target]
  simp only [bind_assoc_eq]
  rw [NFS_NEV_BasisProducer.association (NBF_RowInstall.install ops) node]
  have continuation :
      (fun basis : Array U32 256#usize =>
        do let out ← NEV_AccumulateRaw.accumulate_batched_with_node_loop1
             {start:=0#usize,«end»:=64#usize} a.weights a.power a.next b 64#usize basis
           ok (toWeights out)) =
      (fun basis : Array U32 256#usize =>
        verifier.accumulate_batched_with_node_loop1 (NBF_Accumulate.install ops)
          {start:=0#usize,«end»:=64#usize} (mapVec toQ a.weights) (toQ a.power)
          a.next (toWeights b) 64#usize basis) := by
    funext basis
    exact NFS_NEV_RowLoop.association (NBF_BasisInstall.install ops)
      a.weights a.power a.next basis 64 {start:=0#usize,«end»:=64#usize} b
      width raw rfl rfl global
  exact congrArg (fun continuation : Array U32 256#usize → Result AspisR1Stage2.verifier.BatchedWeights =>
    do let basis ← NBF_BasisDomain.source (NBF_RowInstall.install ops) node
       continuation basis) continuation
#print axioms installs_commute
#print axioms association
end NFS_NEV_AccumulatePrefix
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
