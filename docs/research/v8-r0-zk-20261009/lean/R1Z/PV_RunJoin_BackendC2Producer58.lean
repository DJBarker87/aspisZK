import R1Z.PV_RunJoin_BackendHRows58
import R1Z.PV_RunJoin_RecordAppend41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendC2Producer58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMatrix58 PV_RunJoin_BackendPrefix58 PV_RunJoin_BackendQInput58
open PV_RunJoin_ResultPost41

def final (p : Nat → Nat → W) (h : Slice Q) (hh : h.length=1024) (g : Array Q 1024#usize) :=
  filled (filled p 26 (values (PV_RunJoin_BackendHRows58.array h hh)) 1024) 27 (values g) 1024

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (self : prover.Backend) (p : Nat → Nat → W) (hp : self.messages=matrix p)
    (h : Slice Q) (hh : h.length=1024) (g : Array Q 1024#usize) :
    Post (fun out => out.2.messages=matrix (final p h hh g))
      (@prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2
        (types base) (selected base heap box ops) self h g) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2
  rw [PV_RunJoin_BackendHRows58.complete base heap box ops self p hp h hh]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_BackendQRows58.g base heap box ops _ _ rfl g]
  simp only [bind_tc_ok]
  repeat first
  | exact rfl
  | apply PV_RunJoin_ResultPost41.bind; intro value
  | split

#print axioms complete
end R1Z.PV_RunJoin_BackendC2Producer58
