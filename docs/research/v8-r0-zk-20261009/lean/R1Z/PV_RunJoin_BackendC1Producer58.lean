import R1Z.PV_RunJoin_BackendBaseColumns58
import R1Z.PV_RunJoin_BackendQRows58
import R1Z.PV_RunJoin_RecordAppend41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendC1Producer58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMatrix58 PV_RunJoin_BackendPrefix58 PV_RunJoin_BackendMRows58
open PV_RunJoin_ResultPost41

def final (p : Nat → Nat → W) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024) (d : Array aspis_core.field.QM31 1024#usize) :=
  filled (PV_RunJoin_BackendBasePrefix58.bases p (values columns hlen) 26) 28
    (PV_RunJoin_BackendQInput58.values d) 1024

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (self : prover.Backend) (p : Nat → Nat → W) (hp : self.messages=matrix p)
    (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (d : Array aspis_core.field.QM31 1024#usize) :
    Post (fun out => out.2.messages=matrix (final p columns hlen d))
      (@prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
        (types base) (selected base heap box ops) self columns d) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
  rw [PV_RunJoin_BackendBaseColumns58.complete base heap box ops columns hlen p 26 0#usize rfl self
    (hp.trans (congrArg matrix (PV_RunJoin_BackendBasePrefix58.zero p (values columns hlen))).symm)]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_BackendQRows58.d base heap box ops _ _ rfl d]
  simp only [bind_tc_ok]
  repeat first
  | exact rfl
  | apply PV_RunJoin_ResultPost41.bind; intro value
  | split

#print axioms complete
end R1Z.PV_RunJoin_BackendC1Producer58
