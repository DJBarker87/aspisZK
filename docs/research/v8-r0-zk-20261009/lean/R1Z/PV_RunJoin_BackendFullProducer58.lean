import R1Z.PV_RunJoin_BackendC1Producer58
import R1Z.PV_RunJoin_BackendC2Producer58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendFullProducer58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMatrix58 PV_RunJoin_BackendMRows58 PV_RunJoin_BackendPrefix58
abbrev Q := aspis_core.field.QM31

def final (p : Nat → Nat → W) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024) (d : Array Q 1024#usize)
    (h : Slice Q) (hh : h.length=1024) (g : Array Q 1024#usize) :=
  PV_RunJoin_BackendC2Producer58.final (PV_RunJoin_BackendC1Producer58.final p columns hlen d) h hh g

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (start first last : prover.Backend) (p : Nat → Nat → W) (hp : start.messages=matrix p)
    (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (d g : Array Q 1024#usize) (h : Slice Q) (hh : h.length=1024)
    (root1 root2 : Array U8 32#usize)
    (hc1 : @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
      (types base) (selected base heap box ops) start columns d=ok (.Ok root1,first))
    (hc2 : @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2
      (types base) (selected base heap box ops) first h g=ok (.Ok root2,last)) :
    last.messages=matrix (final p columns hlen d h hh g) := by
  have hfirst := PV_RunJoin_BackendC1Producer58.complete base heap box ops start p hp columns hlen d
  rw [hc1] at hfirst
  change first.messages=matrix (PV_RunJoin_BackendC1Producer58.final p columns hlen d) at hfirst
  have hlast := PV_RunJoin_BackendC2Producer58.complete base heap box ops first _ hfirst h hh g
  rw [hc2] at hlast
  exact hlast

#print axioms complete
end R1Z.PV_RunJoin_BackendFullProducer58
