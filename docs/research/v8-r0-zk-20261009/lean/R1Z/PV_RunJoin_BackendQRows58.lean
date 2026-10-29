import R1Z.PV_RunJoin_BackendQInput58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendQRows58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMatrix58 PV_RunJoin_BackendPrefix58 PV_RunJoin_BackendQInput58
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem g (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (self : prover.Backend) (p : Nat → Nat → W) (hp : self.messages=matrix p)
    (q : Array Q 1024#usize) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1
      (types base) (selected base heap box ops) self q 0#usize=
      ok {self with messages:=matrix (filled p 27 (values q) 1024)} := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_BackendRows58.c2_g]
  exact PV_RunJoin_BackendFillPure58.complete _ (values q)
    (read base heap box ops q) p 27#usize (by decide) 1024 0#usize rfl self
    (by simpa only [PV_RunJoin_BackendPrefix58.zero] using hp)

theorem d (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (self : prover.Backend) (p : Nat → Nat → W) (hp : self.messages=matrix p)
    (q : Array Q 1024#usize) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1
      (types base) (selected base heap box ops) self q 0#usize=
      ok {self with messages:=matrix (filled p 28 (values q) 1024)} := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_BackendRows58.c1_d]
  exact PV_RunJoin_BackendFillPure58.complete _ (values q)
    (read base heap box ops q) p 28#usize (by decide) 1024 0#usize rfl self
    (by simpa only [PV_RunJoin_BackendPrefix58.zero] using hp)

#print axioms g
#print axioms d
end R1Z.PV_RunJoin_BackendQRows58
