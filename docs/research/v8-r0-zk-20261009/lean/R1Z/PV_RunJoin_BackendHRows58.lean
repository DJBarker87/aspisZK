import R1Z.PV_RunJoin_BackendQRows58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendHRows58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMatrix58 PV_RunJoin_BackendPrefix58 PV_RunJoin_BackendQInput58

def array (q : Slice Q) (hq : q.length=1024) : Array Q 1024#usize := ⟨q.val,hq⟩

theorem index (q : Slice Q) (hq : q.length=1024) (j : Usize) :
    Slice.index_usize q j=Array.index_usize (array q hq) j := by
  rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (self : prover.Backend) (p : Nat → Nat → W) (hp : self.messages=matrix p)
    (q : Slice Q) (hq : q.length=1024) :
    @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
      (types base) (selected base heap box ops) self q 0#usize=
      ok {self with messages:=matrix (filled p 26 (values (array q hq)) 1024)} := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_BackendRows58.c2_h]
  apply PV_RunJoin_BackendFillPure58.complete _ (values (array q hq))
    _ p 26#usize (by decide) 1024 0#usize rfl self
    (hp.trans (congrArg matrix (PV_RunJoin_BackendPrefix58.zero p 26 (values (array q hq)))).symm)
  intro row hi
  rw [index q hq]
  exact read base heap box ops (array q hq) row hi

#print axioms index
#print axioms complete
end R1Z.PV_RunJoin_BackendHRows58
