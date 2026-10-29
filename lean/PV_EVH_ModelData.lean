import PV_EVH_Deployed
/-! adopted by owner decision D502/D478. Closed synthetic data for the model
satisfiability witness. No operation here is claimed to model a deployed body. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVH_ModelData
open Aeneas Aeneas.Std ProverRwFull

/-- adopted by owner decision D502/D478. Concrete unit external carriers for
the consistency MODEL, with no assumption that any external type is inhabited. -/
def types : ExternalTypes := by
  constructor <;> intros <;> exact Unit

local instance : ExternalTypes := types

/-- adopted by owner decision D502/D478. Concrete synthetic operations, all
returning divergence. This is data inhabitation only, never a source law or
an installation of these operations into the native privacy experiment. -/
def operations : ExternalFuns := by
  constructor <;> intros <;> exact .div

/-- adopted by owner decision D502/D478. Symbolic array shape; no large literal
or recurrence is normalized to establish the length. -/
def filled {T : Type} (n : Usize) (a : T) : Array T n :=
  ⟨List.replicate n.val a,by simp only [List.length_replicate]⟩

/-- adopted by owner decision D502/D478. Small explicit model field element. -/
def zeroQ : aspis_core.field.QM31 := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩

/-- adopted by owner decision D502/D478. Explicit model public snapshot. -/
def snapshot : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  ⟨filled 32#usize 0#u8,filled 32#usize 0#u8,0#u64,0#u64,
    filled 8#usize 0#u32,filled 20#usize (filled 8#usize 0#u32)⟩

/-- adopted by owner decision D502/D478. Explicit model challenge tuple. -/
def challenges : aspis_core.state_only_prefix.r0.Challenges :=
  ⟨zeroQ,zeroQ,zeroQ,filled 10#usize zeroQ,zeroQ,zeroQ⟩

/-- adopted by owner decision D502/D478. Explicit model caller and point for
V244's all-claims binder, not a claim about a reachable deployed semantic oracle. -/
def semantic : host_semantic.SemanticOracle :=
  ⟨.Transfer () ⟨snapshot,()⟩,filled 29#usize ⟨[],by simp⟩,
    challenges,zeroQ,filled 1024#usize zeroQ⟩

def point : Array aspis_core.field.QM31 10#usize := filled 10#usize zeroQ

#print axioms types
#print axioms operations
#print axioms filled
#print axioms semantic
end PV_EVH_ModelData
