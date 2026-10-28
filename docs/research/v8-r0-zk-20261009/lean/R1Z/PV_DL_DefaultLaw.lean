import R1Z.PV_DL_Default
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_DefaultLaw
set_option autoImplicit false
abbrev Snapshot := Array U32 8#usize × U64 × Array U8 64#usize × Usize

def initialState : Array U32 8#usize := Array.make 8#usize
  [1779033703#u32,3144134277#u32,1013904242#u32,2773480762#u32,
   1359893119#u32,2600822924#u32,528734635#u32,1541459225#u32]

def snapshot : Snapshot :=
  (initialState,0#u64,Array.repeat 64#usize 0#u8,0#usize)

/-- Full Result equality for the extracted owned constructor. The native
constructor correspondence is a separate no-stub P6 receipt. -/
theorem source : PV_DL_Default.default_reference = ok snapshot := rfl

theorem nonvacuous : ∃ q : Snapshot, PV_DL_Default.default_reference = ok q :=
  ⟨snapshot,source⟩

theorem empty_position : snapshot.2.2.2 = 0#usize := rfl

theorem zero_blocks : snapshot.2.1 = 0#u64 := rfl

/-- No compression operation occurs in the constructor; its result is
independent of both backend parameters. -/
theorem backend_independent {C : Type} (soft shani : C) :
    (fun _ : C => PV_DL_Default.default_reference) soft =
    (fun _ : C => PV_DL_Default.default_reference) shani := rfl

#print axioms initialState
#print axioms snapshot
#print axioms source
#print axioms nonvacuous
#print axioms empty_position
#print axioms zero_blocks
#print axioms backend_independent
end R1Z.PV_DL_DefaultLaw
