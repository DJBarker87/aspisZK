import R1Z.PV_RunJoin_BackendWrite58
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendRows58
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_RunJoin_BackendMatrix58
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31

def body (read : Usize → Result W) (lane : Usize) (self : prover.Backend) (row : Usize) :
    Result (ControlFlow (prover.Backend × Usize) prover.Backend) := do
  if row<1024#usize then
    let value ← read row
    let next ← PV_RunJoin_BackendWrite58.write self lane row value
    let row1 ← Aeneas.Std.lift (Usize.wrapping_add row 1#usize)
    ok (cont (next,row1))
  else ok (done self)

def run (read : Usize → Result W) (lane : Usize) (self : prover.Backend) (row : Usize) :=
  loop (fun (s,r) => body read lane s r) (self,row)

theorem c2_g (self : prover.Backend) (g : Array Q 1024#usize) (row : Usize) :
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1 self g row=
      run (fun j => do let q ← Array.index_usize g j; aspis_core.field.wide_exact.WideExact.from_qm31 q) 27#usize self row := by
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1 run
  congr 1
  funext pair
  rcases pair with ⟨s,r⟩
  simp only [prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop1.body,
    body,PV_RunJoin_BackendWrite58.write,bind_assoc_eq,bind_tc_ok,lift,Aeneas.Std.uncurry]

theorem c2_h (self : prover.Backend) (h : Slice Q) (row : Usize) :
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0 self h row=
      run (fun j => do let q ← Slice.index_usize h j; aspis_core.field.wide_exact.WideExact.from_qm31 q) 26#usize self row := by
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0 run
  congr 1
  funext pair
  rcases pair with ⟨s,r⟩
  simp only [prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0.body,
    body,PV_RunJoin_BackendWrite58.write,bind_assoc_eq,bind_tc_ok,lift,Aeneas.Std.uncurry]

theorem c1_d (self : prover.Backend) (d : Array Q 1024#usize) (row : Usize) :
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1 self d row=
      run (fun j => do let q ← Array.index_usize d j; aspis_core.field.wide_exact.WideExact.from_qm31 q) 28#usize self row := by
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1 run
  congr 1
  funext pair
  rcases pair with ⟨s,r⟩
  simp only [prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop1.body,
    body,PV_RunJoin_BackendWrite58.write,bind_assoc_eq,bind_tc_ok,lift,Aeneas.Std.uncurry]

theorem c1_base (self : prover.Backend) (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (lane row : Usize) :
    prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0 self columns lane row=
      run (fun j => do
        let column ← Array.index_usize columns lane
        let m ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice aspis_core.field.M31) column j
        aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 m) lane self row := by
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0 run
  congr 1
  funext pair
  rcases pair with ⟨s,r⟩
  simp only [prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0_loop0.body,
    body,PV_RunJoin_BackendWrite58.write,bind_assoc_eq,bind_tc_ok,lift,Aeneas.Std.uncurry]

#print axioms c1_base
#print axioms c2_g
#print axioms c2_h
#print axioms c1_d
end R1Z.PV_RunJoin_BackendRows58
