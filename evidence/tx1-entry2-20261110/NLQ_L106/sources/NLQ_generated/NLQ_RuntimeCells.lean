import NLQ_SnapshotFrame
set_option autoImplicit false
noncomputable section
namespace NLQ_RuntimeCells
open Aeneas Aeneas.Std AspisR1 AspisR1.S2W_D189Entry
/-- Cell identity is supplied by the SAME runtime admission as the token
ledger. No equality of pointer words is used to infer cell or byte identity. -/
theorem aliases (e : Entry)
 (runtime : AdapterRw.RuntimeEntrypointAdmission e.heap (fun a => (NLM_RuntimeInput.records e a).key) 3)
 (a b : Nat) (ha : a<3) (hb : b<3) :
 (((NLQ_SnapshotFold.final e).sdk.accounts a).data=
  ((NLQ_SnapshotFold.final e).sdk.accounts b).data ↔
  (NLM_RuntimeInput.records e a).key=(NLM_RuntimeInput.records e b).key) := by
 exact NLF_Admission.aliases_exactly e.heap _ 3 a b runtime ha hb
/-- Initial/native counter binding is preserved by all completed snapshots. -/
theorem counters (e : Entry)
 (runtime : AdapterRw.RuntimeEntrypointAdmission e.heap (fun a => (NLM_RuntimeInput.records e a).key) 3)
 (c : Nat) : NLF_RefCell.flag ((NLQ_SnapshotFold.final e).sdk.cells c)=e.heap.counter c :=
 (NLQ_SnapshotFrame.admitted e runtime).2 c
#print aliases
#print axioms aliases
#print axioms counters
end NLQ_RuntimeCells
