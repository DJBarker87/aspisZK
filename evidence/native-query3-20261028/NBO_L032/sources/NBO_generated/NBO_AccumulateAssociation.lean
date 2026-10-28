import NBO_AllCalls
set_option autoImplicit false
noncomputable section
namespace NBO_AccumulateAssociation
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev sourceOps (ops : Ops) := NBF_Accumulate.install ops
/-- Concrete reference dictionary: both loop callbacks are the SAME emitted
source loops with the installed retained basis/row primitives. No returned
accumulation or loop-result equality is a parameter. -/
def reference (ops : Ops) : AccumulateOps :=
 {zero:=(sourceOps ops).op4,one:=(sourceOps ops).op5,
  basisLoop:=verifier.accumulate_batched_with_node_loop0 (sourceOps ops),
  weightLoop:=verifier.accumulate_batched_with_node_loop1 (sourceOps ops),
  mulE:=(sourceOps ops).op3,addE:=(sourceOps ops).op2,
  trace:=(sourceOps ops).op15,mulK:=(sourceOps ops).op9}
def prefixRun (ops : Ops) (a : verifier.Accumulator) (node : U32)
 (b : verifier.BatchedWeights) : Result verifier.BatchedWeights := do
 let width:=alloc.vec.Vec.len a.weights
 let zero ← (sourceOps ops).op4
 let one ← (sourceOps ops).op5
 let initial ← Array.update (Array.repeat 256#usize zero) 0#usize one
 let basis ← verifier.accumulate_batched_with_node_loop0 (sourceOps ops)
   one node width initial 1#usize
 verifier.accumulate_batched_with_node_loop1 (sourceOps ops)
   {start:=0#usize,«end»:=width} a.weights a.power a.next b width basis
private theorem associate {A B C : Type} (x : Result A) (f : A → Result B)
 (g : B → Result C) : ((x >>= f) >>= g) = (x >>= fun a=>f a >>= g) := by
 cases x <;> rfl
/-- The actual successful row prefix preserves the source counter. -/
theorem prefix_terms (ops : Ops) (a : verifier.Accumulator) (node : U32)
 (b mid : verifier.BatchedWeights) (size : a.weights.val.length=64)
 (raw : b.raw.val.length=64) (run : prefixRun ops a node b=ok mid) : mid.terms=b.terms := by
 have width : alloc.vec.Vec.len a.weights=64#usize := UScalar.eq_of_val_eq size
 unfold prefixRun at run
 rw [width] at run
 iterate 4 obtain ⟨x,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 exact (Port3_NativeRowLoop.fields (sourceOps ops) a.weights a.power a.next 64#usize
   _ 64 {start:=0#usize,«end»:=64#usize} b mid (by decide)
   (by change 64≤b.raw.val.length;omega) run).2
/-- Exact whole Result association to the checked reference accumulation on
its reached numeric domain, including failures/divergence in any child.
Both actual loops are installed above; no successful-final-result is supplied. -/
theorem source (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (node : U32) (value : Stage2E) (b : verifier.BatchedWeights)
 (size : a.weights.val.length=64) (raw : b.raw.val.length=64)
 (active : a.next.val<10) (sync : b.terms=a.next) :
 verifier.accumulate_batched_with_node (sourceOps ops) p a node value b =
 AspisR1Stage2.verifier.accumulateWithOps (reference ops) p a node value b := by
 have next := Port3_Wrapping.checked_add a.next 1#usize (by change a.next.val+1≤4096;omega)
 have nativeShell : verifier.accumulate_batched_with_node (sourceOps ops) p a node value b =
   (do let mid ← prefixRun ops a node b
       let term ← lift (Usize.wrapping_add mid.terms 1#usize)
       let product ← (sourceOps ops).op3 value a.power
       let rhs ← (sourceOps ops).op2 a.rhs product
       (sourceOps ops).op15 11#u16 a.next rhs
       let power ← (sourceOps ops).op9 a.power p.rho
       let successor ← lift (Usize.wrapping_add a.next 1#usize)
       ok ({a with rhs:=rhs,power:=power,next:=successor},{mid with terms:=term})) := by
   unfold verifier.accumulate_batched_with_node prefixRun
   simp only [associate,bind_tc_ok]
 have referenceShell : AspisR1Stage2.verifier.accumulateWithOps (reference ops) p a node value b =
   (do let mid ← prefixRun ops a node b
       let term ← mid.terms+1#usize
       let product ← (sourceOps ops).op3 value a.power
       let rhs ← (sourceOps ops).op2 a.rhs product
       (sourceOps ops).op15 11#u16 a.next rhs
       let power ← (sourceOps ops).op9 a.power p.rho
       let successor ← a.next+1#usize
       ok ({a with rhs:=rhs,power:=power,next:=successor},{mid with terms:=term})) := by
   unfold AspisR1Stage2.verifier.accumulateWithOps reference prefixRun
   simp only [associate,bind_tc_ok]
 rw [nativeShell,referenceShell]
 cases hprefix : prefixRun ops a node b with
 | fail e => rfl
 | div => rfl
 | ok mid =>
   have terms := prefix_terms ops a node b mid size raw hprefix
   have term := Port3_Wrapping.checked_add mid.terms 1#usize
     (by rw [terms,sync];change a.next.val+1≤4096;omega)
   simp only [bind_tc_ok,term,next]
#print axioms associate
#print axioms prefix_terms
#print axioms source
end NBO_AccumulateAssociation
end
