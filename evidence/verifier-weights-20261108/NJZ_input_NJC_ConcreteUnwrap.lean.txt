import NJC_RawPort
import NIL_FreshOps
set_option autoImplicit false
noncomputable section
namespace NJC_ConcreteUnwrap
open Aeneas Aeneas.Std Result NIL_Carriers

/-- Test the concrete pinned Std unwrap only on its entered Ok branch. -/
theorem source (n : Usize) (b : Array U8 n) :
 core.result.Result.unwrap core.fmt.DebugTryFromSliceError (.Ok b)=ok b := by
 rfl

/-- The fresh emitted raw body with its literal Std debug argument restored. -/
def raw (n : Usize) (r : Fresh.R) :=
 NJC_ReaderEmission.verifier.Reader.raw n
  (core.result.Result.unwrap core.fmt.DebugTryFromSliceError) r

theorem bounded (n : Usize) (r : Fresh.R) (bound : r.at.val+n.val≤r.bytes.val.length) :
 ∃ b : Array U8 n, ∃ out : Fresh.R,
 raw n r=ok (b,out) ∧ b.val=(r.bytes.val.drop r.at.val).take n.val ∧
 out.at.val=r.at.val+n.val ∧ out.bytes=r.bytes :=
 NJC_RawPort.bounded n _ (source n) r bound

#print axioms source
#print axioms raw
#print axioms bounded

/-- Complete concrete Std raw body equals the retained reader reference on
all pre-states, not only successful or bounded reads. -/
theorem clause (n : Usize) (r : Fresh.R) : raw n r=NIL_FreshOps.raw n r := by
 unfold raw
 apply NIL_ResultTransport.outer_injective
  (fun p=>(p.1,reader p.2)) (fun p=>(p.1,unReader p.2))
  (fun p=>by rcases p with ⟨b,out⟩;simp only [reader_roundtrip])
 rw [NJC_RawPort.transport,NIL_FreshOps.raw_port]
 rfl

#print axioms clause

end NJC_ConcreteUnwrap
