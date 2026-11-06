import NJC_RawPort
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
end NJC_ConcreteUnwrap
