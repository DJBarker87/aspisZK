import NDF_RawValue
import CheckpointBytes3Reader
set_option autoImplicit false
namespace NDF_RawBridge
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

def reference (N : Usize) (r : verifier.Reader) : Result (Array U8 N × verifier.Reader) := do
  let (out,finish) ← NDF_ReaderRef.raw_ref N r.bytes r.at
  ok (out,{r with «at»:=finish})

theorem cohort (N : Usize) (r : verifier.Reader) (fit : r.at.val+N.val≤r.bytes.val.length) :
    reference N r = CheckpointBytes3Reader.raw N r := by
  obtain ⟨value,finish,call,contents,endVal⟩ := NDF_RawValue.total N r.bytes r.at fit
  obtain ⟨bytes,out,source,sourceContents,cursor,backing⟩ :=
    OraclePortCkptAbi2Unwrap.raw_panic_unreachable r N (fun _ => fail .panic) fit
  have sameBytes : value=bytes := Subtype.ext (contents.trans sourceContents.symm)
  have sameAt : out.at=finish := UScalar.eq_of_val_eq (cursor.trans endVal.symm)
  have sameOut : out={r with «at»:=finish} := by
    cases out
    cases r
    simp_all
  simp only [reference,call,bind_tc_ok,CheckpointBytes3Reader.raw,source,sameBytes,sameOut]
  rfl

#print axioms cohort
end NDF_RawBridge
