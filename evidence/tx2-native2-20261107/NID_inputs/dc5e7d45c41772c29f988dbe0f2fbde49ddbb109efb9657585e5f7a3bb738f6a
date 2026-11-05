import NID_BoundedReaders
set_option autoImplicit false
noncomputable section
namespace NID_ReadListTransport
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 CheckpointBytes4Sections

/-- Full Result transport through sequential checkpoint reads. Bounds and
backing for every successor are derived from the executed predecessor's exact
codec return; no unrelated reader state or successful suffix is supplied. -/
theorem source (unwrap : T2Nat_RawJoin.Unwrap)
 (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b) (n : Nat) (r : verifier.Reader)
 (bound : r.at.val+16*n≤r.bytes.val.length) :
 readList (T2Nat_ScalarJoin.readK unwrap) n r=readList CheckpointBytes3Reader.readK n r := by
 induction n generalizing r with
 | zero => rfl
 | succ n ih =>
   obtain ⟨b,out,_,cursor,backing,run⟩ := CheckpointBytes3Reader.read_k_c5 r (by omega)
   have head := NID_BoundedReaders.k unwrap unwrap_ok r (by omega)
   simp only [readList,head,run,bind_tc_ok]
   cases value : CheckpointBytes3Reader.optionK
     ((ExactLeafFieldCodec.decodeQM31 (MultiproofConeCanonical.bytesOf b.val)).map CheckpointBytes3KDecode.rawK) with
   | Err err => rfl
   | Ok x =>
     dsimp only
     rw [ih out (by rw [cursor,backing];omega)]
#print axioms source
end NID_ReadListTransport
