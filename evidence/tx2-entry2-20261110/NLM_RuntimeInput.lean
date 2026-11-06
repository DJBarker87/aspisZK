import NLF_SdkBorrowLaw
import S2W_D189Entry
set_option autoImplicit false
noncomputable section
namespace NLM_RuntimeInput
open Aeneas Aeneas.Std AspisR1 AspisR1.S2W_D189Entry
open AspisR1.S2W_ReturnedCheckpoint AspisR1.S2W_CommittedCheckpoint
/-- Metadata is selected by the SAME admitted data cell; no unrelated byte
buffer or independently chosen cell map enters the parent. -/
def records (e : Entry) (a : Nat) : NLF_SdkModel.Account :=
 let r := e.records (e.handles a).1
 ⟨nativeBytes r.owned.key.to_slice,nativeBytes r.owned.owner.to_slice,
  (e.handles a).1,(e.handles a).2,r.owned.is_signer,r.owned.is_writable,
  r.owned.executable,r.rentEpoch⟩
def money (e : Entry) (i : Nat) : Nat := (e.records i).lamports
def initial (e : Entry) : NLF_ParentModel.Parent :=
 NLF_RuntimeInterpretation.install e.heap (records e) (money e)
/-- Full byte equality, obtained from the payload contents. Address/length
metadata alone is deliberately insufficient for this theorem. -/
theorem payload_bytes (e : Entry) (i : Nat) :
 NLF_RuntimeInterpretation.byteList e.heap i = nativeBytes (e.buffers i) := by
 apply List.ext_getElem
 · simp [NLF_RuntimeInterpretation.byteList,Entry.heap,Entry.payload,nativeBytes]
 · intro j hj hk
   simp [NLF_RuntimeInterpretation.byteList,Entry.heap,Entry.payload,source, List.getElem?_eq_getElem hk]
/-- The SDK projection reads the exact buffer that Entry.snapshot selects. -/
theorem initial_payload (e : Entry) (a : Nat) :
 ((initial e).state.cells ((initial e).state.accounts a).data).payload.bytes =
 nativeBytes (e.buffers (e.handles a).1) := by
 exact payload_bytes e (e.handles a).1
#print records
#print initial
#print axioms payload_bytes
#print axioms initial_payload
end NLM_RuntimeInput
