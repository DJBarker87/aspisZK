import NDI_ReaderByteBridge
import NDF_RawBridge
set_option autoImplicit false
namespace NDI_ReaderCohort
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem selected_byte (width : Usize) (r : verifier.Reader) (coordinate : Usize)
    (fit : r.at.val+width.val≤r.bytes.val.length) (bound : coordinate.val<width.val) :
    ∃ out finish value,
      CheckpointBytes3Reader.raw width r=ok (out,{r with «at»:=finish}) ∧
      NDI_ReaderByteRef.raw_byte_ref r.bytes r.at width coordinate=ok (value,finish) ∧
      out.val[coordinate.val]?=some value := by
  obtain ⟨out,finish,value,call,byte,cell⟩ :=
    NDI_ReaderByteBridge.reference width r.bytes r.at coordinate fit bound
  have ref : NDF_RawBridge.reference width r=ok (out,{r with «at»:=finish}) := by
    simp only [NDF_RawBridge.reference,call,bind_tc_ok]
  rw [NDF_RawBridge.cohort width r fit] at ref
  exact ⟨out,finish,value,ref,byte,cell⟩

#print axioms selected_byte
end NDI_ReaderCohort
