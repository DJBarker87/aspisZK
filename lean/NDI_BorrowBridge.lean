import NDI_TranscriptBorrow.Funs
import NDI_TranscriptRef.Funs
set_option autoImplicit false
namespace NDI_BorrowBridge
open Aeneas Aeneas.Std Result

theorem initial (reply : Array U8 32#usize) (coordinate : Usize) :
    NDI_TranscriptBorrow.transcript_new_byte_borrow_ref reply coordinate =
      NDI_TranscriptRef.transcript_new_byte_ref reply coordinate := rfl

theorem sample (block advanced : Array U8 32#usize) (row : U8) (coordinate : Usize) :
    NDI_TranscriptBorrow.transcript_sample_byte_borrow_ref block advanced row coordinate =
      NDI_TranscriptRef.transcript_sample_byte_ref block advanced row coordinate := rfl

#print axioms initial
#print axioms sample
end NDI_BorrowBridge
