import RPz7_CPP_Classify
import PoolT_Write
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Write
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry MultiproofConeCanonical
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation
open S2W_EntryWriteHistory S2W_ReturnedCheckpoint
attribute [local instance] Classical.propDecidable

/-- Exhaustive inversion of a committed verifier event. The source route,
original count, actual accepted native reply and actual post-copy bytes are
conclusions. Includes errors, divergence, rejected routes and both TX paths. -/
theorem committed {A : Type} (ops : AdapterRw.Ops)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (store : Store) (input : Invocation A)
    (key : Nat) (image : AspisV8R19.DuplexFrames.Bytes)
    (event : (CPP_Invocation.native n1 n2 copy allocator id store input).2.1 = .committedWrite key image) :
    Hiq_ReleaseRoute.route input.call.data = .first ∧ input.count = 3 ∧
      ∃ saved post final,
        S2W_D189Wrappers.first n1 copy allocator (load store input.call.layout) id input.call.data input.call.state =
          ok (.Ok (saved,post,final)) ∧
        key = (input.call.layout.handles 2).1 ∧ image = bytesOf saved.val ∧
        saved.val.length = 1768 ∧
        payloadBytes encode (post.payload key) 1768 = image ∧
        post.ambient = (load store input.call.layout).heap.ambient ∧
        post.accounts = (load store input.call.layout).heap.accounts ∧
        post.counter = (load store input.call.layout).heap.counter ∧
        (∀ cell, cell ≠ key → post.payload cell = (load store input.call.layout).heap.payload cell) := by
  cases route : Hiq_ReleaseRoute.route input.call.data with
  | reject => rw [CPP_Classify.rejected n1 n2 copy allocator id store input route] at event; cases event
  | second =>
    simp only [CPP_Invocation.native,route] at event
    cases event
  | first =>
    by_cases count : input.count = 3
    · refine ⟨rfl,count,?_⟩
      rw [CPP_Classify.first_valid n1 n2 copy allocator id store input route count] at event
      simp only [Hir_Call.native,route] at event
      cases reply : S2W_D189Wrappers.first n1 copy allocator (load store input.call.layout) id input.call.data input.call.state with
      | fail error => simp only [reply,firstEffect] at event; cases event
      | div => simp only [reply,firstEffect] at event; cases event
      | ok result => cases result with
        | Err error => simp only [reply,firstEffect] at event; cases event
        | Ok value =>
          rcases value with ⟨saved,post,final⟩
          simp only [reply,firstEffect] at event
          obtain ⟨keyEq,imageEq⟩ := S2X.AccountEvent.committedWrite.inj event
          have copied := PoolT_Write.accepted_verifier_writes_copy ops n1 n2 hashv extraction copy std allocator
            (load store input.call.layout) id input.call.data input.call.state final saved post reply
          refine ⟨saved,post,final,rfl,keyEq.symm,imageEq.symm,copied.2.1,?_,copied.2.2.2.1,
            copied.2.2.2.2.1,copied.2.2.2.2.2.1,?_⟩
          · rw [← keyEq,← imageEq]; exact copied.2.2.1
          · intro cell different
            exact copied.2.2.2.2.2.2 cell (by change cell ≠ (input.call.layout.handles 2).1; rw [keyEq]; exact different)
    · rw [CPP_Classify.first_invalid n1 n2 copy allocator id store input route count] at event; cases event

#print axioms committed
end AspisR1.CPP_Write
end
