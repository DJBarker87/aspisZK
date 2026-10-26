import CPP_Write
import CPP_Metadata
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_CommitGeometry
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry MultiproofConeCanonical
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation

/-- Every committed dispatcher write derives an actual native reply with no
account deallocation, changed data descriptor, or live guard left behind.
These exclude source close/realloc possibilities on the accepted copy path. -/
theorem committed {A : Type} (ops : AdapterRw.Ops)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (store : Store) (input : Invocation A)
    (key : Nat) (image : AspisV8R19.DuplexFrames.Bytes)
    (event : (CPP_Invocation.native n1 n2 copy allocator id store input).2.1 = .committedWrite key image) :
    ∃ saved post final,
      S2W_D189Wrappers.first n1 copy allocator (load store input.call.layout) id input.call.data input.call.state =
        ok (.Ok (saved,post,final)) ∧
      key = (input.call.layout.handles 2).1 ∧ image = bytesOf saved.val ∧
      post.guards = [] ∧
      post.allocated = (load store input.call.layout).heap.allocated ∧
      post.ownerLive = (load store input.call.layout).heap.ownerLive ∧
      ∀ cell, (post.payload cell).descriptor = ((load store input.call.layout).heap.payload cell).descriptor := by
  obtain ⟨route,count,saved,post,final,accepted,keyEq,imageEq,size,bytes,ambient,accounts,counter,other⟩ :=
    CPP_Write.committed ops n1 n2 hashv extraction copy std allocator id store input key image event
  have frame := CPP_Metadata.first_frame n1 copy std allocator (load store input.call.layout)
    id input.call.data input.call.state final saved post accepted
  exact ⟨saved,post,final,accepted,keyEq,imageEq,frame.2.2.2.2.1,frame.2.2.2.2.2.1,
    frame.2.2.2.2.2.2.1,frame.2.2.2.2.2.2.2.1⟩

#print axioms committed
end AspisR1.CPP_CommitGeometry
end
