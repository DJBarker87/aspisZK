import RPz7_CPR_DataWriter
import Hist_Metadata
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_EntryFlags
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers

/-- Actual writer acceptance supplies CP privileges on the original Entry.
No fee-payer or durable-nonce metadata is present in Entry. -/
theorem writer {A : Type} (ops : AdapterRw.Ops)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (state final : A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first n1 copy allocator e id data state = ok (.Ok (saved,post,final))) :
    (e.records (e.handles 2).1).owned.is_signer = false ∧
    (e.records (e.handles 2).1).owned.executable = false ∧
    (e.records (e.handles 2).1).owned.is_writable = true := by
  have native := (first_accepted n1 copy std allocator e id data state final saved post accepted).1
  have source := (extraction.stage1 id e.first data).symm.trans native
  obtain ⟨pa,pu,ca,_,_,index,_,_,guard⟩ := S2W_EntryPrivileges.guards ops id e.first data saved source
  have same := Result.ok.inj (index.symm.trans (first_index e).2.2)
  subst ca
  exact Hist_Metadata.checkpoint_flags ops (e.snapshot 2 1768 1768) id true guard

/-- The runtime signature rule, when separately represented, excludes the
fee payer. This theorem does not manufacture that missing runtime rule. -/
theorem not_fee_payer {Key : Type} (key fee : Key) (signer : Bool)
    (nonsigning : signer = false) (feeSigner : key = fee → signer = true) : key ≠ fee := by
  intro same
  have impossible := feeSigner same
  rw [nonsigning] at impossible
  cases impossible

#print axioms writer
#print axioms not_fee_payer
end AspisR1.CPS_EntryFlags
end
