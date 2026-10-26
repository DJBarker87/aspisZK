import CPS_EntryFlags
import CPS_PhysicalKey
import Hiq_KeyLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_Ordinary
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers

/-- Runtime meaning of ordinary, with each exclusion visible. -/
def ordinary (fee : Hist_Authority.Key) (nonce : Hist_Authority.Key → Prop)
    (key : Hist_Authority.Key) : Prop := key ≠ fee ∧ ¬ nonce key

/-- The exact owner guard on the original accepted source entry. -/
theorem owner {A : Type} (ops : AdapterRw.Ops) (keyLaw : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (e : Entry) (id : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (state final : A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first n1 copy allocator e id data state = ok (.Ok (saved,post,final))) :
    (e.records (e.handles 2).1).owned.owner = id := by
  have native := (first_accepted n1 copy std allocator e id data state final saved post accepted).1
  have source := (extraction.stage1 id e.first data).symm.trans native
  obtain ⟨ca,index,owned⟩ := Hist_Authority.accepted_owner ops id e.first data saved
    (by simpa only [Hiq_KeyLaw.installed_eq ops keyLaw] using source)
  have same := Result.ok.inj (index.symm.trans (first_index e).2.2)
  subst ca
  exact owned

/-- Source privileges plus explicit runtime signature/nonce interpretations
suffice. These two interpretation premises are NOT in entry admission and are
not adopted trust. This statement exposes the remaining boundary. -/
theorem of_flags (e : Entry) (id system fee : Hist_Authority.Key)
    (nonce : Hist_Authority.Key → Prop)
    (signer : (e.records (e.handles 2).1).owned.is_signer = false)
    (owned : (e.records (e.handles 2).1).owned.owner = id)
    (distinct : id ≠ system)
    (feeSigner : CPS_PhysicalKey.key e 2 = fee →
      (e.records (e.handles 2).1).owned.is_signer = true)
    (nonceOwner : nonce (CPS_PhysicalKey.key e 2) →
      (e.records (e.handles 2).1).owned.owner = system) :
    ordinary fee nonce (CPS_PhysicalKey.key e 2) := by
  refine ⟨CPS_EntryFlags.not_fee_payer _ _ _ signer feeSigner,?_⟩
  intro active
  exact distinct (owned.symm.trans (nonceOwner active))

#print axioms owner
#print axioms of_flags
end AspisR1.CPS_Ordinary
end
