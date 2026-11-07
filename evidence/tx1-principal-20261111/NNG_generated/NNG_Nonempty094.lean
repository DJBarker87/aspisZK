import NNG_DomainFinding094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Nonempty094
open Aeneas Aeneas.Std Result

def bytes32 : Array U8 32#usize:=Array.repeat 32#usize 0#u8
def words : Array U32 8#usize:=Array.repeat 8#usize 0#u32
def frontier : Array (Array U32 8#usize) 20#usize:=Array.repeat 20#usize words
def public_ : LIB_VCarriers.Public:=
 .Withdrawal ⟨bytes32,bytes32,0#u64,words,words,0#u32,0#u32,bytes32,words⟩
  ⟨⟨bytes32,bytes32,0#u64,0#u64,words,frontier⟩,⟨0#u64,words,frontier⟩⟩

theorem words_canonical : NJX_DigestCohort.dc words := by
 intro x member
 change x ∈ List.replicate 8 0#u32 at member
 have same: x=0#u32:=(List.mem_replicate.mp member).2
 subst x
 decide
#print axioms words_canonical

theorem frontier_canonical : ∀ d∈frontier.val,NJX_DigestCohort.dc d := by
 intro d member
 change d∈List.replicate 20 words at member
 have same : d=words:=(List.mem_replicate.mp member).2
 subst d
 exact words_canonical
#print axioms frontier_canonical

theorem public_domain : LIB_Instances.VL.publicDom public_ := by
 exact ⟨words_canonical,words_canonical,(by intro d impossible;cases impossible),words_canonical,
    frontier_canonical,words_canonical,frontier_canonical⟩
#print axioms public_domain

theorem no_candidate : ¬∃ impl,RSL.TX1_094.RowSpec_094 LIB_Instances.VL LIB_Instances.P impl := by
 rintro ⟨impl,candidate⟩
 exact NNG_DomainFinding094.rejects_all_implementations public_ public_domain impl candidate
#print axioms no_candidate
end AspisR1.NNG_Nonempty094
