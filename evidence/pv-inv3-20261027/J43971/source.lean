import R1Z.PV_Inv_BankCompression
import R1Z.PV_Inv_GlobalPairs
set_option autoImplicit false
namespace R1Z.PV_Inv_EntryReference
open R0P PV_Inv_BankSource PV_Inv_RegistryInput PV_Inv_RawSlots
variable {K W : Type} [Field K]

abbrev Key := Fin 1024 × Bool

def producer (banks : Banks K) (lambda : K) (weight : SourceLink K → W)
    (l : SourceLink K) : Key × Entry K W :=
  ((l.producer.row,true),⟨PV_Inv_BankCompression.producer banks lambda l,weight l⟩)
def consumer (banks : Banks K) (lambda : K) (weight : SourceLink K → W)
    (l : SourceLink K) : Key × Entry K W :=
  ((l.consumer.row,false),⟨PV_Inv_BankCompression.consumer banks lambda l,weight l⟩)

/-- Structural row-builder reference, preserving the native interleaved order.
Unlike the terminal static slots, zero-weight entries can be overwritten. -/
def entries (banks : Banks K) (lambda : K) (weight : SourceLink K → W)
    (registry : List (SourceLink K)) : List (Key × Entry K W) :=
  PV_Inv_GlobalPairs.endpoints (producer banks lambda weight) (consumer banks lambda weight) registry

theorem member (banks : Banks K) (lambda : K) (weight : SourceLink K → W)
    (registry : List (SourceLink K)) (e : Key × Entry K W)
    (he : e ∈ entries banks lambda weight registry) :
    ∃ l ∈ registry, e = producer banks lambda weight l ∨ e = consumer banks lambda weight l := by
  obtain ⟨l,hl,he⟩ := List.mem_flatMap.mp he
  refine ⟨l,hl,?_⟩
  simpa only [List.mem_cons,List.not_mem_nil,or_false] using he

#print axioms member
end R1Z.PV_Inv_EntryReference
