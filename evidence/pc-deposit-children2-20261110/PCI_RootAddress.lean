import PCI_RootRef.Funs
import PCG_CheckpointAddress
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_RootAddress
open PCG_AddressRef
abbrev Key := Array U8 32#usize

def toRequest (q : PCI_RootRef.Request) : Request :=
  ⟨q.program,q.seeds,q.lengths,q.count⟩

def model (program pool : Key) (page : U64) : Request :=
  {program,
   seeds := Array.make 4#usize [Array.make 32#usize [97#u8, 115#u8, 112#u8, 105#u8, 115#u8, 45#u8, 112#u8, 111#u8, 111#u8, 108#u8, 45#u8, 114#u8, 111#u8, 111#u8, 116#u8, 45#u8, 112#u8, 97#u8, 103#u8, 101#u8, 45#u8, 118#u8, 49#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8],pool,
     PCG_CheckpointAddress.padded page,Array.repeat 32#usize 0#u8],
   lengths := Array.make 4#usize [23#usize,32#usize,8#usize,0#usize],count := 3#usize}

def build (program pool : Key) (page : U64) : Result Request := do
  let q ← PCI_RootRef.request280 program pool page
  ok (toRequest q)

theorem le_padded (page : U64) :
    PCI_RootRef.le_padded page = ok (PCG_CheckpointAddress.padded page) := by
  change PCG_AddressRef.le_padded page = _
  exact PCG_CheckpointAddress.le_padded page

theorem request (program pool : Key) (page : U64) :
    build program pool page = ok (model program pool page) := by
  simp only [build,PCI_RootRef.request280,le_padded,bind_tc_ok]
  rfl

theorem descriptor_domain (program pool : Key) (page : U64) :
    PCG_AddressLaws.DescriptorDomain (model program pool page) := by
  simp [PCG_AddressLaws.DescriptorDomain,model,Array.make]

/-- Reuse the CLOSED SDK bridge at SAME seed slices/program id. All statuses,
    returned bytes and bump, abort prefixes and singleton ordered request survive. -/
theorem complete (program pool : Key) (page : U64) (op38 : PCG_AddressRoots.Op38) :
    PCG_AddressRoots.nativeFind (build program pool page) op38 =
      ok ⟨[PCG_RequestCarrier.request (model program pool page)],
        PCG_SdkPda.findReply (op38 (PCG_RequestCarrier.request (model program pool page)))⟩ ∧
    PCG_SdkPda.Domain (PCG_RequestCarrier.request (model program pool page)) ∧
    (PCG_RequestCarrier.request (model program pool page)).program = program ∧
    (PCG_RequestCarrier.request (model program pool page)).seeds.val.length = 3 := by
  constructor
  · rw [request]
    rfl
  · refine ⟨PCG_RequestCarrier.sdk_domain _,rfl,?_⟩
    exact PCG_RequestCarrier.exact_count _ (by simp [model])

#print axioms le_padded
#print axioms request
#print axioms descriptor_domain
#print axioms complete
end PCI_RootAddress
