import PV_LIB_SPEC_FrozenABI
import PV_LIB_SPEC_ConcreteCaptures
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ArcImageGap
open PV_STX2_Syntax PV_EVHB_OwnerMachine
/-- Adopted ELF fc8808eb, e0580/e0585: malloc(48), alignment8.
The four stores at e059c,e05a3,e05ab,e05b3 initialize words0,8,16,24.
The final word is the None niche 0x8000000000000002. No store reaches32..47.
This is the exact local binary cut, not a source-to-binary refinement theorem. -/
def width : Nat := 48
def alignment : Nat := 8
def strongOffset : Nat := 0
def weakOffset : Nat := 8
def dataOffset : Nat := 16
def dataWidth : Nat := 32

def byte (word i : Nat) : Fin 256 :=
  ⟨word / 256^i % 256,Nat.mod_lt _ (by decide)⟩
/-- Sparse native initial image, including the actual absent-result niche.
Unwritten payload bytes retain the allocator's memory. They are not zeros. -/
def initialImage (scope i : Nat) : Option (Fin 256) :=
  if i < 8 then some (byte 1 i)
  else if i < 16 then some (byte 1 (i-8))
  else if i < 24 then some (byte scope (i-16))
  else if i < 32 then some (byte (2^63+2) (i-24))
  else none

def initializedMemory (p scope : Nat) (memory : Nat → Option Nat) (address : Nat) : Option Nat :=
  if p ≤ address ∧ address < p+32 then
    (initialImage scope (address-p)).map Fin.val
  else memory address

def binaryInitialized (p scope : Nat) (w : OWNER) : OWNER :=
  {w with world := {w.world with memory := initializedMemory p scope w.world.memory}}

theorem source_hole (scope : Nat) (i : Nat) (hole : 32 ≤ i) :
    initialImage scope i = none := by
  simp only [initialImage,if_neg (by omega : ¬ i < 8),
    if_neg (by omega : ¬ i < 16),if_neg (by omega : ¬ i < 24),
    if_neg (by omega : ¬ i < 32)]

theorem binary_frames_payload (p scope i : Nat) (w : OWNER) (hole : 32 ≤ i) :
    (binaryInitialized p scope w).world.memory (p+i) = w.world.memory (p+i) := by
  change initializedMemory p scope w.world.memory (p+i) = _
  exact if_neg (by omega)


/-- Checked pointwise obstruction to EXACT full-memory agreement with the
session6 total-image handler, even if its numeric layout is fixed correctly.
This holds for all source field values; it does not depend on malformed Data.
The only pre-memory used here is the concrete retained initialized entry. -/
theorem total_image_disagrees
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (layout : shape.layout.width = width) (strong weak packet : Data) :
    (PV_THR2_PacketArcInnerBytes.initialized shape strong weak packet 4096
      PV_LIB_SPEC_ConcreteCaptures.state).world.memory 4128 ≠
    (binaryInitialized 4096 0 PV_LIB_SPEC_ConcreteCaptures.state).world.memory 4128 := by
  have inside : 32 < shape.layout.width := by rw [layout]; decide
  have legacy := PV_THR2_PacketArcInnerBytes.inside shape strong weak packet 4096 32
    PV_LIB_SPEC_ConcreteCaptures.state inside
  have binary := binary_frames_payload 4096 0 32 PV_LIB_SPEC_ConcreteCaptures.state (by decide)
  change _ ≠ _
  rw [show (4128 : Nat) = 4096+32 from rfl,legacy,binary]
  change some _ ≠ none
  intro impossible
  cases impossible

/-- No total native image of the current provider Shape can equal this
concrete sparse binary initialization on the complete memory world.
This refutes that exact ABI association, NOT existential OwnInit success,
observational refinement, or the Rust implementation. -/
theorem no_exact_total_image :
    ¬ ∃ shape : PV_THR2_TypedRepresentation_ArcInner.Shape,
      shape.layout.width = width ∧
      ∀ strong weak packet,
        (PV_THR2_PacketArcInnerBytes.initialized shape strong weak packet 4096
          PV_LIB_SPEC_ConcreteCaptures.state).world.memory =
        (binaryInitialized 4096 0 PV_LIB_SPEC_ConcreteCaptures.state).world.memory := by
  rintro ⟨shape,layout,agrees⟩
  exact total_image_disagrees shape layout .null .null .null
    (congrFun (agrees .null .null .null) 4128)

#print axioms width
#print axioms alignment
#print axioms strongOffset
#print axioms weakOffset
#print axioms dataOffset
#print axioms dataWidth
#print axioms byte
#print axioms initialImage
#print axioms initializedMemory
#print axioms binaryInitialized
#print axioms source_hole
#print axioms binary_frames_payload
#print axioms total_image_disagrees
#print axioms no_exact_total_image
end PV_LIB_SPEC_ArcImageGap
