import PV_THR2_BoxDynRepresentationBridge
set_option autoImplicit false
namespace PV_THR2_BoxDynBinaryLayout
open PV_OWN2_Codec
/-- Recount14 typed_representation, binary-structural data. The eleven
fc8808eb native_workers vtables from the existing D690 check. Each row is
indexed by that check's exact spawn/drop/call_once symbol context, retained in
session11/binary-layout/checked-layout.json. The reference-to-physical-data
association and source/binary adequacy are separate; this is not a compiler
correctness theorem. The four excluded monomorphizations are not covered. -/
def addresses : Fin 11 → Pointer
  | ⟨0,_⟩ => ⟨1765816,by decide⟩ -- spawn 0xe0450
  | ⟨1,_⟩ => ⟨1765848,by decide⟩ -- spawn 0xe07c0
  | ⟨2,_⟩ => ⟨1765944,by decide⟩ -- spawn 0xe1220
  | ⟨3,_⟩ => ⟨1765976,by decide⟩ -- spawn 0xe1590
  | ⟨4,_⟩ => ⟨1766008,by decide⟩ -- spawn 0xe1900
  | ⟨5,_⟩ => ⟨1769472,by decide⟩ -- spawn 0x10b750
  | ⟨6,_⟩ => ⟨1769504,by decide⟩ -- spawn 0x10bac0
  | ⟨7,_⟩ => ⟨1769536,by decide⟩ -- spawn 0x10be30
  | ⟨8,_⟩ => ⟨1769568,by decide⟩ -- spawn 0x10c1a0
  | ⟨9,_⟩ => ⟨1769888,by decide⟩ -- spawn 0x10f0e0
  | ⟨10,_⟩ => ⟨1769920,by decide⟩ -- spawn 0x10f450
/-- D690 records ELF virtual addresses. fc8808eb is ET_DYN (PIE), so the
runtime symbol is relocated by the image's load bias. Addition is the ELF64
word operation; mapping/validity belongs to interpretation adequacy. The bias
is fixed loader execution data for the image, never selected per callback. -/
def runtimeAddress (loadBias : Pointer) (siteIndex : Fin 11) : Pointer :=
  loadBias + addresses siteIndex
/-- Install the relocated checked symbol; no run equality is assumed. -/
def symbols (loadBias : Pointer) (siteIndex : Fin 11) : PV_THR2_OperatorSemantics_14119.Symbols :=
  ⟨runtimeAddress loadBias siteIndex⟩
/-- Equality to the relocated binary-layout table. This is binary-structural
data, not a source-refinement or loader-correctness proof. -/
theorem emitted_vtable115 (loadBias : Pointer) (siteIndex : Fin 11) :
    PV_THR2_BoxDynRepresentationBridge.EmittedVtable115 (symbols loadBias siteIndex)
      (runtimeAddress loadBias siteIndex) := rfl
#print axioms emitted_vtable115
end PV_THR2_BoxDynBinaryLayout
