import PV_LIB_SPEC_AllocationImages
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_AllocationSites
open PV_LIB_SPEC_AllocationImages
/-- Native sites, NOT erased generic allocation tokens. Two sites can have the
same width yet distinct fields, byte stores, source operands and provenance. -/
inductive Site where
  | scope_fa099 | packet_e058a | callback_e05e8 | init_e064b | thread_17be96
  deriving DecidableEq
structure CopyOperands where
  snapshot : Memory
  rsp : Nat
  packetPointer : Nat
  capturePointer : Nat
  captureLength : Nat

def Operands : Site → Type
  | .scope_fa099 => Nat
  | .packet_e058a => Nat
  | .callback_e05e8 => CopyOperands
  | .init_e064b => Nat × Nat × Nat
  | .thread_17be96 => Nat × Nat × Nat

def width : Site → Nat
  | .scope_fa099 => 40
  | .packet_e058a => 48
  | .callback_e05e8 => 56
  | .init_e064b => 24
  | .thread_17be96 => 48

def alignment (_ : Site) : Nat := 8
/-- These particular binary cuts write contiguous prefixes; the model does
not generalize this to other allocations or to Vec spare capacity. -/
def writtenLength : Site → Nat
  | .scope_fa099 => 33
  | .packet_e058a => 32
  | .callback_e05e8 => 56
  | .init_e064b => 24
  | .thread_17be96 => 44

def image : (site : Site) → Operands site → Image
  | .scope_fa099,threadPointer => scope threadPointer
  | .packet_e058a,scopePointer => packet scopePointer
  | .callback_e05e8,args => callback args.snapshot args.rsp args.packetPointer args.capturePointer args.captureLength
  | .init_e064b,(handle,callbackPointer,vtable) => threadInit handle callbackPointer vtable
  | .thread_17be96,(id,namePointer,nameLength) => threadInner id namePointer nameLength

theorem scope_mask (threadPointer i : Nat) : scope threadPointer i = none ↔ 33 ≤ i := by
  by_cases hole : 33 ≤ i
  · exact ⟨fun _ => hole,fun _ => scope_hole _ _ hole⟩
  · simp only [scope,word]
    split <;> try { simp only [Option.some_ne_none,false_iff]; omega }
    split <;> try { simp only [Option.some_ne_none,false_iff]; omega }
    split <;> try { simp only [Option.some_ne_none,false_iff]; omega }
    split <;> try { simp only [Option.some_ne_none,false_iff]; omega }
    rw [if_pos (by omega)]
    simp only [Option.some_ne_none,false_iff]; omega

theorem packet_mask (scopePointer i : Nat) : packet scopePointer i = none ↔ 32 ≤ i := by
  unfold packet PV_LIB_SPEC_SparseArc.image PV_LIB_SPEC_ArcImageGap.initialImage
  split <;> try { simp only [Option.map_some,Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [Option.map_some,Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [Option.map_some,Option.some_ne_none,false_iff]; omega }
  split <;> simp only [Option.map_some,Option.map_none,Option.some_ne_none,false_iff,true_iff] <;> omega

theorem callback_mask (args : CopyOperands) (i : Nat) :
    callback args.snapshot args.rsp args.packetPointer args.capturePointer args.captureLength i = none ↔ 56 ≤ i := by
  unfold callback
  split <;> try { simp only [Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> simp only [word,Option.some_ne_none,false_iff,true_iff] <;> omega

theorem init_mask (handle callbackPointer vtable i : Nat) :
    threadInit handle callbackPointer vtable i = none ↔ 24 ≤ i := by
  unfold threadInit
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> simp only [word,Option.some_ne_none,false_iff,true_iff] <;> omega

theorem thread_mask (id namePointer nameLength i : Nat) :
    threadInner id namePointer nameLength i = none ↔ 44 ≤ i := by
  unfold threadInner
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> simp only [Option.some_ne_none,false_iff,true_iff] <;> omega

/-- Exact support for EVERY site and operand, including copied unknown bytes.
Every no-store byte is outside this support; no whole-layout initializer is
substituted for the actual binary stores. -/
theorem mask (site : Site) (args : Operands site) (i : Nat) :
    image site args i = none ↔ writtenLength site ≤ i := by
  cases site with
  | scope_fa099 => exact scope_mask args i
  | packet_e058a => exact packet_mask args i
  | callback_e05e8 => exact callback_mask args i
  | init_e064b => exact init_mask args.1 args.2.1 args.2.2 i
  | thread_17be96 => exact thread_mask args.1 args.2.1 args.2.2 i

theorem stores_within_layout (site : Site) (args : Operands site) (i : Nat)
    (store : image site args i ≠ none) : i < width site := by
  have support := mask site args i
  have absent : ¬ writtenLength site ≤ i := fun h => store (support.2 h)
  have small : i < writtenLength site := by omega
  cases site <;> simp only [writtenLength,width] at small ⊢ <;> omega

theorem retains_tail (site : Site) (args : Operands site) (p i : Nat) (before : Memory)
    (unwritten : writtenLength site ≤ i) :
    overwrite p (image site args) before (p+i) = before (p+i) := by
  apply hole
  rw [Nat.add_sub_cancel_left]
  exact (mask site args i).2 unwritten

#print axioms Site
#print axioms CopyOperands
#print axioms Operands
#print axioms width
#print axioms alignment
#print axioms writtenLength
#print axioms image
#print axioms scope_mask
#print axioms packet_mask
#print axioms callback_mask
#print axioms init_mask
#print axioms thread_mask
#print axioms mask
#print axioms stores_within_layout
#print axioms retains_tail
end PV_LIB_SPEC_AllocationSites
