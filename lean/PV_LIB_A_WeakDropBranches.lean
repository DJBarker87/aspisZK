import PV_LIB_A_WeakDropSource
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakDropBranches
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_THR2_SourceStoreLibrary PV_LIB_A_StorePrimitiveV2 PV_LIB_A_WeakDropSource

/-- A source read of count1 selects deallocation, rather than the old model's
undefined/nonlast restriction. The decrement is always performed first. -/
theorem allocated (C : Carrier PV_EVHB_OwnerMachine.OWNER Data)
    (s post : Store Data) (w : PV_EVHB_OwnerMachine.OWNER) (ptr : Data) (p : Address) (n : Nat)
    (address : C.dereference w ptr = some p)
    (count : numberAt C s {p with fields := p.fields ++ [1,0,0]} = some n)
    (writeCount : writeAddress C s {p with fields := p.fields ++ [1,0,0]}
      (some (.number ((n+modulus-1)%modulus))) = some post) :
    PV_THR2_LibrarySemantics_WeakDropBegin683.allocated C s w ptr =
      some ⟨post,if n = 1 then .deallocate p else .done⟩ := by
  unfold PV_THR2_LibrarySemantics_WeakDropBegin683.allocated
  rw [address]
  change (numberAt C s {p with fields := p.fields ++ [1,0,0]}).bind _ = _
  rw [count]
  change (writeAddress C s {p with fields := p.fields ++ [1,0,0]}
    (some (.number ((n+modulus-1)%modulus)))).bind _ = _
  rw [writeCount]
  rfl

/-- Source pointer aggregates (including the typed-reference codec) do not
accidentally take the raw usize::MAX dangling branch. -/
theorem last_source (C : Carrier PV_EVHB_OwnerMachine.OWNER Data)
    (s post : Store Data) (w : PV_EVHB_OwnerMachine.OWNER) (args : List Data)
    (fields : List (String × Data)) (p : Address)
    (selected : pointer C args s w = some (.object fields))
    (address : C.dereference w (.object fields) = some p)
    (count : numberAt C s {p with fields := p.fields ++ [1,0,0]} = some 1)
    (writeCount : writeAddress C s {p with fields := p.fields ++ [1,0,0]}
      (some (.number ((1+modulus-1)%modulus))) = some post) :
    PV_THR2_LibrarySemantics_WeakDropBegin683 C args s w = some ⟨post,.deallocate p⟩ := by
  unfold PV_THR2_LibrarySemantics_WeakDropBegin683
  rw [selected]
  change PV_THR2_LibrarySemantics_WeakDropBegin683.allocated C s w (.object fields) = _
  rw [allocated C s post w (.object fields) p 1 address count writeCount]
  rfl

/-- BoxNew's source allocation is a root. Its final source lifetime transition
is defined, with no externally supplied final Store or success-only interface. -/
theorem free_root {W E : Type} (C : Carrier W Data) (s : Store Data)
    (a i : Nat) (w : W) (events : List E) (value : Data) :
    finish C (.deallocate ⟨a,i,[]⟩) s ⟨.returned (.ok value),w,events⟩ =
      some (write s ⟨a,i,[]⟩ none) := rfl

theorem free_other_root {W E : Type} (C : Carrier W Data) (s : Store Data)
    (a i : Nat) (w : W) (events : List E) (value : Data) (q : Address)
    (other : q ≠ ⟨a,i,[]⟩) :
    (finish C (.deallocate ⟨a,i,[]⟩) s ⟨.returned (.ok value),w,events⟩).map
      (fun post => post.cells q) = some (s.cells q) := by
  rw [free_root]
  change some (if q = ⟨a,i,[]⟩ then none else s.cells q) = _
  rw [if_neg other]

#print axioms allocated
#print axioms last_source
#print axioms free_root
#print axioms free_other_root
end PV_LIB_A_WeakDropBranches
