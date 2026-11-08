import PV_LIB_A_WeakCount10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_GuardWeakBegin10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_THR2_SourceStoreLibrary PV_LIB_A_StorePrimitiveV2

/-- Follow the ACTUAL584 guard's two fields to the original NonNull pointer.
The guard source value comes from WeakGuardBuildRun10.guard_root. -/
theorem pointer (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (w : OWNER)
    (types : List Data) (a i root slot heap localIndex : Nat) (nonNull : Data)
    (guard : s.cells ⟨a,i,[]⟩ =
      some (PV_LIB_A_WeakGuardBuild10.guard types nonNull root slot))
    (nonNullPointer : (PV_LIB_A_DestructorValues10.carrier C b).field nonNull 0 =
      some (PV_STX2_TypedReferences.reference ⟨heap,localIndex,[]⟩ .null)) :
    PV_LIB_A_WeakDropSource.pointer (PV_LIB_A_DestructorValues10.carrier C b)
      [PV_STX2_TypedReferences.reference ⟨a,i,[]⟩ .null] s w =
      some (PV_STX2_TypedReferences.reference ⟨heap,localIndex,[]⟩ .null) := by
  have ref : (PV_LIB_A_DestructorValues10.carrier C b).dereference w
      (PV_STX2_TypedReferences.reference ⟨a,i,[]⟩ .null) = some ⟨a,i,[]⟩ :=
    PV_LIB_A_DestructorValues10.reference C b _ _ w
  have first : (PV_LIB_A_DestructorValues10.carrier C b).field
      (PV_LIB_A_WeakGuardBuild10.guard types nonNull root slot) 0 = some nonNull := rfl
  simp [PV_LIB_A_WeakDropSource.pointer,PV_THR2_SourceStoreLibrary.receiver,
    ref,readAddress,readFields,guard,first,nonNullPointer]

/-- Both source Weak branches now derive their pointer, numeric read AND
write-definedness from source aggregates. The post-count Store is calculated;
none of these three results is assumed as a new caller obligation. -/
theorem begin (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (w : OWNER)
    (types : List Data) (a i root slot heap localIndex n : Nat)
    (nonNull strong payload atomicKind unsafeKind : Data)
    (guard : s.cells ⟨a,i,[]⟩ =
      some (PV_LIB_A_WeakGuardBuild10.guard types nonNull root slot))
    (nonNullPointer : (PV_LIB_A_DestructorValues10.carrier C b).field nonNull 0 =
      some (PV_STX2_TypedReferences.reference ⟨heap,localIndex,[]⟩ .null))
    (source : s.cells ⟨heap,localIndex,[]⟩ =
      some (PV_LIB_A_WeakCount10.inner strong payload atomicKind unsafeKind n)) :
    PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683
      (PV_LIB_A_DestructorValues10.carrier C b)
      [PV_STX2_TypedReferences.reference ⟨a,i,[]⟩ .null] s w =
      some ⟨write s ⟨heap,localIndex,[]⟩
        (some (PV_LIB_A_WeakCount10.inner strong payload atomicKind unsafeKind
          ((n+modulus-1)%modulus))),
        if n = 1 then .deallocate ⟨heap,localIndex,[]⟩ else .done⟩ := by
  unfold PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683
  rw [pointer C b s w types a i root slot heap localIndex nonNull guard nonNullPointer]
  exact PV_LIB_A_WeakCount10.allocated C b s w heap localIndex n
    strong payload atomicKind unsafeKind source

#print axioms pointer
#print axioms begin
end PV_LIB_A_GuardWeakBegin10
