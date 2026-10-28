import R1Z.PV_RDB2D_CollectorCases
namespace R1Z.PV_RDB2D_CollectorRequests
open Aeneas Aeneas.Std Result PV_RDB1_V183_ReserveWorld
open PV_RDB2D_CollectorTrace PV_RDB2D_CollectorProgram PV_RDB2D_CollectorCases
set_option autoImplicit false

def first : Request := ⟨2,0,127,⟨8,alignment2⟩⟩
def second (p : Nat) : Request := ⟨p,127,254,⟨8,alignment2⟩⟩
def third : Request := ⟨2,0,272,⟨2,alignment2⟩⟩

theorem first_public : publicRequest first=.allocate 1016 2 := rfl
theorem second_public (p : Nat) : publicRequest (second p)=.reallocate 1016 2 2032 := by
  simp only [publicRequest,second,alignment2_word,show ¬((127:Nat)=0) by omega,ite_false]
  norm_num
theorem third_public : publicRequest third=.allocate 544 2 := rfl

theorem retained_length (p : Nat) : (retained p).values.length=64 := by
  exact (List.length_map _).trans PV_RDB2D_CollectorShape.filtered_length

theorem second_exact (p : Nat) :
    (⟨(retained p).address,(retained p).capacity,(retained p).values.length+190,⟨8,alignment2⟩⟩ : Request)=second p := by
  rw [retained_length]
  rfl

def initializedLegacy {S F : Type} (p : Nat) (s : S) (state : State S F) : State S F :=
  store p (.links PV_B3P_Schedule133.legacyLinks) (afterRequest first (some p) s state)

def initializedForest {S F : Type} (p1 p2 : Nat) (s : S) (state : State S F) : State S F :=
  store p2 (.links (PV_B3P_Schedule133.forestLinks PV_B3P_Schedule133.legacyLinks))
    (afterRequest (second p1) (some p2) s (filtered p1 state))

theorem after_first {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F)
    (state : State S F) (p : Nat) (s : S)
    (h : allocate first state.resource.allocator=ok (some p,s)) :
    source allocate deallocate handler state =
      reserveReference allocate deallocate handler p (initializedLegacy p s state) := by
  rw [PV_RDB2D_CollectorProgram.complete]
  unfold PV_RDB2D_CollectorProgram.reference
  exact success allocate handler _ _ _ _ _ p s h

theorem second_null {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F)
    (state : State S F) (p : Nat) (s : S)
    (h : allocate (second p) (filtered p state).resource.allocator=ok (none,s)) :
    reserveReference allocate deallocate handler p state =
      abortWith handler 2032 (afterRequest (second p) none s (filtered p state)) := by
  unfold reserveReference
  have hh : allocate ⟨(retained p).address,(retained p).capacity,(retained p).values.length+190,⟨8,alignment2⟩⟩
    (filtered p state).resource.allocator=ok (none,s) := by rw [second_exact]; exact h
  rw [null allocate handler _ _ _ _ _ s hh,second_exact,retained_length]
  congr 1 <;> omega


theorem after_second {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F)
    (state : State S F) (p1 p2 : Nat) (s : S)
    (h : allocate (second p1) (filtered p1 state).resource.allocator=ok (some p2,s)) :
    reserveReference allocate deallocate handler p1 state =
      flatReference allocate deallocate handler p2 (initializedForest p1 p2 s state) := by
  unfold reserveReference
  have hh : allocate ⟨(retained p1).address,(retained p1).capacity,(retained p1).values.length+190,⟨8,alignment2⟩⟩
    (filtered p1 state).resource.allocator=ok (some p2,s) := by rw [second_exact]; exact h
  rw [success allocate handler _ _ _ _ _ p2 s hh,second_exact]
  rfl


theorem third_null {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F)
    (state : State S F) (linkAddress : Nat) (s : S)
    (h : allocate third state.resource.allocator=ok (none,s)) :
    flatReference allocate deallocate handler linkAddress state =
      abortWith handler 544 (afterRequest third none s state) := by
  unfold flatReference
  exact null allocate handler _ _ _ _ _ s h


theorem after_third {S F : Type} (allocate : Allocator S)
    (deallocate : Nat → Nat → Nat → S → Result S) (handler : Handler S F)
    (state : State S F) (linkAddress rowAddress : Nat) (s : S)
    (h : allocate third state.resource.allocator=ok (some rowAddress,s)) :
    flatReference allocate deallocate handler linkAddress state =
      afterFlat deallocate linkAddress rowAddress PV_B3P_Sorted133.expected
        (afterRequest third (some rowAddress) s state) := by
  unfold flatReference
  exact success allocate handler _ _ _ _ _ rowAddress s h

#print axioms first_public
#print axioms second_public
#print axioms third_public
#print axioms retained_length
#print axioms second_exact
#print axioms after_first
#print axioms second_null
#print axioms after_second
#print axioms third_null
#print axioms after_third
end R1Z.PV_RDB2D_CollectorRequests
