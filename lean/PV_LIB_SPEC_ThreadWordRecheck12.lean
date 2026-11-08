import PV_LIB_SPEC_NativeMemory12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ThreadWordRecheck12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984
open PV_LIB_SPEC_ThreadWords12
open PV_LIB_SPEC_AllocationImages

theorem read_away (w : OWNER) (address location value : Nat)
    (disjoint : address+8 ≤ location ∨ location+8 ≤ address) :
    read (write w location value) address = read w address := by
  have memory (i : Fin 8) : (write w location value).world.memory (address+i.val) =
      w.world.memory (address+i.val) := by
    dsimp only [PV_LIB_SPEC_ThreadWords12.write,initialized]
    unfold overwrite
    split
    · have hole : wordImage value (address+i.val-location) = none := by
        exact if_neg (by omega)
      simp only [hole,Option.getD_none]
    · rfl
  unfold PV_LIB_SPEC_ThreadWords12.read
  have bytes : (fun i : Fin 8 => (write w location value).world.memory (address+i.val)) =
      (fun i => w.world.memory (address+i.val)) := funext memory
  rw [bytes]

def one : Pointer := ⟨1,by decide⟩
def inner : Pointer := ⟨16400,by decide⟩
/-- LOCAL initialized word snapshot. This supplies no metadata/live Thread
validity and is not relabelled a reachable original-entry/TLS initialization. -/
def prepared (w : OWNER) : OWNER := write (write w 16384 one.val) 65496 inner.val

theorem tls_word (w : OWNER) : read (prepared w) 65496 = some inner :=
  read_written _ _ _
theorem count_word (w : OWNER) : read (prepared w) 16384 = some one := by
  rw [prepared,read_away _ _ _ _ (Or.inl (by decide))]
  exact read_written _ _ _

/-- Exact native initialized-TLS sequence17c498/17c4a1/17c4ac: the value is
ArcInner16384, not Inner16400, and the native count becomes2. No result image,
full world equality or success-decode premise is chosen for the caller. -/
theorem current_success (w : OWNER) (ignored : Data) (events : List Event) :
    current 65496 (prepared w) ⟨.returned (.ok ignored),prepared w,events⟩ =
      some ⟨.returned (.ok (.number 16384)),write (prepared w) 16384 2,events⟩ := by
  unfold current
  rw [tls_word]
  change increment 16384 (.number 16384) (prepared w)
    ⟨.returned (.ok ignored),prepared w,events⟩ = _
  unfold increment
  rw [count_word]
  rfl

theorem increment_written (w : OWNER) (events : List Event) (value : Data) :
    increment 6144 value (write w 6144 one.val)
      ⟨.returned (.ok .null),write w 6144 one.val,events⟩ =
      some ⟨.returned (.ok value),write (write w 6144 one.val) 6144 2,events⟩ := by
  unfold increment
  rw [read_written]
  rfl

theorem returned_thread_shape :
    PV_THR2_TypedRepresentation_Thread.Shape (.number 16384) := ⟨⟨16384,by decide⟩,rfl⟩

#print axioms read_away
#print axioms one
#print axioms inner
#print axioms prepared
#print axioms tls_word
#print axioms count_word
#print axioms current_success
#print axioms increment_written
#print axioms returned_thread_shape
end PV_LIB_SPEC_ThreadWordRecheck12
