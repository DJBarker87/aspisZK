import NMC_AllSlotFrames
import NMC_EraseBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Records
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
def Origin {H : Type} (s : NLC_Finish.State H) (row : U8)
 (slot : Option r1_wire.ValidatedRecord) : Prop :=
 ∀ record, slot = some record → r1_wire.Prefix.validated_record s.input.prefix1 row = ok (.Ok record)
def step {H : Type} (s : NLC_Finish.State H) (row : U8) (event : NLC_Finish.Event)
 (store : r1_wire.ValidatedRecord→Locals H) : PreparedHashCode.Code (NLC_Finish.Post H) := do
 let result ← r1_wire.Prefix.validated_record s.input.prefix1 row
 pure (NLC_Finish.returned s event result store)
theorem written {H : Type} (s after : NLC_Finish.State H) (row : U8) (event : NLC_Finish.Event)
 (store : r1_wire.ValidatedRecord→Locals H) (select : Locals H→Option r1_wire.ValidatedRecord)
 (selected : ∀ record,select (store record)=some record)
 (head : (PreparedHashCode.run (step s row event store)).2=ok (.inr after)) :
 Origin after row (select after.locals) := by
 have actual : PreparedHashCode.erase (step s row event store)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 change (do let result ← r1_wire.Prefix.validated_record s.input.prefix1 row
            ok (NLC_Finish.returned s event result store))=ok (.inr after) at actual
 cases child : r1_wire.Prefix.validated_record s.input.prefix1 row with
 | fail error=>rw [child] at actual;cases actual
 | div=>rw [child] at actual;cases actual
 | ok result=>cases result with
   | Err error=>simp only [child,bind_tc_ok,NLC_Finish.returned] at actual;cases actual
   | Ok value=>
     simp only [child,bind_tc_ok,NLC_Finish.returned] at actual
     have chosen:=Sum.inr.inj (Result.ok.inj actual)
     cases chosen
     intro record stored
     rw [selected] at stored
     cases Option.some.inj stored
     exact child
theorem some_slot {T : Type} (slot : Option T) (ready : slot.isSome=true) : ∃ value,slot=some value := by
 cases slot with
 | none=>cases ready
 | some value=>exact ⟨value,rfl⟩
#print axioms written
#print axioms some_slot
end AspisR1.NMC_Records
end
