import PV_LIB_A_ActiveDispatch17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActiveSetter17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- CLOSED207 is used with the source Cell argument and true; its native
phase is CLOSED289, including the explicit final Store on every answer.
The boundary consumer does not substitute the old store-free207 contract. -/
theorem closed (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a dest : Nat) (pointer : Address) (parent : Frame) (parents : List Frame)
    (wait : PV_STX2_Native.Waiting Data) (H : (PV_STX2_Native.Request Data → PV_STX_World.World → Reply PV_STX_World.World Event Data)) (w : OWNER)
    (events : List Event) (changes : Address → Option Data) (b : Bool)
    (pre : PV_FN_THREAD_f207_EffectsSummary.Pre s a dest pointer parent parents wait w) :
    PV_FN_THREAD_f207_EffectsSummary.Post base ctl programs s a dest pointer parent parents
      H w events changes b :=
  PV_FN_THREAD_f207_EffectsSummary.contract base ctl programs s a dest pointer parent parents
    wait H w events changes b pre

/-- The exact emitted callback returns the reply of replace(true), not unit. -/
theorem reply (H : Handler) (s : Store Data) (pointer : Address) (w : OWNER) :
    PV_FN_THREAD_f207.reply H s pointer w =
      H (PV_LIB_A_ActiveDispatch17.setter s.nextActivation pointer) w := rfl

/-- The named source action writes the real TLS Cell; it is not an externally
provided effects dictionary or a supplied successful intermediate read. -/
theorem source_write (p : Parameters) (s : Store Data) (w : OWNER) :
    PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_CellReplace289
      (runtime p).carrier (PV_FN_THREAD_f207.args PV_LIB_SPEC_Entry13.slot.source) s w =
      some (write s PV_LIB_SPEC_Entry13.slot.source (some (.boolean true))) :=
  PV_LIB_SPEC_ActiveReplacement16.source_write p s w

/-- Full native physical reply: returned old bool and one byte set to true;
non-success replies remain those of the existing physical setter adapter. -/
theorem physical (p : Parameters) (c : Config) (w : OWNER)
    (active : PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot p c w = some false) :
    PV_LIB_SPEC_CellPhysical13.reply PV_LIB_SPEC_Entry13.slot p c w
      (PV_FN_THREAD_f207.args PV_LIB_SPEC_Entry13.slot.source) ⟨.returned (.ok .null),w,[]⟩ =
      some ⟨.returned (.ok (.boolean false)),
        PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot w true,[]⟩ :=
  PV_LIB_SPEC_ActiveReplacement16.physical p c w active

#print axioms closed
#print axioms reply
#print axioms source_write
#print axioms physical
end PV_LIB_A_ActiveSetter17
