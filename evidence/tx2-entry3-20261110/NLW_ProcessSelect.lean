import NLM_Process221Cuts
set_option autoImplicit false
noncomputable section
namespace NLW_ProcessSelect
open Aeneas Aeneas.Std AspisR1 NLM_Process221
/-- The precise same-data selection; failures of std selection retain their
prefix instead of supplying a chosen route. -/
def fallback (data : Slice U8) : Result Child := do
 let first←Hiq_DispatchSource.eqU8 data (Array.make 2#usize [3#u8,10#u8])
 if first then .ok .first else
 let second←Hiq_DispatchSource.eqU8 data (Array.make 2#usize [3#u8,11#u8])
 if second then .ok .first else .ok .second
def dispatch (data : Slice U8) (head : Option U8) : Result Child :=
 match head with
 | none=>fallback data
 | some byte=>
   if byte=4#u8 then .ok .init else
   if byte=5#u8 then .ok .write else
   if byte=6#u8 then .ok .finalize else fallback data
def selected (data : Slice U8) : Result Child := do
 let head←Hiq_DispatchSource.firstByte data
 let value←Hiq_DispatchSource.copied head
 dispatch data value
/-- Narrowed intermediate source packet. It requests a child law only for
THIS frame/world and the actually selected kind, not all kinds/all frames. -/
def LocalPacket {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (s : NLM_Process221.State Account Ambient) : Prop :=
 ∀ kind,selected s.frame.data=.ok kind →
 NHZ_DRIVER.Cuts hashv (callee kind s.frame s.world)
  (child kind s.frame s.world).result (child kind s.frame s.world).attempted
#print selected
#print LocalPacket
end NLW_ProcessSelect
