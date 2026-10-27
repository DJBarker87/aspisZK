import JHb_RequestCarrier
import JHb_Programs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_RequestBindings
open Aeneas Aeneas.Std Result

theorem profile : (JHb_DataRequest.bytes.drop 8).take 32=AdapterRw.r1_pool_adapter.PROFILE_BINDING.val := by
  unfold AdapterRw.r1_pool_adapter.PROFILE_BINDING
  rfl
#print axioms profile

theorem release : (JHb_DataRequest.bytes.drop 40).take 32=AdapterRw.r1_pool_adapter.RELEASE_BINDING.val := by
  unfold AdapterRw.r1_pool_adapter.RELEASE_BINDING
  rfl
#print axioms release

theorem pool : (JHb_DataRequest.bytes.drop 72).take 32=JHb_Programs.pool.val := by rfl
#print axioms pool

theorem header : JHb_DataRequest.bytes.take 8=[65#u8,83#u8,81#u8,56#u8,1#u8,1#u8,1#u8,0#u8] := by rfl
#print axioms header
end AspisR1.JHb_RequestBindings
end
