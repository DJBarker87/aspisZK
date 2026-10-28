import NDO_NBX_SlotValues
import PoolS2_PolicyExact
import NDO_NCX_JHuObservations
import NDO_JHu_FixturePdaRuntime
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_Leaves
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

/-- Canonical BPF upgradeable loader ID, as bytes. This is a constant SDK
interpretation, not a successful authentication callback. -/
def loader : solana_pubkey.Pubkey := Array.make 32#usize [
  2#u8,168#u8,246#u8,145#u8,78#u8,136#u8,161#u8,176#u8,
  226#u8,16#u8,21#u8,62#u8,247#u8,99#u8,174#u8,43#u8,
  0#u8,194#u8,185#u8,61#u8,22#u8,193#u8,36#u8,210#u8,
  192#u8,83#u8,122#u8,16#u8,4#u8,128#u8,0#u8,0#u8]

theorem loader_fixture : loader=JHj_RegistryValue.loader := by
  apply Subtype.ext
  change _ = (JHb_DataRegistry.bytes.drop 152).take 32
  exact JHg_AuditRegistry.loader.symm
#print axioms loader_fixture

/-- Existing total policy/status source interpretations, canonical SDK ID,
and the two existing decoder installations. No acceptance result is installed. -/
def install (base : Ops) : Ops :=
  NCV_Install.install (NCX_Install.install
    {NBX_SlotValues.instantiate base with op41:=ok loader})

theorem runtime (base : Ops) (h : JHu_FixturePdaRuntime.FixturePdaRuntime base) :
    JHu_FixturePdaRuntime.FixturePdaRuntime (install base) := h
#print axioms runtime
end AspisR1.JHv_Leaves
end
