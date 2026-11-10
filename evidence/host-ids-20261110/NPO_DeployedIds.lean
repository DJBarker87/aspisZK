import LIB_Deployed
import CPH_Program
set_option autoImplicit false
noncomputable section
namespace NPO_DeployedIds
open Aeneas Aeneas.Std
/-! Program ids of the two devnet deployments, decoded from base58 by NPO_base58.py
(alphabet 123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz; round-trip checked).
10 November 2026 (NPC_DEVNET_RESULT.md): verifier GqZzWuGT (ELF 2331ad8a), whose embedded
Pool-id slot holds 37hdATMk and whose registry-id slot is unchanged (9pWwAcBg).
29 October 2026: verifier CSnhzGdH (ELF 63ad3e9c), Pool BmsNikL9, registry program 9pWwAcBg.
`pool`/`registry` are the verifier's AUDIT_POOL_PROGRAM / AUDIT_REGISTRY_PROGRAM slots
(r1_pool_adapter.rs), i.e. what LIB_Deployed.ids and NHJ_IdPacket.install carry. -/
/-- GqZzWuGTojfsxYnDzmyWKhdPGkce19xN1Txu9Vgnr5hy -/
def verifierNov : AspisR1.S2W_ExtractionBoundary.Program :=
  Array.make 32#usize [235#u8, 80#u8, 124#u8, 139#u8, 156#u8, 94#u8, 152#u8, 233#u8, 165#u8, 85#u8, 129#u8, 140#u8, 237#u8, 232#u8, 178#u8, 255#u8, 133#u8, 31#u8, 95#u8, 251#u8, 181#u8, 184#u8, 69#u8, 201#u8, 157#u8, 112#u8, 244#u8, 47#u8, 89#u8, 111#u8, 123#u8, 176#u8]
/-- 37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt -/
def poolNov : NHJ_IdPacket.KeyBytes :=
  Array.make 32#usize [31#u8, 110#u8, 202#u8, 182#u8, 93#u8, 211#u8, 209#u8, 31#u8, 180#u8, 240#u8, 151#u8, 201#u8, 64#u8, 153#u8, 187#u8, 138#u8, 102#u8, 240#u8, 42#u8, 47#u8, 45#u8, 80#u8, 255#u8, 230#u8, 102#u8, 102#u8, 205#u8, 28#u8, 125#u8, 189#u8, 44#u8, 235#u8]
/-- 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q -/
def registryNov : NHJ_IdPacket.KeyBytes :=
  Array.make 32#usize [131#u8, 9#u8, 163#u8, 201#u8, 153#u8, 45#u8, 35#u8, 222#u8, 189#u8, 104#u8, 139#u8, 224#u8, 185#u8, 96#u8, 72#u8, 135#u8, 226#u8, 88#u8, 106#u8, 68#u8, 10#u8, 156#u8, 60#u8, 72#u8, 82#u8, 28#u8, 53#u8, 49#u8, 227#u8, 146#u8, 232#u8, 171#u8]
/-- CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ -/
def verifierOct : AspisR1.S2W_ExtractionBoundary.Program :=
  Array.make 32#usize [170#u8, 11#u8, 193#u8, 210#u8, 222#u8, 217#u8, 63#u8, 11#u8, 239#u8, 54#u8, 55#u8, 125#u8, 220#u8, 28#u8, 12#u8, 148#u8, 104#u8, 109#u8, 23#u8, 35#u8, 117#u8, 190#u8, 244#u8, 173#u8, 165#u8, 123#u8, 230#u8, 201#u8, 120#u8, 178#u8, 48#u8, 201#u8]
/-- BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs -/
def poolOct : NHJ_IdPacket.KeyBytes :=
  Array.make 32#usize [160#u8, 19#u8, 98#u8, 42#u8, 240#u8, 202#u8, 109#u8, 154#u8, 218#u8, 233#u8, 162#u8, 167#u8, 169#u8, 176#u8, 187#u8, 66#u8, 122#u8, 69#u8, 190#u8, 75#u8, 195#u8, 45#u8, 233#u8, 50#u8, 40#u8, 58#u8, 26#u8, 66#u8, 26#u8, 133#u8, 145#u8, 52#u8]
/-- 9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q -/
def registryOct : NHJ_IdPacket.KeyBytes :=
  Array.make 32#usize [131#u8, 9#u8, 163#u8, 201#u8, 153#u8, 45#u8, 35#u8, 222#u8, 189#u8, 104#u8, 139#u8, 224#u8, 185#u8, 96#u8, 72#u8, 135#u8, 226#u8, 88#u8, 106#u8, 68#u8, 10#u8, 156#u8, 60#u8, 72#u8, 82#u8, 28#u8, 53#u8, 49#u8, 227#u8, 146#u8, 232#u8, 171#u8]
/-- The 29 October Pool/registry ids are the already-pinned devnet packet ids. -/
theorem poolOct_devnet : poolOct = NHJ_IdPacket.poolDevnet := rfl
theorem registryOct_devnet : registryOct = NHJ_IdPacket.registryDevnet := rfl
/-- The registry program is the same in both deployments. -/
theorem registry_same : registryNov = registryOct := rfl
/-- The re-instantiated D values, as RSL.DeployedIds (same carrier as LIB_Deployed.ids). -/
def DNov : RSL.DeployedIds := ⟨LIB_Carriers.b32 poolNov, LIB_Carriers.b32 registryNov⟩
def DOct : RSL.DeployedIds := ⟨LIB_Carriers.b32 poolOct, LIB_Carriers.b32 registryOct⟩
theorem DOct_devnet : DOct = LIB_Deployed.devnet := rfl
/-- Restatement of AspisR1.CPH_Program.not_system at the 10 November verifier id. The original
proof compares the literal head byte (95 = 0x5f of 7Q2nGsPg) with 0, so it does not transfer; the
same proof with the new head byte (235) does. -/
theorem not_systemNov : verifierNov ≠ AspisR1.Hist_Nonvacuity.key 0#u8 := by
  intro same
  have head := congrArg (fun key : AspisR1.S2W_ExtractionBoundary.Program => key.val[0]?) same
  change some (235#u8) = some (0#u8) at head
  exact (by decide : (235#u8) ≠ 0#u8) (Option.some.inj head)
/-- The same at the 29 October verifier id (head byte 170). -/
theorem not_systemOct : verifierOct ≠ AspisR1.Hist_Nonvacuity.key 0#u8 := by
  intro same
  have head := congrArg (fun key : AspisR1.S2W_ExtractionBoundary.Program => key.val[0]?) same
  change some (170#u8) = some (0#u8) at head
  exact (by decide : (170#u8) ≠ 0#u8) (Option.some.inj head)
end NPO_DeployedIds
end
#print axioms NPO_DeployedIds.poolOct_devnet
#print axioms NPO_DeployedIds.registryOct_devnet
#print axioms NPO_DeployedIds.registry_same
#print axioms NPO_DeployedIds.DOct_devnet
#print axioms NPO_DeployedIds.not_systemNov
#print axioms NPO_DeployedIds.not_systemOct
