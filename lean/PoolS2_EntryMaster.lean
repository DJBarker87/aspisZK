import PoolS2_MasterStage
import PoolS2_RawMaster
import PoolS2_RawPrefix
set_option autoImplicit false
namespace AspisR1.PoolS2_EntryMaster
open Aeneas Aeneas.Std Result S2W_D189Entry PoolS2_PdaSource PoolS2_PdaSeeds

/-- ONE partial owned stage, interpreted over original entry buffers. This
is not the native P1 planner/caller theorem. No successful child is assumed. -/
theorem accepted (e : Entry) (decode : PoolS2_MasterRead.Decode) (pda : Ops)
    (program : Key) (data : Slice U8) (r : PoolS2_Prefix.Roles) (m : Master)
    (h : PoolS2_MasterStage.run decode pda program (PoolS2_RawSnapshot.accounts e) data = ok (.Ok (r,m))) :
    decode (e.buffers (e.handles 0).1) = ok (.Ok m) ∧
    m.identity.pool = (e.records (e.handles 0).1).owned.key ∧
    pda.create (masterCreate m.identity.asset_mint m.bump) program =
      ok (.Ok (e.records (e.handles 0).1).owned.key) ∧
    (e.heap.accounts 0).1 ≠ (e.heap.accounts 9).1 := by
  obtain ⟨front,read⟩ := PoolS2_MasterStage.accepted decode pda program _ data r m h
  have selected := (PoolS2_RawPrefix.roles e data r front).1
  rw [selected] at read
  obtain ⟨decoded,identity,created⟩ := PoolS2_RawMaster.accepted e 0 decode pda program true m read
  exact ⟨decoded,identity,created,PoolS2_RawPrefix.data_cells e data r front⟩

#print axioms accepted
end AspisR1.PoolS2_EntryMaster
