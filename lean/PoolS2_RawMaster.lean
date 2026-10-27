import PoolS2_RawSnapshot
import PoolS2_MasterFacts
set_option autoImplicit false
namespace AspisR1.PoolS2_RawMaster
open Aeneas Aeneas.Std Result S2W_D189Entry PoolS2_PdaSource PoolS2_PdaSeeds

theorem accepted (e : Entry) (slot : Nat) (decode : PoolS2_MasterRead.Decode) (pda : Ops)
    (program : Key) (writable : Bool) (master : Master)
    (h : PoolS2_MasterRead.run decode pda program (PoolS2_RawSnapshot.snapshot e slot) writable = ok (.Ok master)) :
    decode (e.buffers (e.handles slot).1) = ok (.Ok master) ∧
    master.identity.pool = (e.records (e.handles slot).1).owned.key ∧
    pda.create (masterCreate master.identity.asset_mint master.bump) program =
      ok (.Ok (e.records (e.handles slot).1).owned.key) := by
  obtain ⟨_,_,_,_,bytes,read,decoded,created,identity⟩ :=
    PoolS2_MasterFacts.accepted decode pda program _ writable master h
  have same : bytes = e.buffers (e.handles slot).1 :=
    core.result.Result.Ok.inj (read.symm.trans (PoolS2_RawSnapshot.raw e slot).1)
  subst bytes
  exact ⟨decoded,identity,created⟩

#print axioms accepted
end AspisR1.PoolS2_RawMaster
