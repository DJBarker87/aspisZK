import NNC_SnapshotRep
import TAS_Interfaces
set_option autoImplicit false
noncomputable section
namespace NNC_R0Rep
open Aeneas Aeneas.Std AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open RSL.TAS
/-- Selected occurrence's exact snapshot/read/range association. This is
representation data; no Root0, acceptance or hash equality is hidden in it. -/
structure SnapshotCut (S : Sig) (c : S.Ctx) (s : SecondCut) where
 post : RSL.SdkState
 owned : List RSL.OwnedAccount
 env : RSL.Env
 events : List RSL.Event
 snapshots : RSL.TX2_240.snapAll (S.args2 c).accounts RSL.TX2_240.snapLens (S.state2 c)
  env ⟨.ret (owned,post),events⟩
 a0 : RSL.AccountInfo
 a6 : RSL.AccountInfo
 x0 : RSL.OwnedAccount
 x6 : RSL.OwnedAccount
 at0 : (S.args2 c).accounts[0]?=some a0
 at6 : (S.args2 c).accounts[6]?=some a6
 owned0 : owned[0]?=some x0
 owned6 : owned[6]?=some x6
 read0 : x0.bytes=.ok (NNC_ByteCarriers.host s.raw.val)
 read6 : x6.bytes=.ok (NNC_ByteCarriers.host s.checkpoint.val)
 range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  s.raw {start:=688#usize,«end»:=s.finish}=Aeneas.Std.Result.ok s.proof
 finish : s.finish.val=58295
 length : s.raw.val.length=58295

/-- Exact TAS R0-rep fold, using the CLOSED snapshot law. `selected` is the
host's definition/unpacking of Root0Native at the SAME occurrence; it must
be installed, rather than postulated as new runtime or cryptographic trust. -/
def assemble (S : Sig) (V0 : RSL.TX2_241.V2Lib)
 (canonical : V0.Root0=NNC_ByteCarriers.Root0)
 (selected : ∀ c, S.Root0Native c →
  ∃ s, Nonempty (SnapshotCut S c s) ∧ NLP_InputDomain.Root0 s.checkpoint s.proof) :
 RSL.TAS.NNC_R0Rep S V0 where
 rep := by
  intro c a0 a6 root _ at0 at6 _ _
  obtain ⟨s,⟨cut⟩,root⟩ := selected c root
  have same0 := Option.some.inj (cut.at0.symm.trans at0)
  have same6 := Option.some.inj (cut.at6.symm.trans at6)
  subst a0
  subst a6
  have representation := NNC_SnapshotRep.from_snapshots s (S.args2 c).accounts
   (S.state2 c) cut.post cut.owned cut.env cut.events cut.snapshots
   cut.a0 cut.a6 cut.x0 cut.x6 cut.at0 cut.at6 cut.owned0 cut.owned6
   cut.read0 cut.read6 cut.range cut.finish cut.length
  rw [canonical]
  exact representation.2.2.mpr root

#print axioms assemble
end NNC_R0Rep
