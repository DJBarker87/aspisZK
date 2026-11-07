import NNE_AbortIndicator
import NNE_RslOk
import NNE_SnapshotSequence
import NNE_EntryArgs
import NNE_CopyFrame
set_option autoImplicit false
noncomputable section
namespace NNE_PhysicalAccepted
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open RSL
abbrev PE := NNE_Snapshot.PE

def child1 (err : PE → ProgramError) (e : Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8) : TX1_345.Args :=
 ⟨NNE_Entry.key p,e.first.val.map (NNE_Snapshot.owned err),nativeBytes data⟩
def child2 (err : PE → ProgramError) (e : Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (clock : Except ProgramError UInt64) : TX2_241.Args :=
 ⟨NNE_Entry.key p,(e.second secondSizes).val.map (NNE_Snapshot.owned err),nativeBytes data,clock⟩

/-- Output binder selection from the actual write observation. -/
def Out1 (saved : alloc.vec.Vec U8) (o : Obs (Except ProgramError Unit × SdkState)) : Prop :=
 ∀ cell bs, Event.write cell bs ∈ o.events → bs = nativeBytes saved

theorem first (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (err : PE → ProgramError) (invalid : err .InvalidAccountData = .invalidAccountData)
 (native : S2W_ExtractionBoundary.First)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (e : Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8) (env : Env)
 (saved : alloc.vec.Vec U8) (post : SdkState) (es : List Event)
 (ref : TX1_344.Ref V P C (NNE_EntryArgs.args e 3 p data) (NNE_Entry.state e 0) env
   ⟨.ret (.ok (),post),es⟩)
 (out : Out1 saved ⟨.ret (.ok (),post),es⟩)
 (model : ∀ es', TX1_345.Ref V P C (child1 err e p data) env
   ⟨.ret (.ok (nativeBytes saved)),es'⟩ → native p e.first data = ok (.Ok saved)) :
 S2W_D189Wrappers.first native copy NNE_AbortIndicator.allocator e p data true =
 ok (.Ok (saved,writeBracket e.heap 2 0 0 (source (nativeBytes saved)),true)) := by
 obtain ⟨xs,mid,ck,acc2,es1,es2,es3,_,hs,hc,ha,hw,he⟩ :=
  NNE_RslOk.first_ok V P C _ _ _ _ _ ref
 obtain ⟨hxs,hmid⟩ := NNE_SnapshotSequence.first err invalid e 0 env xs mid es1 hs
 subst xs; subst mid
 have ha' : acc2 = NNE_Entry.account e 2 := by
  simpa [NNE_EntryArgs.args] using ha.symm
 subst acc2
 obtain ⟨_,hlen,token,pre,tail,hev,_,_⟩ := NNE_CopyFrame.copy_ok _ _ _ _ _ _ hw
 have member : Event.write (NNE_Entry.account e 2).cell ck ∈ es := by
  rw [he,hev]
  simp
 have hck := out _ _ member
 have called : native p e.first data = ok (.Ok saved) := by
  apply model es2
  simpa only [child1,hck,NNE_EntryArgs.args] using hc
 apply NNE_AbortIndicator.first_return native copy std e p data saved called
 change (e.buffers (e.handles 2).1).val.length = (nativeBytes saved).length
 have len := hlen
 rw [hck] at len
 simpa only [NNE_Entry.payload,nativeBytes,List.length_map] using len.symm

theorem second (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (err : PE → ProgramError) (invalid : err .InvalidAccountData = .invalidAccountData)
 (native : S2W_ExtractionBoundary.Second) (e : Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (slot : S2W_ExtractionBoundary.Slot) (env : Env) (post : SdkState) (es : List Event)
 (ref : TX2_240.Ref L D V (NNE_EntryArgs.args e 7 p data) (NNE_Entry.state e 0) env
   ⟨.ret (.ok (),post),es⟩)
 (model : ∀ es', TX2_241.Ref L D V (child2 err e p data env.clock) env
   ⟨.ret (.ok ()),es'⟩ → native p (e.second secondSizes) data slot = ok (.Ok ())) :
 S2W_D189Wrappers.second native NNE_AbortIndicator.allocator e p data slot true =
 ok (.Ok (e.heap,true)) := by
 obtain ⟨xs,es1,es2,_,hs,_,hc,_⟩ := NNE_RslOk.second_ok L D V _ _ _ _ _ ref
 obtain ⟨hxs,_⟩ := NNE_SnapshotSequence.second err invalid e 0 env xs post es1 hs
 subst xs
 apply NNE_AbortIndicator.second_return native e p data slot
 apply model es2
 simpa only [child2,NNE_EntryArgs.args] using hc
#print axioms first
#print axioms second
end NNE_PhysicalAccepted
end
