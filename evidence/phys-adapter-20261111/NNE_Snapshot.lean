import NNE_Entry
import RSL_TX1_344
set_option autoImplicit false
noncomputable section
namespace NNE_Snapshot
open Aeneas Aeneas.Std AspisR1 S2W_D189Entry S2W_D189Wrappers S2W_ReturnedCheckpoint
abbrev PE := AdapterRw.solana_program_error.ProgramError

def owned (err : PE → RSL.ProgramError) (a : S2W_D189Entry.Owned) : RSL.OwnedAccount :=
 ⟨NNE_Entry.key a.key,NNE_Entry.key a.owner,a.is_signer,a.is_writable,a.executable,
  match a.length with | .Ok n => .ok n.val | .Err e => .error (err e),
  match a.bytes with | .Ok b => .ok (nativeBytes b) | .Err e => .error (err e)⟩

def view (a : RSL.AccountInfo) (s : RSL.SdkState) (l1 l2 : Nat) : RSL.OwnedAccount :=
 let bs := RSL.payload a s
 ⟨a.key,a.owner,a.is_signer,a.is_writable,a.executable,.ok bs.length,
  if bs.length = l1 ∨ bs.length = l2 then .ok bs else .error .invalidAccountData⟩

theorem snapshot_view (err : PE → RSL.ProgramError)
 (invalid : err .InvalidAccountData = .invalidAccountData) (e : Entry) (n i l1 l2 : Nat) :
 owned err (e.snapshot i l1 l2) = view (NNE_Entry.account e i) (NNE_Entry.state e n) l1 l2 := by
 by_cases h : (e.buffers (e.handles i).1).val.length = l1 ∨ (e.buffers (e.handles i).1).val.length = l2
 all_goals
  simp [owned,Entry.snapshot,view,NNE_Entry.account,NNE_Entry.state,RSL.payload,
   nativeBytes,Slice.len,h,invalid]

theorem admitted_sizes (e : Entry) (n count : Nat) (sizes : Nat → Nat × Nat) :
 (List.range count).filterMap (fun i =>
  let len := (RSL.payload (NNE_Entry.account e i) (NNE_Entry.state e n)).length
  if len = (sizes i).1 ∨ len = (sizes i).2 then some len else none) =
 admittedSizes e count sizes := by
 simp only [NNE_Entry.payload,nativeBytes,List.length_map,admittedSizes]

theorem first_lenses : RSL.TX1_344.snapLens = (List.range 3).map firstSizes := rfl

theorem second_lenses : RSL.TX2_240.snapLens = (List.range 7).map secondSizes := rfl

theorem first_snapshots (err : PE → RSL.ProgramError)
 (invalid : err .InvalidAccountData = .invalidAccountData) (e : Entry) (n : Nat) :
 e.first.val.map (owned err) =
 [view (NNE_Entry.account e 0) (NNE_Entry.state e n) 58295 58295,
  view (NNE_Entry.account e 1) (NNE_Entry.state e n) 1880 1880,
  view (NNE_Entry.account e 2) (NNE_Entry.state e n) 1768 1768] := by
 change [owned err (e.snapshot 0 58295 58295),owned err (e.snapshot 1 1880 1880),
  owned err (e.snapshot 2 1768 1768)] = _
 rw [snapshot_view err invalid e n,snapshot_view err invalid e n,snapshot_view err invalid e n]

theorem second_snapshots (err : PE → RSL.ProgramError)
 (invalid : err .InvalidAccountData = .invalidAccountData) (e : Entry) (n : Nat) :
 (e.second secondSizes).val.map (owned err) =
 (List.ofFn (fun i : Fin 7 =>
  view (NNE_Entry.account e i.val) (NNE_Entry.state e n) (secondSizes i.val).1 (secondSizes i.val).2)) := by
 simp only [Entry.second,List.map_ofFn]
 congr 1
 funext i
 exact snapshot_view err invalid e n i.val _ _
#print axioms snapshot_view
#print axioms admitted_sizes
#print axioms first_lenses
#print axioms second_lenses
#print axioms first_snapshots
#print axioms second_snapshots
end NNE_Snapshot
end
