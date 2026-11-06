import NKA_InitHistory
import NKA_ClaimsReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_HeapCarrier
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames
open NKA_InitializedPrefix
abbrev Claims := NJT_ClaimsWindows.Claims
abbrev Status := core.result.Result Claims r1_wire.Error

def rows (value : Claims) : Rows := fun p i=>
 NJG_NativeCuts.word (cell (cell value p) ⟨i.val/4,by change i.val/4<29;omega⟩) ⟨i.val%4,by omega⟩

structure RowPost where
 outcome : Result (core.result.Result Unit r1_wire.Error)
 memory : Memory
 written : Bool
abbrev RowNative := Fin 3 → (Fin 116 → U32) → Memory → RowPost
abbrev memoryNative (native : RowNative) : Native := fun p row before=>(native p row before).memory

/-- Successful SAME-row projection of the complete NJM_K011/K012 Result and
initialized-prefix frame assertion. Decoder success is established by the
SAME parsed caller in the root; it is not a root hypothesis. -/
def RowCut (native : RowNative) : Prop :=
 Cut (memoryNative native) ∧
 ∀ p row before,(native p row before).outcome=ok (.Ok ()) ∧ (native p row before).written=true

structure BoxPost where
 value : Claims
 owner : Nat
 length : Nat
abbrev BoxNative := Nat → NKA_InitHistory.Storage → BoxPost
/-- NJM_K006/K007/K008: assume_init returns the original owned allocation,
with every observed u32 unchanged. The data prefix comes from complete and typed-write readiness from the
actual runRows history; neither is a caller success or pointer-equality premise. The safe
singleton carrier is NJT_K003/K004/K005 and the pinned Aeneas Slice model. -/
def BoxCut (native : BoxNative) : Prop :=
 ∀ (owner : Nat) (value : Claims) (storage : NKA_InitHistory.Storage),
 NKA_InitHistory.Ready storage → Prefix (rows value) 3 storage.memory →
 (native owner storage).owner=owner ∧ (native owner storage).length=1 ∧
 ∀ (p : Fin 3) (k : Fin 29) (limb : Fin 4),
 NJG_NativeCuts.word (cell (cell (native owner storage).value p) k) limb=
 NJG_NativeCuts.word (cell (cell value p) k) limb

def runRows (native : RowNative) (value : Claims) : List (Fin 3) → NKA_InitHistory.Storage →
 Result (core.result.Result NKA_InitHistory.Storage r1_wire.Error)
 | [],before => ok (.Ok before)
 | p::ps,before => do
  let post:=native p (rows value p) before.memory
  let result ← post.outcome
  match result with
  | .Err e => ok (.Err e)
  | .Ok _ =>
   let writes:=if post.written then p::before.writes else before.writes
   runRows native value ps ⟨post.memory,writes⟩

theorem row_returned (native : RowNative) (cut : RowCut native)
 (p : Fin 3) (row : Fin 116 → U32) (before : Memory) :
 (native p row before).outcome=ok (.Ok ()) := (cut.2 p row before).1

theorem typed_write (native : RowNative) (cut : RowCut native)
 (p : Fin 3) (row : Fin 116 → U32) (before : Memory) :
 (native p row before).written=true := (cut.2 p row before).2

/-- The history follows the SAME native completed-write flags (K029/K030).
It is derived from empty fresh storage, not supplied as a caller premise. -/
theorem runRows_source (native : RowNative) (cut : RowCut native) (value : Claims) (before : Memory) :
 runRows native value [0,1,2] ⟨before,[]⟩=
 ok (.Ok (NKA_InitHistory.completed (run (memoryNative native) (rows value) before))) := by
 simp only [runRows,row_returned native cut,typed_write native cut,bind_tc_ok,if_true]
 rfl

def result (reservation : NP6_StdModel.Reservation) (native : RowNative)
 (box : BoxNative) (owner : Nat) (before : Memory) (value : Claims) : Result Status :=
 match reservation with
 | .Err _ => ok (.Err .Allocation)
 | .Ok _ => do
  let status ← runRows native value [0,1,2] ⟨before,[]⟩
  match status with
  | .Err e => ok (.Err e)
  | .Ok memory => ok (.Ok (box owner memory).value)

/-- Full returning Result of forward-instantiated native windows. Prefix
initializedness is derived before the owned-carrier cast; every successful
row outcome is discharged by the exact native stage assertion. -/
theorem source (reservation : NP6_StdModel.Reservation) (native : RowNative)
 (cut : RowCut native) (box : BoxNative) (boxCut : BoxCut box)
 (owner : Nat) (before : Memory) (value : Claims) :
 result reservation native box owner before value=
 (match reservation with | .Err _=>ok (.Err .Allocation) | .Ok _=>ok (.Ok value)) := by
 cases reservation with
 | Err e => rfl
 | Ok unit =>
  have initialized:=complete (memoryNative native) cut.1 (rows value) before
  have same : (box owner (NKA_InitHistory.completed (run (memoryNative native) (rows value) before))).value=value :=
   NJT_ClaimsWindows.claims_ext _ _ (boxCut owner value _ (NKA_InitHistory.ready _) initialized).2.2
  simp only [result,runRows_source native cut,bind_tc_ok,same]

/-- Owned-carrier metadata is retained separately from the data windows.
No pointee value is inferred from the numeric ownership token. -/
theorem ownership (native : RowNative) (cut : RowCut native) (box : BoxNative)
 (boxCut : BoxCut box) (owner : Nat) (before : Memory) (value : Claims) :
 let post:=box owner (NKA_InitHistory.completed (run (memoryNative native) (rows value) before))
 post.owner=owner ∧ post.length=1 := by
 have packet:=boxCut owner value _ (NKA_InitHistory.ready _) (complete (memoryNative native) cut.1 (rows value) before)
 exact ⟨packet.1,packet.2.1⟩

#print axioms row_returned
#print axioms typed_write
#print axioms ownership
#print axioms runRows_source
#print axioms source
end AspisR1.NKA_HeapCarrier
end
