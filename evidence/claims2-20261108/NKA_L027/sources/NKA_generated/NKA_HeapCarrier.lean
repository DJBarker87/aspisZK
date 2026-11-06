import NKA_InitializedPrefix
import NKA_ClaimsReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_HeapCarrier
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames
open NKA_InitializedPrefix
abbrev Claims := NJT_ClaimsWindows.Claims
abbrev Status := core.result.Result Claims r1_wire.Error

def rows (value : Claims) : Rows := fun p i=>
 NJG_NativeCuts.word (cell (cell value p) ⟨i.val/4,by omega⟩) ⟨i.val%4,by omega⟩

structure RowPost where
 outcome : Result (core.result.Result Unit r1_wire.Error)
 memory : Memory
abbrev RowNative := Fin 3 → (Fin 116 → U32) → Memory → RowPost
abbrev memoryNative (native : RowNative) : Native := fun p row before=>(native p row before).memory

/-- Successful SAME-row projection of the complete NJM_K011/K012 Result and
initialized-prefix frame assertion. Decoder success is established by the
SAME parsed caller in the root; it is not a root hypothesis. -/
def RowCut (native : RowNative) : Prop :=
 Cut (memoryNative native) ∧
 ∀ p row before,(native p row before).outcome=ok (.Ok ())

abbrev BoxNative := Memory → Claims
/-- NJM_K006/K007/K008: assume_init returns the original owned allocation,
with every observed u32 unchanged. The initializer premise is supplied by
complete, not by caller success or numeric pointer equality. The safe
singleton carrier is NJT_K003/K004/K005 and the pinned Aeneas Slice model. -/
def BoxCut (native : BoxNative) : Prop :=
 ∀ (value : Claims) (memory : Memory),Prefix (rows value) 3 memory →
 ∀ (p : Fin 3) (k : Fin 29) (limb : Fin 4),
 NJG_NativeCuts.word (cell (cell (native memory) p) k) limb=
 NJG_NativeCuts.word (cell (cell value p) k) limb

def runRows (native : RowNative) (value : Claims) : List (Fin 3) → Memory →
 Result (core.result.Result Memory r1_wire.Error)
 | [],before => ok (.Ok before)
 | p::ps,before => do
  let post:=native p (rows value p) before
  let result ← post.outcome
  match result with
  | .Err e => ok (.Err e)
  | .Ok _ => runRows native value ps post.memory

theorem runRows_source (native : RowNative) (cut : RowCut native) (value : Claims) (before : Memory) :
 runRows native value [0,1,2] before=ok (.Ok (run (memoryNative native) (rows value) before)) := by
 simp only [runRows,cut.2,bind_tc_ok]
 rfl

def result (reservation : NP6_StdModel.Reservation) (native : RowNative)
 (box : BoxNative) (before : Memory) (value : Claims) : Result Status :=
 match reservation with
 | .Err _ => ok (.Err .Allocation)
 | .Ok _ => do
  let status ← runRows native value [0,1,2] before
  match status with
  | .Err e => ok (.Err e)
  | .Ok memory => ok (.Ok (box memory))

/-- Full returning Result of forward-instantiated native windows. Prefix
initializedness is derived before the owned-carrier cast; every successful
row outcome is discharged by the exact native stage assertion. -/
theorem source (reservation : NP6_StdModel.Reservation) (native : RowNative)
 (cut : RowCut native) (box : BoxNative) (boxCut : BoxCut box)
 (before : Memory) (value : Claims) :
 result reservation native box before value=
 (match reservation with | .Err _=>ok (.Err .Allocation) | .Ok _=>ok (.Ok value)) := by
 cases reservation with
 | Err e => rfl
 | Ok unit =>
  have initialized:=complete (memoryNative native) cut.1 (rows value) before
  have same : box (run (memoryNative native) (rows value) before)=value :=
   NJT_ClaimsWindows.claims_ext _ _ (boxCut value _ initialized)
  simp only [result,runRows_source native cut,bind_tc_ok,same]

#print axioms runRows_source
#print axioms source
end AspisR1.NKA_HeapCarrier
end
