import PV_STX_World
import PV_STX_Entropy
set_option autoImplicit false
noncomputable section
namespace PV_STX_EntropyWorld
open Aeneas Aeneas.Std ProverRwFull PV_STX_Machine PV_STX_World
open PV_RJ4IDB (NativeEvent)
variable [ExternalTypes]
abbrev Filled := (core.result.Result Unit getrandom.error.Error) × Slice U8
/-- The only external data is one reached OS reply. Partial error writes are
in the returned Slice, never reconstructed from the final source Result. -/
abbrev Provider := World → Slice U8 → Answer Filled

def draw (provider : Provider) (buffer : Slice U8) (w : World) : Reply World NativeEvent Filled :=
  let answer := provider w buffer
  let request := side "entropy-request" (ascii (toString w.base.entropyCursor))
  let delivery := side "entropy-delivery" (ascii (toString w.base.entropyCursor))
  match answer with
  | .pending => ⟨.pending,w,[]⟩
  | .returned .div =>
    ⟨answer,{w with base := {w.base with entropyCursor := w.base.entropyCursor+1}},[request]⟩
  | .fault _ =>
    ⟨answer,{w with base := {w.base with entropyCursor := w.base.entropyCursor+1}},[request]⟩
  | .returned _ =>
    ⟨answer,{w with base := {w.base with entropyCursor := w.base.entropyCursor+1}},[request,delivery]⟩

/-- Port of evh's transparent Zeroizing wrappers. Constructors and borrows do
not allocate; destruction is a separate reached operation, not a silent drop.
This interpreter does NOT select a new fixed ExternalFuns dictionary. -/
def handler (provider : Provider) : Handler PV_STX_Entropy.Request World NativeEvent :=
  fun op w => match op with
  | .fill buffer => draw provider buffer w
  | .restore _ back value => ⟨.returned (.ok (back value)),w,[]⟩
  | .new _ value => ⟨.returned (.ok value),w,[]⟩
  | .asMut inst _ value => ⟨.returned (inst.as_mut value),w,[]⟩
  | .derefMut _ value => ⟨.returned (.ok (value,id)),w,[]⟩
  | .deref _ value => ⟨.returned (.ok value),w,[]⟩

theorem draw_partial_error (provider : Provider) (buffer after : Slice U8)
    (error : getrandom.error.Error) (w : World)
    (h : provider w buffer = .returned (.ok (.Err error,after))) :
    draw provider buffer w =
      ⟨.returned (.ok (.Err error,after)),
       {w with base := {w.base with entropyCursor := w.base.entropyCursor+1}},
       [side "entropy-request" (ascii (toString w.base.entropyCursor)),
        side "entropy-delivery" (ascii (toString w.base.entropyCursor))]⟩ := by
  simp only [draw,h]

theorem draw_pending (provider : Provider) (buffer : Slice U8) (w : World)
    (h : provider w buffer = .pending) : draw provider buffer w = ⟨.pending,w,[]⟩ := by
  simp only [draw,h]

theorem draw_frame (provider : Provider) (buffer : Slice U8) (w : World) :
    (draw provider buffer w).world.heap = w.heap ∧
    (draw provider buffer w).world.allocator = w.allocator ∧
    (draw provider buffer w).world.base.files = w.base.files ∧
    (draw provider buffer w).world.handles = w.handles ∧
    (draw provider buffer w).world.stackCursor = w.stackCursor ∧
    (draw provider buffer w).world.threadCursor = w.threadCursor := by
  unfold draw
  cases provider w buffer with
  | pending => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | fault f => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | returned r => cases r <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Each returned mutable borrow has the actual backward continuation. -/
theorem restore_step {X Y A : Type} (provider : Provider) (site : Nat)
    (back : X → Y) (value : X) (k : PV_STX_Code.Kont PV_STX_Entropy.Request A Y) (w : World) :
    step (handler provider) ⟨Y,.call (.restore site back value),k⟩ w =
      ⟨resumed (@PV_STX_Code.continueWith _ A) k (back value),w,[]⟩ := rfl

#print axioms draw_partial_error
#print axioms draw_pending
#print axioms draw_frame
#print axioms restore_step
end PV_STX_EntropyWorld
