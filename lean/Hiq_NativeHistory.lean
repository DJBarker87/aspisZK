import Hiq_NativeClassify
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_NativeHistory
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry S2Trust S2W_D189Entry S2W_D189Wrappers
open Hiq_NativeAction
variable {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def run (store : Store) : List (Action A) → Store × List S2X.AccountEvent
  | [] => (store,[])
  | action :: rest =>
    let head := apply native copy allocator id store action
    let tail := run head.1 rest
    (tail.1,head.2 :: tail.2)

theorem classified (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = native id accounts data)
    (trustedCopy : S2W_TrustedStd.TrustedStd copy) (store : Store) (actions : List (Action A)) :
    Trace ops id store (run native copy allocator id store actions).2 (run native copy allocator id store actions).1 := by
  induction actions generalizing store with
  | nil => exact Trace.nil store
  | cons action rest ih =>
    exact Trace.cons (Hiq_NativeClassify.step ops law native source copy trustedCopy allocator id store action)
      (ih (apply native copy allocator id store action).1)

theorem protection (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = native id accounts data)
    (trustedCopy : S2W_TrustedStd.TrustedStd copy) (store : Store) (actions : List (Action A)) (key : Nat)
    (owner : (store key).owner = id) (marker : Initialized (store key).data) :
    (∀ event ∈ (run native copy allocator id store actions).2, S2X.Preserves key event) ∧
      (run native copy allocator id store actions).1 key = store key :=
  Hist_TraceProtection.trace_frame ops id store _ key _
    (classified native copy allocator id ops law source trustedCopy store actions) owner marker

#print axioms classified
#print axioms protection
end AspisR1.Hiq_NativeHistory
end
