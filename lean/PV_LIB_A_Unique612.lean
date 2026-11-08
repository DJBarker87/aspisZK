import PV_LIB_A_NativeLeaves
import PV_THR2_IntrinsicSemantics_UniqueNewUnchecked612
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_Unique612
open PV_STX_Machine PV_STX2_Syntax PV_STX_World
open PV_THR2_IntrinsicSemantics_UniqueNewUnchecked612
/-- Exact provider function, including all nonsuccess replies and malformed
request shapes. The existing named Fact is the sole semantics obligation. -/
def model {E : Type}
    (H : PV_STX2_Native.Request Data → World → Reply World E Data)
    (request : PV_STX2_Native.Request Data) (w : World) := handler H request w

def law {E : Type}
    (H : PV_STX2_Native.Request Data → World → Reply World E Data)
    (request : PV_STX2_Native.Request Data) (w : World) (out : Reply World E Data) : Prop :=
  out = model H request w

theorem installed {E : Type}
    (H : PV_STX2_Native.Request Data → World → Reply World E Data)
    (fact : Fact H) (w : World) (a : Nat) (raw : Data) :
    law H (.child PV_THR2_BoxFromTable.fnUniqueFull a [raw]) w
      (H (.child PV_THR2_BoxFromTable.fnUniqueFull a [raw]) w) := by
  unfold law model handler
  simp only [ite_true]
  generalize eq : H (.child PV_THR2_BoxFromTable.fnUniqueFull a [raw]) w = r
  cases ans : r.answer with
  | returned result =>
    cases result with
    | ok v =>
      have h := fact w a raw v ((congrArg Reply.answer eq).trans ans)
      rw [eq] at h
      rcases r with ⟨answer,world,events⟩
      simp only at ans h
      subst answer
      rcases h with ⟨rfl,rfl,rfl⟩
      rfl
    | fail err => simp [PV_THR2_PointerIdentityReply.finish,ans]
    | div => simp [PV_THR2_PointerIdentityReply.finish,ans]
  | fault f => simp [PV_THR2_PointerIdentityReply.finish,ans]
  | pending => simp [PV_THR2_PointerIdentityReply.finish,ans]
#print axioms installed
end PV_LIB_A_Unique612
