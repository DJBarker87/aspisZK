import PV_LIB_SLICE_BoundedRun
import PV_W5_F32Contract
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_F32
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER PV_STX2_SliceMachine

/-- Exact supplied-machine prefixes from the CLOSED provider's own entry. -/
def run (D : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W5_UbCheckPrimitives.Handler)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (n : Nat) :=
  advance D K P H n (PV_FN_SLICE_f32.start s parent parents a w prior)

/-- Fixed provider test, including its actual frame and event-prefix clauses.
This is a fuel test, not a child law. In particular it never quantifies over
alternative backend answers or independently selected output traces. -/
def eligible (D : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W5_UbCheckPrimitives.Handler)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (n : Nat) : Prop :=
  PV_FN_SLICE_f32.Boundary D K P H s parent parents a w prior n
      (run D K P H s parent parents a w prior n) ∧
  PV_W5_F59Frame.Post s a w (run D K P H s parent parents a w prior n) ∧
  ∃ suffix, (run D K P H s parent parents a w prior n).events = prior ++ suffix

def selectedFuel (D : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W5_UbCheckPrimitives.Handler)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) : Nat :=
  PV_LIB_SLICE_BoundedRun.fuel 128 (eligible D K P H s parent parents a w prior)

def output (D : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W5_UbCheckPrimitives.Handler)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) := run D K P H s parent parents a w prior (selectedFuel D K P H s parent parents a w prior)

def model (D : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W5_UbCheckPrimitives.Handler)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB.observe (⟨output D K P H s parent parents a w prior,stack⟩ :
    PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)

def law (D : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W5_UbCheckPrimitives.Handler)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model D K P H s parent parents a w prior stack

/-- Reify the CLOSED contract by a bounded search on its deterministic run.
There is no proof argument or selected native reply in the model's inputs.
The least eligible certified prefix need not be the first syntactic boundary;
no firstness strengthening of the provider is claimed. -/
theorem certified (D : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W5_UbCheckPrimitives.Handler)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent)
    (base : Carrier OWNER Data) (ctrl : Control) (word : Data → Nat)
    (addresses : Data → Address) (backend : PV_W5_NativeFrame.Backend)
    (source target : Data) (size alignment count : Nat) (pre : PV_FN_SLICE_f32.Pre s a source target size alignment count w)
    (spec : PV_FN_SLICE_f32.LiteralMachineSpec D K P H base ctrl word addresses backend)
    (stack : List Config) :
    law D K P H s parent parents a w prior stack (model D K P H s parent parents a w prior stack) ∧
    selectedFuel D K P H s parent parents a w prior ≤ 128 ∧
    eligible D K P H s parent parents a w prior (selectedFuel D K P H s parent parents a w prior) := by
  have provider := PV_FN_SLICE_f32.contract D K P H base ctrl word addresses backend s parent parents a
    source target size alignment count w prior pre spec
  rcases provider with ⟨n,out,limit,reached,boundary,frame,events⟩
  have existsFuel : ∃ n, n ≤ 128 ∧ eligible D K P H s parent parents a w prior n := by
    refine ⟨n,limit,?_,?_,?_⟩
    · simpa only [run,reached] using boundary
    · simpa only [run,reached] using frame
    · simpa only [run,reached] using events
  exact ⟨rfl,PV_LIB_SLICE_BoundedRun.selected 128 (eligible D K P H s parent parents a w prior) existsFuel⟩

theorem functional (D : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_W5_UbCheckPrimitives.Handler)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (left right : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent)
    (hl : law D K P H s parent parents a w prior stack left) (hr : law D K P H s parent parents a w prior stack right) : left = right :=
  hl.trans hr.symm

#print axioms certified
#print axioms functional
end PV_LIB_SLICE_F32
