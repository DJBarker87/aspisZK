import PV_FN_THREAD_f6LoadCounter
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6CounterTest
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Named operator interpretation for source2200's usize Ne zero. Rust scalar
inequality compares values, with no world effect. This installs that emitted
instance, retaining the base interpretation on every other operand shape.
The domain's usize typing is supplied by127's named return type, not a value
or future-success restriction. No control.binary interpretation is involved:
source2200 is a leaf bind of an Expression.binary. -/
def carrier {W : Type} (base : Carrier W Data) (b : Bool) : Carrier W Data :=
  let c := PV_THR2_EntryDynamic.carrier (PV_THR2_ScopeLiterals.carrier base) b
  {c with binary := fun op x y => match op,x,y with
    | "Ne",.number n,.number 0 => some (.boolean (decide (n ≠ 0)))
    | _,_,_ => c.binary op x y}

theorem PV_THR2_OperatorSemantics_2200 {W : Type} (base : Carrier W Data)
    (b : Bool) (n : Nat) :
    (carrier base b).binary "Ne" (.number n) (.number 0) =
      some (.boolean (decide (n ≠ 0))) := rfl

def prepared (t : Store Data) (a n : Nat) :=
  write (write (write (write t ⟨a,19,[]⟩ none) ⟨a,16,[]⟩ none)
    ⟨a,15,[]⟩ none) ⟨a,14,[]⟩ (some (.boolean (decide (n ≠ 0))))

def afterBranch (t : Store Data) (a n : Nat) (parents : List Frame)
    (loops : List LoopFrame) : Config :=
  ⟨{activation := a,remaining :=
      (if n = 0 then [PV_THR2_F6.node67] else []) ++ PV_THR2_F6.block86.drop 16,
      loops := loops},parents,write (prepared t a n) ⟨a,14,[]⟩ none⟩

/-- Four OWN instructions after127 Post, including the actual zero/nonzero
branch. The127 result is only an internal Post projection. Both paths remain;
there is no termination or zero-counter assumption. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a n : Nat) (parents : List Frame) (loops : List LoopFrame)
    (b : Bool) (w : W) (es : List E) (stack : List Config)
    (counter_cell : t.cells ⟨a,15,[]⟩ = some (.number n)) :
    PV_THR2_IntrinsicState.advance (carrier base b) ctl P H 4
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 12,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (afterBranch t a n parents loops),w,es⟩,stack⟩ := by
  have shape : PV_THR2_F6.block86.drop 12 =
    [PV_THR2_F6.node63,PV_THR2_F6.node64,PV_THR2_F6.node65,PV_THR2_F6.node69] ++
      PV_THR2_F6.block86.drop 16 := rfl
  rw [shape]
  generalize tail : PV_THR2_F6.block86.drop 16 = remaining
  have zero : (carrier base b).constant
      (.object [("kind",.object [("Literal",.object [("Scalar",.object
        [("Unsigned",.array [.atom "Usize",.atom "0"])])])]),("ty",.object [("Deduplicated",.number 435)])]) = some (.number 0) := rfl
  have truth (v : Bool) : (carrier base b).truth (.boolean v) = some v := rfl
  have ne (v : Nat) : (carrier base b).binary "Ne" (.number v) (.number 0) =
      some (.boolean (decide (v ≠ 0))) := PV_THR2_OperatorSemantics_2200 base b v
  by_cases hn : n = 0 <;>
    simp [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
      PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
      PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
      PV_THR2_AggregateCompletion.carrier,
      PV_STX2_SliceMachine.step,PV_THR2_F6.node63,PV_THR2_F6.node64,
      PV_THR2_F6.node65,PV_THR2_F6.node69,PV_THR2_F6.block66,PV_THR2_F6.block68,
      native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operands,operand,
      PV_STX2_Store.read,locate,writeAddress,write,counter_cell,zero,truth,ne,
      prepared,afterBranch,tail,hn]

/-- Actual source2202 exits only the innermost completion loop. Its saved
continuation and all lower loop/caller frames are retained exactly. -/
theorem exit {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (t : Store Data) (a : Nat) (parents : List Frame)
    (loop : LoopFrame) (lower : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.step B ctl P H
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.node67 :: rest,loops := loop :: lower},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := loop.afterLoop,loops := lower},parents,t⟩,w,es⟩,stack⟩ := by
  simp [PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_STX2_SliceMachine.step,PV_THR2_F6.node67]

theorem frame (t : Store Data) (a n : Nat) (p : Address) (outside : p.activation ≠ a) :
    (write (prepared t a n) ⟨a,14,[]⟩ none).cells p = t.cells p := by
  have neq (i : Nat) : p ≠ (⟨a,i,[]⟩ : Address) := by
    intro eq
    exact outside (congrArg Address.activation eq)
  simp [prepared,write,neq]

#print axioms PV_THR2_OperatorSemantics_2200
#print axioms run
#print axioms exit
#print axioms frame
end PV_FN_THREAD_f6CounterTest
