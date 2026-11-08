import PV_THR2_Source15LoopMatch
import PV_THR2_IntrinsicFrameBreak
import PV_THR2_Source15CaptureChain
set_option autoImplicit false
namespace PV_THR2_Source15LiveCaptures
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Actual3461-3471 chain, including payload read and all three capture references. -/
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  PV_THR2_Source15CaptureChain.prepend PV_THR2_F15.node23
    (PV_THR2_Source15CaptureChain.prepend PV_THR2_F15.node24 PV_THR2_Source15CaptureChain.chain)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
The complete live capture prefix is exactly the actual source syntax. -/
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ PV_THR2_F15.block47.drop 19 = PV_THR2_F15.block47.drop 8 := rfl
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Source match discriminant, read from the actual local8. -/
def tag (ctl : Control) (s : Store Data) (a : Nat) := (s.cells ⟨a,8,[]⟩).bind ctl.variant
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Variant0 executes break; variant1 executes storage and actual payload read. -/
def steps {W : Type} (base : Carrier W Data) (ctl : Control) (s : Store Data) (a : Nat) (w : W) : Nat := match tag ctl s a with
  | some 0 => 1
  | some 1 => PV_THR2_IntrinsicFrameChain.steps base a w chain (write s ⟨a,9,[]⟩ none)
  | _ => 0
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Missing tags stay gaps. No tag-to-field law or payload value identity is assumed. -/
def after {W E : Type} (base : Carrier W Data) (ctl : Control)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  let t := write s ⟨a,9,[]⟩ none
  match tag ctl s a with
  | some 0 => ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 13},parents,t⟩,w,es⟩,stack⟩
  | some 1 => ⟨⟨PV_THR2_IntrinsicFrameChain.result base a parents
        [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩] (PV_THR2_F15.block47.drop 19) w chain t,w,es⟩,stack⟩
  | _ => PV_THR2_Source15LoopMatch.after base ctl s a parents w es stack
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Follow every3460 case; execute real break3450 or storage3461/copy3462. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base ctl s a w)
      (PV_THR2_Source15LoopMatch.after base ctl s a parents w es stack) =
      after base ctl s a parents w es stack := by
  unfold steps after tag
  cases hr : s.cells ⟨a,8,[]⟩ with
  | none => simp only [Option.bind_none]; rfl
  | some v =>
    simp only [Option.bind_some]
    cases hv : ctl.variant v with
    | none => rfl
    | some n =>
      cases n with
      | zero =>
        simp only
        have shape : PV_THR2_Source15LoopMatch.after base ctl s a parents w es stack =
          ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.node19 :: PV_THR2_F15.block47.drop 8,loops := [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]},parents,write s ⟨a,9,[]⟩ none⟩,w,es⟩,stack⟩ := by
          simp [PV_THR2_Source15LoopMatch.after,PV_THR2_IntrinsicFrameMatch.result,PV_STX2_Store.read,write,hr,hv,selectVariant,PV_THR2_F15.block20]
        rw [shape]
        exact PV_THR2_IntrinsicFrameBreak.run base ctl programs handler _ a parents _ [] _ _ w es stack
      | succ n =>
        cases n with
        | zero =>
          simp only
          have shape : PV_THR2_Source15LoopMatch.after base ctl s a parents w es stack =
            ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.node23 :: PV_THR2_F15.node24 :: PV_THR2_F15.block47.drop 10,loops := [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]},parents,write s ⟨a,9,[]⟩ none⟩,w,es⟩,stack⟩ := by
            simp [PV_THR2_Source15LoopMatch.after,PV_THR2_IntrinsicFrameMatch.result,PV_STX2_Store.read,write,hr,hv,selectVariant]
            rfl
          rw [shape]
          change PV_THR2_IntrinsicState.advance base ctl programs handler
            (PV_THR2_IntrinsicFrameChain.steps base a w chain (write s ⟨a,9,[]⟩ none))
            ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 8,loops := [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]},parents,write s ⟨a,9,[]⟩ none⟩,w,es⟩,stack⟩ = _
          rw [← PV_THR2_Source15LiveCaptures.shape]
          exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain _ a parents _ _ w es stack
        | succ n => rfl
#print axioms shape
#print axioms run
end PV_THR2_Source15LiveCaptures
