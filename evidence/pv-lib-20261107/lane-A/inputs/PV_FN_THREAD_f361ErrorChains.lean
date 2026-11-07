import PV_THR2_Source15CaptureChain
import PV_THR2_IntrinsicAtContinuation
import PV_THR2_F361
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361ErrorChain0To4
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node178 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node179 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node180 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node181 .done))))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ (PV_THR2_F361.block220.drop 4 ++ PV_THR2_F361.live.body.drop 145) = (PV_THR2_F361.block220.drop 0 ++ PV_THR2_F361.live.body.drop 145) := rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    ((PV_THR2_F361.block220.drop 4 ++ PV_THR2_F361.live.body.drop 145)) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps ((PV_THR2_F361.block220.drop 0 ++ PV_THR2_F361.live.body.drop 145)) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after ((PV_THR2_F361.block220.drop 0 ++ PV_THR2_F361.live.body.drop 145)) (finish base) q
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base q) q = after base q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl programs handler
    (PV_THR2_IntrinsicFrameChain.steps base a w chain s)
    ⟨⟨.running ⟨{activation := a,remaining := (PV_THR2_F361.block220.drop 0 ++ PV_THR2_F361.live.body.drop 145),loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361ErrorChain0To4
namespace PV_FN_THREAD_f361ErrorChain5To7
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node183 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node184 .done))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ (PV_THR2_F361.block220.drop 7 ++ PV_THR2_F361.live.body.drop 145) = (PV_THR2_F361.block220.drop 5 ++ PV_THR2_F361.live.body.drop 145) := rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    ((PV_THR2_F361.block220.drop 7 ++ PV_THR2_F361.live.body.drop 145)) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps ((PV_THR2_F361.block220.drop 5 ++ PV_THR2_F361.live.body.drop 145)) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after ((PV_THR2_F361.block220.drop 5 ++ PV_THR2_F361.live.body.drop 145)) (finish base) q
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base q) q = after base q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl programs handler
    (PV_THR2_IntrinsicFrameChain.steps base a w chain s)
    ⟨⟨.running ⟨{activation := a,remaining := (PV_THR2_F361.block220.drop 5 ++ PV_THR2_F361.live.body.drop 145),loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361ErrorChain5To7
namespace PV_FN_THREAD_f361ErrorChain8To19
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node188 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node189 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node190 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node191 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node192 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node193 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node194 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node195 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node196 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node197 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node198 .done)))))))))))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ (PV_THR2_F361.block220.drop 19 ++ PV_THR2_F361.live.body.drop 145) = (PV_THR2_F361.block220.drop 8 ++ PV_THR2_F361.live.body.drop 145) := rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    ((PV_THR2_F361.block220.drop 19 ++ PV_THR2_F361.live.body.drop 145)) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps ((PV_THR2_F361.block220.drop 8 ++ PV_THR2_F361.live.body.drop 145)) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after ((PV_THR2_F361.block220.drop 8 ++ PV_THR2_F361.live.body.drop 145)) (finish base) q
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base q) q = after base q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl programs handler
    (PV_THR2_IntrinsicFrameChain.steps base a w chain s)
    ⟨⟨.running ⟨{activation := a,remaining := (PV_THR2_F361.block220.drop 8 ++ PV_THR2_F361.live.body.drop 145),loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361ErrorChain8To19
namespace PV_FN_THREAD_f361ErrorChain20To23
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node200 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node201 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node202 .done)))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ (PV_THR2_F361.block220.drop 23 ++ PV_THR2_F361.live.body.drop 145) = (PV_THR2_F361.block220.drop 20 ++ PV_THR2_F361.live.body.drop 145) := rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    ((PV_THR2_F361.block220.drop 23 ++ PV_THR2_F361.live.body.drop 145)) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps ((PV_THR2_F361.block220.drop 20 ++ PV_THR2_F361.live.body.drop 145)) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after ((PV_THR2_F361.block220.drop 20 ++ PV_THR2_F361.live.body.drop 145)) (finish base) q
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base q) q = after base q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl programs handler
    (PV_THR2_IntrinsicFrameChain.steps base a w chain s)
    ⟨⟨.running ⟨{activation := a,remaining := (PV_THR2_F361.block220.drop 20 ++ PV_THR2_F361.live.body.drop 145),loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361ErrorChain20To23
namespace PV_FN_THREAD_f361ErrorChain24To39
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node204 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node205 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node206 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node207 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node208 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node209 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node210 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node211 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node212 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node213 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node214 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node215 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node216 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node217 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node218 .done)))))))))))))))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ (PV_THR2_F361.block220.drop 39 ++ PV_THR2_F361.live.body.drop 145) = (PV_THR2_F361.block220.drop 24 ++ PV_THR2_F361.live.body.drop 145) := rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    ((PV_THR2_F361.block220.drop 39 ++ PV_THR2_F361.live.body.drop 145)) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps ((PV_THR2_F361.block220.drop 24 ++ PV_THR2_F361.live.body.drop 145)) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after ((PV_THR2_F361.block220.drop 24 ++ PV_THR2_F361.live.body.drop 145)) (finish base) q
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base q) q = after base q := by
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance base ctl programs handler
    (PV_THR2_IntrinsicFrameChain.steps base a w chain s)
    ⟨⟨.running ⟨{activation := a,remaining := (PV_THR2_F361.block220.drop 24 ++ PV_THR2_F361.live.body.drop 145),loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361ErrorChain24To39
