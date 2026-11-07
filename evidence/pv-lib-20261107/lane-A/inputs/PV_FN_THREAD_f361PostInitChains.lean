import PV_THR2_Source15CaptureChain
import PV_THR2_IntrinsicAtContinuation
import PV_FN_THREAD_f361SuffixLists
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Chain130To139
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node163 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node164 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node165 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node166 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node167 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node168 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node169 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node170 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node171 .done)))))))))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ PV_THR2_F361.live.body.drop 139 = PV_THR2_F361.live.body.drop 130 := by
  rw [show (139: Nat) = 128+11 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128,
    show (130: Nat) = 128+2 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128]
  rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 139) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 130) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 130) (finish base) q
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
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 130,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361Chain130To139
namespace PV_FN_THREAD_f361Chain140To142
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node173 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node174 .done))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ PV_THR2_F361.live.body.drop 142 = PV_THR2_F361.live.body.drop 140 := by
  rw [show (142: Nat) = 128+14 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128,
    show (140: Nat) = 128+12 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128]
  rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 142) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 140) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 140) (finish base) q
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
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 140,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361Chain140To142
namespace PV_FN_THREAD_f361Chain143To144
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node176 .done)
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ PV_THR2_F361.live.body.drop 144 = PV_THR2_F361.live.body.drop 143 := by
  rw [show (144: Nat) = 128+16 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128,
    show (143: Nat) = 128+15 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128]
  rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 144) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 143) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 143) (finish base) q
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
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 143,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361Chain143To144
namespace PV_FN_THREAD_f361Chain145To149
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node222 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node223 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node224 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node225 .done))))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ PV_THR2_F361.live.body.drop 149 = PV_THR2_F361.live.body.drop 145 := by
  rw [show (149: Nat) = 128+21 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128,
    show (145: Nat) = 128+17 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128]
  rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 149) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 145) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 145) (finish base) q
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
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 145,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361Chain145To149
namespace PV_FN_THREAD_f361Chain150To155
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node229 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node230 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node231 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node232 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node233 .done)))))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ PV_THR2_F361.live.body.drop 155 = PV_THR2_F361.live.body.drop 150 := by
  rw [show (155: Nat) = 128+27 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128,
    show (150: Nat) = 128+22 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128]
  rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 155) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 150) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 150) (finish base) q
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
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 150,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361Chain150To155
namespace PV_FN_THREAD_f361Chain156To159
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node235 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node236 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node237 .done)))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ PV_THR2_F361.live.body.drop 159 = PV_THR2_F361.live.body.drop 156 := by
  rw [show (159: Nat) = 128+31 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128,
    show (156: Nat) = 128+28 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128]
  rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 159) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 156) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 156) (finish base) q
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
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 156,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361Chain156To159
namespace PV_FN_THREAD_f361Chain160To187
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node239 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node240 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node241 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node242 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node243 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node244 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node245 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node246 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node247 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node248 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node249 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node250 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node251 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node252 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node253 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node254 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node255 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node256 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node257 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node258 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node259 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node260 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node261 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node262 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node263 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node264 (PV_THR2_Source15CaptureChain.prepend PV_THR2_F361.node265 .done)))))))))))))))))))))))))))
theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ PV_THR2_F361.live.body.drop 187 = PV_THR2_F361.live.body.drop 160 := by
  rw [show (187: Nat) = 128+59 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128,
    show (160: Nat) = 128+32 from rfl,
    PV_FN_THREAD_f361SuffixLists.drop_after128]
  rfl
def cost {W : Type} (base : Carrier W Data) (c : Config) (w : W) :=
  PV_THR2_IntrinsicFrameChain.steps base c.frame.activation w chain c.store
def finish {W E : Type} (base : Carrier W Data) (c : Config) (w : W) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State W E :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result base c.frame.activation c.callers c.frame.loops
    (PV_THR2_F361.live.body.drop 187) w chain c.store,w,es⟩,stack⟩
noncomputable def steps {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F361.live.body.drop 160) (cost base) q
noncomputable def after {W E : Type} (base : Carrier W Data) (q : PV_THR2_IntrinsicState.State W E) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F361.live.body.drop 160) (finish base) q
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
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 160,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  rw [← shape]
  exact PV_THR2_IntrinsicFrameChain.run base ctl programs handler chain s a parents loops _ w es stack
#print axioms shape
#print axioms run
end PV_FN_THREAD_f361Chain160To187
