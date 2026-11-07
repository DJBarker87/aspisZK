import NMC_LocalWindows
import NLU_TerminalTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Models
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NMC_Window
abbrev Q := NLC_Finish.Q
abbrev Reply := core.result.Result (Option Q) r1_wire.Error
abbrev PublicReply := core.result.Result Q FIq_Terminal.Error
abbrev DecodeReply := core.result.Result NLC_Finish.Words r1_wire.Error
noncomputable def qeq (a b : Q) : Bool := by classical exact decide (a=b)
noncomputable def peq (a b : NLC_Finish.Point) : Bool := by classical exact decide (a=b)
def mapPublic {A : Type} (s : Context A) (reply : PublicReply) : Observation A Reply :=
 match reply with
 | .Err _=>⟨.Err .Public,s⟩
 | .Ok terminal=>⟨.Ok none,{s with frame:={s.frame with terminal:=terminal}}⟩
def terminalGuard {A : Type} (s : Context A) (masked : Q) : Observation A Reply :=
 if qeq s.frame.running masked then ⟨.Ok none,s⟩ else ⟨.Err .Terminal,s⟩
def circleGuard {A : Type} (s : Context A) (_ : Unit) : Observation A Reply :=
 if peq s.frame.z0 s.frame.z1 then ⟨.Err .EqualCirclePoints,s⟩ else ⟨.Ok none,s⟩
def low {A : Type} (s : Context A) (i : Fin 16) : Observation A Reply :=
 ⟨.Ok (some (NLU.cell (NLU.cell s.frame.claims.value 0 (by decide)) i.val (by change i.val<29;omega))),s⟩
def high {A : Type} (s : Context A) (i : Fin 10) : Observation A Reply :=
 ⟨.Ok (some (NLU.cell (NLU.cell s.frame.claims.value 0 (by decide)) (16+i.val) (by change 16+i.val<29;omega))),s⟩
def blind {A : Type} (s : Context A) (_ : Unit) : Observation A Reply :=
 ⟨.Ok (some (NLU.cell (NLU.cell s.frame.claims.value 0 (by decide)) 27 (by decide))),s⟩
def extra28 {A : Type} (s : Context A) (_ : Unit) : Observation A Reply :=
 ⟨.Ok (some (NLU.cell s.frame.extra 28 (by decide))),s⟩
def stateBefore {A : Type} (s : Context A) (_ : Unit) : Observation A Reply :=
 ⟨.Ok none,{s with frame:={s.frame with state:=s.frame.transcript.state}}⟩
def decode25 {A : Type} (s : Context A) (reply : DecodeReply) : Observation A Reply :=
 match reply with
 | .Err error=>⟨.Err error,s⟩
 | .Ok extra=>⟨.Ok none,{s with frame:={s.frame with extra:=extra}}⟩
def decode26 {A : Type} (s : Context A) (reply : DecodeReply) : Observation A Reply :=
 match reply with
 | .Err error=>⟨.Err error,s⟩
 | .Ok before=>⟨.Ok none,{s with frame:={s.frame with before:=before}}⟩
end AspisR1.NMC_Models
end
