import LIB_VTerminalCarriers
import LIB_VResult
set_option autoImplicit false
noncomputable section
namespace LIB_VTerminal
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1 LIB_VTerminalCarriers
abbrev Args := Public × Claims × Alpha × OrigChallenges
abbrev NativeError := NLH_WrapperState.Error
def native (a : Args) : Result (core.result.Result NQ NativeError) :=
 FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
  (FIq_Carriers.toPublic a.1) (nativeClaims a.2.1) (nativeArray a.2.2.1) (nativeChallenges a.2.2.2)
def Domain (a : Args) : Prop := LIB_VPublicDomain.publicDom a.1
def Good : Result (core.result.Result NQ NativeError) → Prop
 | .ok (.Ok q) => FIv_NativeValue.Canon q
 | _ => True
theorem projected_good (out : NLH_WrapperRoot.Outcome) (h : NLH_WrapperRoot.Canonical out) :
 Good (NLH_WrapperRoot.projected out) := by
 cases out with
 | fail e => trivial
 | div => trivial
 | ok reply => cases reply with
  | Err e => trivial
  | Ok st => exact h
theorem native_good (a : Args) (h : Domain a) : Good (native a) := by
 obtain ⟨out,events,_,_,canonical,same,_⟩ := NLH_WrapperRoot.source
  (FIq_Carriers.toPublic a.1) (nativeClaims a.2.1) (nativeArray a.2.2.1) (nativeChallenges a.2.2.2)
  h.1 (claims_canonical a.2.1) (array_canonical a.2.2.1) (array_canonical a.2.2.2.zc)
  (scalar_canonical a.2.2.2.lambda) (scalar_canonical a.2.2.2.chi)
  (scalar_canonical a.2.2.2.theta) (scalar_canonical a.2.2.2.mu) h.2
 unfold native
 rw [←same]
 exact projected_good out canonical
def liftRaw : (r : Result (core.result.Result NQ NativeError)) → Good r → Result (Except Unit QM31)
 | .ok (.Ok q),h => .ok (.ok (ofNative q h))
 | .ok (.Err _),_ => .ok (.error ())
 | .fail e,_ => .fail e
 | .div,_ => .div
def model (a : Args) : Result (Except Unit QM31) := by
 classical
 exact if h : Domain a then liftRaw (native a) (native_good a h)
 else .fail .arrayOutOfBounds
def terminalQm31 : RSL.Child Args (Except Unit QM31) :=
 ⟨Domain,fun a=>LIB_Carriers.resultGraph id (fun _=>model a) (fun _=>[])⟩
def forget : Except Unit QM31 → Except Unit NQ
 | .ok q=>.ok (scalar q) | .error e=>.error e
def project : core.result.Result NQ NativeError → Except Unit NQ
 | .Ok q=>.ok q | .Err _=>.error ()
theorem lift_exact (r : Result (core.result.Result NQ NativeError)) (h : Good r) :
 (do let out←liftRaw r h;Result.ok (forget out)) =
 (do let out←r;Result.ok (project out)) := by
 cases r with
 | fail e=>rfl | div=>rfl | ok reply=>cases reply with
  | Err e=>rfl
  | Ok q=>simp only [liftRaw,forget,project,scalar_ofNative,bind_tc_ok]
theorem model_exact (a : Args) (h : Domain a) :
 (do let out←model a;Result.ok (forget out)) =
 (do let out←native a;Result.ok (project out)) := by
 classical
 simp only [model,dif_pos h]
 exact lift_exact _ _
def eval (a : Args) : Except Unit QM31 := LIB_VResult.value id (.error ()) (model a)
theorem returns (a : Args) (env : RSL.Env) :
 NND_Returned.Returns (terminalQm31.law a) env (eval a) :=
 LIB_VResult.returns id (Except.error () : Except Unit QM31) (fun _=>model a) (fun _=>[]) env
theorem functional : RSL.Child.Functional terminalQm31 := fun _ _=>LIB_VResult.functional id _ _
theorem law_exact (a : Args) (env : RSL.Env) (o : RSL.Obs (Except Unit QM31)) :
 terminalQm31.law a env o ↔ o=LIB_Carriers.resultObs id [] (model a) := Iff.rfl
#print axioms projected_good
#print axioms native_good
#print axioms lift_exact
#print axioms model_exact
#print axioms returns
#print axioms functional
#print axioms law_exact
end LIB_VTerminal
