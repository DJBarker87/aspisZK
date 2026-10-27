import XRx_TryDriver
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_RoundDriver
abbrev State (H : Type) := aspis_core.field.QM31 × Array aspis_core.field.QM31 10#usize × r1_wire.SemanticTranscript H
def index (n : Nat) : Usize := if h:n<10 then UScalar.ofNat n (by scalar_tac) else 0#usize

def step {H : Type} (D : aspis_core.digest.Digest32 H) (p : r1_wire.Prefix)
 (n : Nat) (s : State H) := r1_semantic.semantic_round D p s.2.2 s.2.1 s.1 (index n)

def initial {H : Type} (D : aspis_core.digest.Digest32 H) (p : r1_wire.Prefix)
 (tr : r1_wire.SemanticTranscript H) : Result (core.result.Result (State H) r1_wire.Error) := do
 let r ← r1_wire.Prefix.validated_record p 14#u8
 match r with
 | .Err e => ok (.Err e)
 | .Ok record =>
  let r ← r1_wire.ValidatedRecord.decode_k 1#usize record 0#usize
  match r with
  | .Err e => ok (.Err e)
  | .Ok values =>
   let running ← Array.index_usize values 0#usize
   let q ← aspis_core.field.QM31.ZERO
   ok (.Ok (running,Array.repeat 10#usize q,tr))

theorem tuple {A B C R : Type} (s : A × B × C) (k : A → B → C → R) :
 (let (a,b,c) := s; k a b c)=k s.1 s.2.1 s.2.2 := by
 rcases s with ⟨a,b,c⟩
 rfl

/-- Associate the emitted literal driver to one generic n-stage first-stop
fold. This theorem has no per-round semantic or native-P6 assumption. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H) (p : r1_wire.Prefix)
 (tr : r1_wire.SemanticTranscript H) :
 r1_semantic.semantic_rounds D p tr = (do
  let s ← initial D p tr
  XRx_StageFold.fold (step D p) (List.range' 0 10) s) := by
 simp only [←XRx_StageFold.source]
 unfold r1_semantic.semantic_rounds initial
 simp only [bind_assoc_eq]
 congr 1
 funext record
 cases record with
 | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from,XRx_StageRules.stopped]
 | Ok vr =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,bind_assoc_eq]
  congr 1
  funext decoded
  cases decoded with
  | Err e => simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
     core.convert.FromSame.from,XRx_StageRules.stopped]
  | Ok values =>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,bind_assoc_eq]
   congr 1
   funext running
   congr 1
   funext zero
   rw [XRx_StageFold.source,←XRx_TryDriver.source]
   simp only [XRx_TryDriver.run,step,index,Nat.reduceAdd,Nat.reduceLT,
    _root_.dite_true,Usize.ofNat,core.result.Result.Insts.CoreOpsTry.branch]
   repeat' (first
    | rfl
    | (congr 1
       funext out
       cases out with
       | Err e => rfl
       | Ok s =>
        rcases s with ⟨a,b,c⟩
        simp only [bind_tc_ok]
        dsimp! only))

   all_goals congr 1
#print axioms tuple
#print axioms source
end XRz_RoundDriver
