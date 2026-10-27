import XRx_TryChain
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRx_RoundDriver
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

/-- Associate the emitted literal driver to one generic n-stage first-stop
fold. This theorem has no per-round semantic or native-P6 assumption. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H) (p : r1_wire.Prefix)
 (tr : r1_wire.SemanticTranscript H) :
 r1_semantic.semantic_rounds D p tr = (do
  let s ← initial D p tr
  XRx_StageFold.fold (step D p) (List.range' 0 10) s) := by
 simp only [←XRx_StageFold.source]
 unfold r1_semantic.semantic_rounds initial
 simp only [XRx_TryChain.source,bind_assoc_eq]
 congr 1
 funext record
 rw [XRx_TryChain.source]
 cases record with
 | Err e => simp only [bind_tc_ok,XRx_StageRules.stopped]
 | Ok vr =>
  simp only [bind_tc_ok,bind_assoc_eq]
  congr 1
  funext decoded
  rw [XRx_TryChain.source]
  cases decoded with
  | Err e => simp only [bind_tc_ok,XRx_StageRules.stopped]
  | Ok values =>
   simp only [bind_tc_ok,bind_assoc_eq]
   congr 1
   funext running
   congr 1
   funext zero
   simp only [XRx_StageRules.next,XRx_StageRules.chain,step,index,
    XRx_TryChain.pair]
   simp only [XRx_StageFold.unrolled]
   rfl

#print axioms source
end XRx_RoundDriver
