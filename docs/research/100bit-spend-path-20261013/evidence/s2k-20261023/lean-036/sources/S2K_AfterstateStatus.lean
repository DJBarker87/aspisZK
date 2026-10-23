import S2K_AfterstatePrefix

/-! Exact status composition of the actual extracted encoder, retaining every
validator error. No successful encoder premise or external certificate axiom. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.AfterstateStatus
open AspisR1TerminalDecoder
open pool_v1.pair_terminal
abbrev Afterstate := PoolV1PairVerifiedAfterstateV1
abbrev Error := PoolV1PairVerifierTransportErrorV1

def finish (p : LoopStep.Iter × Array U8 688#usize) :
    Result (core.result.Result (Array U8 688#usize) Error) := do
  let out ← encode_pool_v1_pair_verified_afterstate_v1_loop p.1 p.2
  ok (.Ok out)

private theorem pair_assoc {A B C D : Type} (m : Result (A × B))
    (f : A → B → Result C) (g : C → Result D) :
    (do let x ← (do let (a,b) ← m; f a b); g x) =
      (do let (a,b) ← m; let x ← f a b; g x) := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok p => rcases p with ⟨a,b⟩; rfl

private theorem pair_let_bind {A B C D : Type} (p : A × B)
    (f : A → B → Result C) (g : C → Result D) :
    (do let x ← (let (a,b) := p; f a b); g x) =
      (let (a,b) := p; do let x ← f a b; g x) := by
  rcases p with ⟨a,b⟩
  rfl

theorem factor (a : Afterstate)
    (validated : validate_verified_afterstate a = ok (.Ok ())) :
    encode_pool_v1_pair_verified_afterstate_v1 a =
      (do let p ← AfterstatePrefix.fields a (Array.repeat 688#usize 0#u8); finish p) := by
  simp only [encode_pool_v1_pair_verified_afterstate_v1, validated,
    bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize Array.repeat 688#usize 0#u8 = initial
  unfold AfterstatePrefix.fields finish
  simp only [pair_let_bind, pair_assoc, bind_assoc_eq, bind_tc_ok]
  rfl

theorem success (a : Afterstate)
    (validated : validate_verified_afterstate a = ok (.Ok ())) :
    ∃ bytes, encode_pool_v1_pair_verified_afterstate_v1 a = ok (.Ok bytes) := by
  obtain ⟨out,fields⟩ := AfterstatePrefix.total a (Array.repeat 688#usize 0#u8)
  obtain ⟨bytes,rows⟩ := AfterstateLoop.total a.next_frontier out
  refine ⟨bytes,?_⟩
  rw [factor a validated, fields]
  simp only [bind_tc_ok,finish,rows]

theorem rejection (a : Afterstate) (e : Error)
    (validated : validate_verified_afterstate a = ok (.Err e)) :
    encode_pool_v1_pair_verified_afterstate_v1 a = ok (.Err e) := by
  simp only [encode_pool_v1_pair_verified_afterstate_v1, validated,
    bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rfl

#print axioms pair_assoc
#print axioms pair_let_bind
#print axioms factor
#print axioms success
#print axioms rejection
end AspisR1.S2K.AfterstateStatus
