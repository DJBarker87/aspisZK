from pathlib import Path
import re
B=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
s=(B/'CurrentCompactCallerModelV1.lean').read_text()
a=s.index('          let r3 ← ops.op20 transport.Variant.S2',s.index('def verifier.candidate.tx1'))
b=a+re.search(r'(?m)^ {8}\| core.ops.control_flow.ControlFlow.Break residual =>',s[a:]).start()
body='\n'.join(line[8:] for line in s[a:b].rstrip().splitlines())
header='''import CurrentCompactPrepareReachabilityV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentCaller.Tx1Reachability
open AspisR1CurrentCaller

/-- Verbatim successful-preparation suffix of the emitted compact tx1 body.
The source adapter checks this complete suffix, including errors and writes. -/
def afterPrepare (ops : Ops) {H : Type}
    (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (val : verifier.Prepared)
    (g1 : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) := do
'''
proof='''
private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m;f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h

/-- The actual current compact tx1 supplies exactly the scratch returned by
its own preparation call to the unchanged remainder. No independent powers
array or successful preparation is a premise. Release observer is None. -/
theorem tx1_success (ops : Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H)
    (out : alloc.vec.Vec U8)
    (h : verifier.candidate.tx1 ops D pub publicBytes proof k hash none=ok (.Ok out)) :
    k=compact.SPLIT ∧ ∃ (parsed : transport.Variant)
      (zero : aspis_core.field.wide_exact.WideExact) (prepared : verifier.Prepared)
      (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize),
      ops.op3 proof=ok (.Ok parsed) ∧ ops.op4 proof=ok (.Ok ()) ∧
      aspis_core.field.wide_exact.WideExact.ZERO ops=ok zero ∧
      verifier.candidate.prepare ops D pub proof hash none (Array.repeat 29#usize zero)
        =ok (.Ok prepared,scratch) ∧
      afterPrepare ops D publicBytes proof k hash none prepared scratch=ok (.Ok out) := by
  unfold verifier.candidate.tx1 at h
  split at h
  · cases h
  · rename_i hk
    have hsplit : k=compact.SPLIT := by simpa only [bne_iff_ne,not_not] using hk
    obtain ⟨r,hr,h⟩ := bind_success (ops.op3 proof) _ _ h
    cases r with
    | Err e =>
      change ok (core.result.Result.Err e)=ok (.Ok out) at h
      cases h
    | Ok parsed =>
      obtain ⟨r,hr1,h⟩ := bind_success (ops.op4 proof) _ _ h
      cases r with
      | Err e =>
        change ok (core.result.Result.Err e)=ok (.Ok out) at h
        cases h
      | Ok u =>
        cases u
        obtain ⟨zero,hzero,h⟩ := bind_success
          (aspis_core.field.wide_exact.WideExact.ZERO ops) _ _ h
        obtain ⟨r,hprepare,h⟩ := bind_success
          (verifier.candidate.prepare ops D pub proof hash none (Array.repeat 29#usize zero)) _ _ h
        rcases r with ⟨r,scratch⟩
        cases r with
        | Err e =>
          change ok (core.result.Result.Err e)=ok (.Ok out) at h
          cases h
        | Ok prepared =>
          change afterPrepare ops D publicBytes proof k hash none prepared scratch=ok (.Ok out) at h
          exact ⟨hsplit,parsed,zero,prepared,scratch,hr,hr1,hzero,hprepare,h⟩

/-- Enclosing same-run delivery of semantic input, selected View,
Prepared::new and the reused gamma scratch into the full tx1 suffix. -/
theorem tx1_prepared_new (ops : Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H) (out : alloc.vec.Vec U8)
    (h : verifier.candidate.tx1 ops D pub publicBytes proof k hash none=ok (.Ok out)) :
    k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
      (prepared : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (semantic y1 : Slice U8) (v : verifier.View) (sem : r1_semantic.Verified H),
      ops.op5 proof semantic y1=ok (.Ok v) ∧
      ops.op9 D pub v.semantic hash none=ok (.Ok sem) ∧
      ops.op8 D sem v hash (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
      afterPrepare ops D publicBytes proof k hash none prepared scratch=ok (.Ok out) := by
  obtain ⟨hk,parsed,zero,prepared,scratch,hparsed,hscan,hzero,hprep,htail⟩ :=
    tx1_success ops D pub publicBytes proof k hash out h
  obtain ⟨semantic,y1,v,sem,hview,hsem,hnew⟩ :=
    PrepareReachability.prepare_success ops D pub proof hash prepared
      (Array.repeat 29#usize zero) scratch hprep
  exact ⟨hk,zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hnew,htail⟩

#print axioms afterPrepare
#print axioms tx1_success
#print axioms tx1_prepared_new
end AspisR1CurrentCaller.Tx1Reachability
'''
(B/'CurrentCompactTx1ReachabilityV1.lean').write_text(header+body+'\n'+proof)
