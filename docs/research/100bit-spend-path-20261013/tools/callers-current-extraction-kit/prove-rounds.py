#!/usr/bin/env python3
"""Generate only finite10-row monadic success inversions, no arithmetic reduction."""
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[4];P=R/'docs/research/100bit-spend-path-20261013/lean/ExtractedSemanticRoundsReachability.lean'
head='''import ExtractedSemanticRoundsModel
import ExtractedDigest32Begin
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.RoundCalls
open r1_wire BeginCalls
abbrev QM := aspis_core.field.QM31
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem update_set {α : Type} {n : Usize} (v : Array α n) (i : Usize)
    (x : α) (out : Array α n) (h : Array.update v i x = ok out) :
    out = v.set i x := by
  unfold Array.update at h
  split at h
  · cases h
  · exact (Result.ok.inj h).symm
private theorem add_exact {ty : UScalarTy} (a b c : UScalar ty)
    (hc : c.val = a.val + b.val) : a + b = ok c := by
  obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := a) (y := b) (by scalar_tac))
  have he : z = c := by scalar_tac
  simpa only [he] using hz

def rows : List U8 := ['''+','.join(str(i)+'#u8'for i in range(15,25))+''']
/-- Actual whole helper success supplies every source row call, ordered returned
alpha value, and transcript carry, for any explicit decode/arithmetic functions. -/
theorem rounds_success {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
    (pre : Prefix) (self after : SemanticTranscript H) (running : QM)
    (alpha : Array QM 10#usize)
    (h : RoundModel.rounds B D pre self = ok (.Ok (running,alpha,after))) :
    ∃ qs, SemanticRun D pre rows self after qs ∧ qs = alpha.val := by
'''
lines=[head]
for n in range(10):lines.append(f'  have hrow{n} : 15#u8 + UScalar.cast .U8 {n}#usize = ok {15+n}#u8 := add_exact _ _ _ (by scalar_tac)\n')
lines.append('  unfold RoundModel.rounds at h\n')
norm='  try dsimp (config := { zeta := true, zetaDelta := true }) only at h\n  try simp (config := { zeta := true, zetaDelta := true }) only [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual, core.convert.FromSame.from, lift, bind_tc_ok, '+', '.join('hrow'+str(n)for n in range(10))+'] at h\n'
def unwrap(ret,name):
 return f'''  have hok_{name} : ∃ value, {ret} = core.result.Result.Ok value := by
    cases {ret} with
    | Ok value => exact ⟨value,rfl⟩
    | Err e =>
'''+''.join('    '+l for l in norm.splitlines(True))+'''      cases h
'''+f'  obtain ⟨{name},rfl⟩ := hok_{name}\n'+norm
lines+=['  obtain ⟨initret,hinitrecord,h⟩ := bind_success (Prefix.validated_record pre 14#u8) _ _ h\n',unwrap('initret','initrecord'),'  obtain ⟨initvalues,hinitdecode,h⟩ := bind_success (B.decode 1#usize initrecord 0#usize) _ _ h\n',unwrap('initvalues','decoded_initial'),'  obtain ⟨initial,hinitindex,h⟩ := bind_success (Array.index_usize decoded_initial 0#usize) _ _ h\n',norm]
a='Array.repeat 10#usize aspis_core.field.QM31.ZERO';t='self'
for n in range(10):
 row=15+n
 lines+=[f'  obtain ⟨recordret{n},hr{n},h⟩ := bind_success (Prefix.validated_record pre {row}#u8) _ _ h\n',unwrap(f'recordret{n}',f'record{n}'),f'  obtain ⟨polyret{n},hdecode{n},h⟩ := bind_success (B.decode 28#usize record{n} 0#usize) _ _ h\n',unwrap(f'polyret{n}',f'polynomial{n}'),f'  obtain ⟨boundary{n},hboundary{n},h⟩ := bind_success (B.boundary polynomial{n}) _ _ h\n',f'  obtain ⟨bad{n},hcompare{n},h⟩ := bind_success _ _ _ h\n',f'''  have hfalse{n} : bad{n} = false := by
    cases bad{n} with
    | false => rfl
    | true => simp only [Bool.true_eq_true, ↓reduceIte] at h; cases h
  subst bad{n}
''',norm,f'  obtain ⟨sampleret{n},t{n+1},hs{n},h⟩ := pair_bind_success (SemanticTranscript.semantic_validated D {t} record{n}) _ _ h\n',unwrap(f'sampleret{n}',f'q{n}'),f'  obtain ⟨alpha{n+1},hupdate{n},h⟩ := bind_success (Array.update ({a}) {n}#usize q{n}) _ _ h\n',f'  have hset{n} := update_set ({a}) {n}#usize q{n} alpha{n+1} hupdate{n}\n',f'  subst alpha{n+1}\n',f'  obtain ⟨value{n},hvalue{n},h⟩ := bind_success _ _ _ h\n',norm]
 a=f'({a}).set {n}#usize q{n}';t=f't{n+1}'
qs='['+','.join('q'+str(i)for i in range(10))+']';lines+=[f'  have he := core.result.Result.Ok.inj (Result.ok.inj h)\n',f'  have ht : after = t10 := (congrArg (fun x => x.2.2) he).symm\n',f'  have ha : alpha = ({a}) := (congrArg (fun x => x.2.1) he).symm\n','  rw [ht,ha]\n',f'  refine ⟨{qs},?_,?_⟩\n','  · unfold rows\n']
for n in range(10):lines.append(f'    apply SemanticRun.cons hr{n} hs{n}\n')
lines+=['    exact SemanticRun.nil t10\n','  · rfl\n', '''
theorem rounds_carry {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
    (pre : Prefix) (self after : SemanticTranscript H) (running : QM)
    (alpha : Array QM 10#usize)
    (h : RoundModel.rounds B D pre self = ok (.Ok (running,alpha,after))) :
    after.hash = self.hash ∧ after.next_row.val = self.next_row.val + 10 := by
  obtain ⟨qs,run,_⟩ := rounds_success B D pre self after running alpha h
  simpa only [rows,List.length_cons,List.length_nil,Nat.reduceAdd] using run.carry D pre
#print axioms rounds_success
#print axioms rounds_carry
end AspisR1PublicPreparation.RoundCalls
'''];P.write_text(''.join(lines));print(P)
