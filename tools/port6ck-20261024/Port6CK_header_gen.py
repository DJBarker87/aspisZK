from pathlib import Path
P=Path('docs/research/100bit-spend-path-20261013/lean')
s=(P/'CheckpointBytes5Resume.lean').read_text();s=s[s.index('def program '):s.index('private theorem if_tail')]
s=s.replace('def program (ops : ResumeOps)', 'def header (ops : ResumeOps)')
s=s.replace(' (v : transport.Variant) :', ' (v : transport.Variant)\n    (next : U8 → Usize → Slice U8 → Digest → Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)) :')
s=s.replace('liftResult (tail ops bytes v i4 end1 s6 a2)','liftResult (next i4 end1 s6 a2)')
s='''import Port6CK_Tail
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Header
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect
open Port6CK_Semantic (Unwrap)
open Port6CK_Ops (ops)
'''+s+'''
theorem tail_same (leaves : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (last : Usize) (suffix : Slice U8) (digest : Digest) :
    CheckpointBytes5Resume.tail leaves bytes v next last suffix digest =
      Port4A_NativeReader.tail leaves bytes v next last suffix digest := by rfl

theorem current_source (reserved : Bool) (unwrap : Unwrap) (bytes proof pub : Slice U8) :
    CheckpointBytes5Resume.program (ops reserved unwrap) bytes proof pub .S2 =
    header (CheckpointBytes4Ops.ops reserved) bytes proof pub .S2
      (Port4A_NativeReader.tail (ops reserved unwrap) bytes .S2) := by
  unfold CheckpointBytes5Resume.program header
  simp only [tail_same]
  try rfl

theorem reference_source (reserved : Bool) (bytes proof pub : Slice U8) :
    CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved) bytes proof pub .S2 =
    header (CheckpointBytes4Ops.ops reserved) bytes proof pub .S2
      (Port4A_NativeReader.tail (CheckpointBytes4Ops.ops reserved) bytes .S2) := by
  unfold CheckpointBytes5Resume.program header
  simp only [tail_same]
  try rfl

theorem size_s2 : CheckpointBytes4Ops.checkpointSize .S2=ok 1768#usize := by
  unfold CheckpointBytes4Ops.checkpointSize CheckpointBytes4Ops.finalLen
  simp only [bind_tc_ok]
  rw [Port4A_ReaderInstall.mul_value _ _ (by decide),bind_tc_ok,
    Port4A_ReaderInstall.add_value _ _ (by decide)]
  rfl

/-- The SAME accepted current source program returns the SAME pair and full
ordered log under the retained reader. All digest operands stay literal. -/
theorem accepted (reserved : Bool) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (bytes proof pub : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (before after : Log)
    (actual : run D hash (CheckpointBytes5Resume.program (ops reserved unwrap) bytes proof pub .S2) before = ok (.Ok (p,a),after)) :
    run D hash (CheckpointBytes5Resume.program (CheckpointBytes4Ops.ops reserved) bytes proof pub .S2) before = ok (.Ok (p,a),after) := by
  rw [current_source] at actual
  rw [reference_source]
  unfold header at actual ⊢
  dsimp only [CheckpointBytes4Ops.ops] at actual ⊢
  simp only [run_bind,run_lift,run_read,run_pure,run_ite,
    bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
'''
ind='  '
def put(t):
 global s
 s+='\n'.join(ind+l for l in t.splitlines())+'\n'
def step(name,pattern=None):
 put(f'''obtain ⟨{name},called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
rw [called]
simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢''')
def guard(cond):
 global ind
 condition = cond if ' > ' in cond else f'({cond})=true'
 put(f'''by_cases reject : {condition}
· try simp only [if_pos reject] at actual
  cases actual
· try simp only [if_neg reject] at actual ⊢''')
 ind+='  '
step('size')
put('have sizeEq : size=1768#usize := Result.ok.inj (called.symm.trans size_s2)')
guard('Slice.len bytes != size')
put('''have length : bytes.val.length=1768 := by
  have same : Slice.len bytes=size := by simpa only [bne_iff_ne,ne_eq,not_not] using reject
  have values := congrArg UScalar.val (same.trans sizeEq)
  exact values''')
step('magic');step('badMagic');guard('badMagic')
step('tagByte');step('tag');guard('tagByte != tag')
step('nextByte');guard('nextByte > 22#u8')
step('version');guard('version != 1#u8')
step('padding');step('iter');step('headerResult');put('rcases headerResult with ⟨badHeader,iterOut⟩\nsimp only [Aeneas.Std.uncurry] at actual ⊢');guard('badHeader')
step('end1');step('proofHashBytes');step('proofParts');step('proofDigest');step('badProof');guard('badProof')
step('pubHashBytes');step('pubParts');step('pubDigest');step('badPub');guard('badPub')
step('s6');step('domain');step('body');step('checkParts');step('a2')
put('''obtain ⟨result,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
cases result with
| Err e => cases actual
| Ok pair =>
  rcases pair with ⟨p1,a1⟩
  have reference := Port6CK_Tail.accepted reserved unwrap unwrap_ok bytes length
    nextByte end1 s6 a2 p1 a1 called
  dsimp only [CheckpointBytes4Ops.ops] at reference
  rw [reference]
  exact actual''')
s+='''
#print axioms tail_same
#print axioms current_source
#print axioms reference_source
#print axioms size_s2
#print axioms accepted
end AspisR1.Port6CK_Header
end
'''
(P/'Port6CK_Header.lean').write_text(s)
