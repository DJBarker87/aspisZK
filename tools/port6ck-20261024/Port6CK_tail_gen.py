from pathlib import Path
P=Path('docs/research/100bit-spend-path-20261013/lean')
s='''import Port6CK_Factor
import Port6CK_QueryFrame
import Port6CK_Roots
import Port6CK_Semantic
import Port6CK_Weights
import Port5Q2_ReaderValidate
import CheckpointBytes4SectionContents
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Tail
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port6CK_Semantic (Unwrap current)
/-- Current helper implementations at the retained parent's exact leaves.
The other leaves retain the existing Std/allocator/P6 interpretation. -/
def ops (reserved : Bool) (unwrap : Unwrap) : ResumeOps :=
  { CheckpointBytes4Ops.ops reserved with
    raw := fun N => Port5Q2_ReaderRaw.raw N (unwrap N)
    readK := current unwrap
    readE := Port5Q2_ReaderScalar.readE (fun N => Port5Q2_ReaderRaw.raw N (unwrap N))
      Port5Q2_ReaderScalar.decodeE
    readSemanticAlpha := Port5Q2_ReaderSemantic.semantic (current unwrap)
    validate := Port5Q2_ReaderValidate.validate
    readWeights := Port5Q2_ReaderWeights.weights (current unwrap) }

/-- Accepted current op18 body, on its SAME physical S2 bytes and returned
pair. Every sequential bound is derived from preceding reached reads. -/
theorem accepted (reserved : Bool) (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (bytes : Slice U8) (length : bytes.val.length=1768)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (actual : Port4A_NativeReader.tail (ops reserved unwrap) bytes .S2 i4 end1 s6 a2=ok (.Ok (p,a))) :
    Port4A_NativeReader.tail (CheckpointBytes4Ops.ops reserved) bytes .S2 i4 end1 s6 a2=ok (.Ok (p,a)) := by
  rw [Port6CK_Factor.source] at actual ⊢
  unfold Port6CK_Factor.tail at actual ⊢
  dsimp only [ops,CheckpointBytes4Ops.ops] at actual ⊢
  obtain ⟨bad,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  rw [called]
  simp only [bind_tc_ok]
  by_cases reject : bad=true
  · simp only [if_pos reject] at actual
    cases actual
  · simp only [if_neg reject] at actual ⊢
'''
ind='    '
cur='({ bytes := bytes, «at» := 80#usize } : verifier.Reader)';pos=80
count=0
# Each step records an explicit invariant at its actual returned reader.
def put(t):
 global s
 s+='\n'.join(ind+x for x in t.splitlines())+'\n'
def invariants(r,prior,advance):
 global cur,pos,count
 pos+=advance
 put(f'''have cursor{count} : {r}.at.val={pos} := by omega
have backing{count} : {r}.bytes=bytes := by first | exact backing | exact backing.trans oldBacking
have oldBacking := backing{count}
have room{count} : {r}.at.val+{1736-pos}≤{r}.bytes.val.length := by rw [cursor{count},backing{count},length]; decide
have size{count} : {r}.bytes.val.length≤4096 := by rw [backing{count},length]; decide''')
 cur=r;count+=1

def raw(n,name,r):
 global cur,pos,count
 put(f'''obtain ⟨⟨{name},{r}⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
have bound : ({cur}).at.val+{n}≤({cur}).bytes.val.length := by
  first | change 80+{n}≤bytes.val.length; omega | omega
rw [Port5Q2_ReaderRaw.reference {n}#usize (unwrap _) (unwrap_ok _) {cur} bound
  (by first | change bytes.val.length≤4096; omega | exact size{count-1})] at called
obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success {n}#usize {cur} {r} {name} bound called
rw [called]
simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢''')
 put(f'change {r}.at.val=({cur}).at.val+{n} at cursor')
 # first cursor projection explicit
 if count==0:put('change '+r+'.at.val=80+32 at cursor\nchange '+r+'.bytes=bytes at backing')
 invariants(r,cur,n)

def scalar(kind,name,r):
 global ind
 width=16 if kind=='k' else 32
 rewrite = f'show current unwrap {cur}=CheckpointBytes3Reader.readK {cur} from Port5Q2_ReaderScalar.current_k unwrap unwrap_ok {cur} bound size{count-1}' if kind=='k' else f'Port5Q2_ReaderScalar.current_e unwrap unwrap_ok {cur} bound size{count-1}'
 put(f'''obtain ⟨⟨value,{r}⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
have bound : ({cur}).at.val+{width}≤({cur}).bytes.val.length := by omega
rw [{rewrite}] at called
rw [called]
simp only [bind_tc_ok,Aeneas.Std.uncurry]
cases value with
| Err e =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame] at actual
  cases actual
| Ok {name} =>''')
 ind+='  '
 put('simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢')
 put(f'obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.{kind}_success {cur} {r} {name} bound called')
 invariants(r,cur,width)
raw(32,'state','r0');raw(32,'root0','r1');raw(32,'root1','r2')
for j in range(4):scalar('e',f'e{j}',f'er{j}')
scalar('k','rho','rhoReader')
put(f'''rw [Port6CK_Queries.cps_bind] at actual ⊢
obtain ⟨⟨queries,queriesReader⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
rw [Port6CK_Queries.reference unwrap unwrap_ok {cur} (by omega) size{count-1}] at called
obtain ⟨cursor,backing⟩ := Port6CK_QueryFrame.reached {cur} queriesReader queries (by omega) called
rw [called]
simp only [bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢''')
invariants('queriesReader',cur,88)
# validator
put('''obtain ⟨checked,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
rw [Port5Q2_ReaderValidate.reference] at called
rw [called]
simp only [bind_tc_ok]
cases checked with
| Err e =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame] at actual
  cases actual
| Ok unit =>''');ind+='  '
put('simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢')
# semantic
put(f'''obtain ⟨semanticResult,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
rw [Port6CK_Semantic.reference unwrap unwrap_ok bytes {cur}.at
  (by rw [cursor{count-1},length]; decide) (by omega)] at called
rw [called]
simp only [bind_tc_ok]
cases semanticResult with
| Err e =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame] at actual
  cases actual
| Ok pair =>''');ind+='  '
put(f'''rcases pair with ⟨semanticAlpha,semanticEnd⟩
simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
obtain ⟨model,decode,values,cursor⟩ := CheckpointBytes4SectionContents.semantic_contents bytes
  {cur}.at semanticEnd semanticAlpha (by rw [cursor{count-1},length]; decide) called
have semanticCursor : semanticEnd.val=568 := by omega
let sr : verifier.Reader := {{ {cur} with «at» := semanticEnd }}
have oldBacking : sr.bytes=bytes := backing{count-1}
have room{count} : sr.at.val+1168≤sr.bytes.val.length := by change semanticEnd.val+1168≤{cur}.bytes.val.length; rw [oldBacking,length]; omega
have size{count} : sr.bytes.val.length≤4096 := by rw [oldBacking,length]; decide
change (do let pair ← current unwrap sr; _) = _ at actual
change (do let pair ← CheckpointBytes3Reader.readK sr; _) = _''')
cur='sr';pos=568;count+=1
for j in range(4):scalar('k',f'coord{j}',f'cr{j}')
for j in range(2):scalar('e',f'wide{j}',f'wr{j}')
scalar('k','power','powerReader')
# finalLen/zero/filled exact controls with reference ops
put('''obtain ⟨n,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
have nEq : n=64#usize := Result.ok.inj called.symm
subst n
rw [called]
simp only [bind_tc_ok]
obtain ⟨zero,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
rw [called]
simp only [bind_tc_ok]
obtain ⟨allocated,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
rw [called]
simp only [bind_tc_ok]
cases allocated with
| Err e =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame] at actual
  cases actual
| Ok v =>''');ind+='  '
put('''simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry] at actual ⊢
obtain ⟨weightsResult,weightCall,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
cases weightsResult with
| Err e =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame] at actual
  cases actual
| Ok pair =>''');ind+='  '
put('''rcases pair with ⟨weights,finish⟩
''')
# pending allocation shape theorem investigate
put('''have vSize : v.val.length=64 := by
  obtain ⟨_,contents⟩ := CheckpointBytes3Allocation.filled_success_content reserved 64#usize zero v called
  rw [contents,List.length_replicate]
  rfl
''')
put(f'''have reference := Port6CK_Weights.accepted unwrap unwrap_ok bytes {cur}.at finish v weights
  (by rw [vSize,cursor{count-1},length]; decide) (by omega) weightCall
rw [reference]
simp only [bind_tc_ok]
exact actual''')
s+='\n#print axioms accepted\nend AspisR1.Port6CK_Tail\nend\n'
(P/'Port6CK_Tail.lean').write_text(s)
