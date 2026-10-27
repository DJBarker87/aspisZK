from pathlib import Path
import re,sys,hashlib,json
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
src=(R/'lean/JFx_DataCheckpoint00.lean').read_text()
cells=re.findall(r'def c\d+ : List U8 := \[([^\]]*)\]',src)
data=[int(v) for cell in cells for v in re.findall(r'(\d+)#u8',cell)]
assert len(data)==1768
lengths=','.join('JFx_DataCheckpoint00.c%02d_length'%i for i in range(len(cells)))
simp='JFx_DataCheckpoint00.bytes,'+lengths+',List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil'
config=[('State',80,32,'raw'),('Root0',112,32,'raw'),('Root1',144,32,'raw')]+[(n,o,32,'e') for n,o in zip(['Gamma','Kappa','Alpha0','Alpha1'],range(176,304,32))]+[('Rho',304,16,'k')]+[(f'Sem{i:02}',408+16*i,16,'k') for i in range(10)]+[(f'Z{i}',568+16*i,16,'k') for i in range(4)]+[('Claim',632,32,'e'),('Rhs',664,32,'e'),('Power',696,16,'k')]+[(f'Weight{i:02}',712+16*i,16,'k') for i in range(64)]
# The generator records each exact small window; no whole-buffer reduction.
weight_sources=[]
for name,off,n,kind in config:
 mod='JFq_'+name
 bs=data[off:off+n];lit=','.join(str(b)+'#u8' for b in bs)
 s=f'''import JFq_Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result AspisR1Stage2

def bytes : List U8 := [{lit}]
theorem length : bytes.length={n} := by simp only [bytes,List.length_cons,List.length_nil]
def value : Array U8 {n}#usize := ⟨bytes,length⟩
theorem selected : (JFx_NativeBytes.checkpoint.val.drop {off}).take {n}=bytes := by
  change (JFx_DataCheckpoint00.bytes.drop {off}).take {n}=bytes
  simp only [{simp}]
  rfl

theorem raw : CheckpointBytes3Reader.raw {n}#usize (JFq_Raw.reader {off}#usize)=
    ok (value,JFq_Raw.reader {off+n}#usize) :=
  JFq_Raw.source {off}#usize {n}#usize {off+n}#usize value (by decide) rfl selected
'''
 if kind!='raw':
  w=[int.from_bytes(bytes(bs[i:i+4]),'little') for i in range(0,n,4)]
  assert all(x<2147483647 for x in w),(name,w)
  def k(ws):return '⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩'%tuple(ws)
  val=k(w) if kind=='k' else '⟨'+k(w[:4])+','+k(w[4:])+'⟩'
  typ='QM31' if kind=='k' else 'wide_exact.WideExact'
  cap=kind.upper();fn='decode_'+kind+'_spec'
  wordfacts='\n'.join(f'  have h{i} : OraclePortCkptAbi2Extracted.word_spec (Array.to_slice value) {4*i}#usize=ok {x}#u32 := by\n    convert CheckpointBytes3Word.word_total (Array.to_slice value) {4*i}#usize (by change {4*i}+4≤{n};omega) using 1 <;> rfl' for i,x in enumerate(w))
  canon=' ∧ '.join(str(x)+' < 2147483647' for x in w)
  if kind=='k':
   shape='  rw [CheckpointBytes3ScalarShape.k_shape _ _ _ _ _ h0 h1 h2 h3]\n  rw [if_pos (by change '+canon+';decide)]\n  rfl'
  else:
   shape='  let words : Fin 8 → U32 := !['+','.join(str(x)+'#u32' for x in w)+']\n  rw [CheckpointBytes3EShape.e_shape _ (by exact value.property) words h0 h1 h2 h3 h4 h5 h6 h7]\n  rw [if_pos (by change ('+' ∧ '.join(str(x)+' < 2147483647' for x in w[:4])+') ∧ ('+' ∧ '.join(str(x)+' < 2147483647' for x in w[4:])+');decide)]\n  rfl'
  s+=f'''
def decoded : OraclePortCkptAbi2Extracted.aspis_core.field.{typ} := {val}
theorem decode : OraclePortCkptAbi2Extracted.{fn} (Array.to_slice value)=ok (some decoded) := by
{wordfacts}
{shape}

def scalar := CheckpointBytes3Namespaces.from{cap} decoded
theorem source : CheckpointBytes3Reader.read{cap} (JFq_Raw.reader {off}#usize)=
    ok (.Ok scalar,JFq_Raw.reader {off+n}#usize) :=
  JFq_Scalar.{kind} {off}#usize {off+n}#usize value decoded raw decode
#print axioms decode
#print axioms source
'''
 s+=f'''\n#print axioms length
#print axioms selected
#print axioms raw
end AspisR1.{mod}
end
'''
 if name.startswith('Weight'):
  weight_sources.append((name,s));continue
 f=R/'lean'/f'{mod}.lean'
 if '--check' in sys.argv: assert f.read_text()==s,f
 else:f.write_text(s)
for group in range(16):
 content='import JFq_Scalar\n'+''.join(s.replace('import JFq_Scalar\n','') for _,s in weight_sources[4*group:4*group+4])
 i=4*group;off=712+16*i
 steps='\n'.join(f'  have step{j} := JFq_Weight{j:02}.source\n  dsimp only [JFq_Raw.reader] at step{j}' for j in range(i,i+4))
 content+=f'''\nnoncomputable section
namespace AspisR1.JFq_WeightBlock{group:02}
open Aeneas Aeneas.Std Result AspisR1Stage2
def values : List aspis_core.field.QM31 := [{','.join(f'JFq_Weight{j:02}.scalar' for j in range(i,i+4))}]
theorem source : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK
    JFx_NativeBytes.checkpoint 4 {off}#usize=ok (.Ok (values,{off+64}#usize)) := by
{steps}
  simp only [Port5Q2_ReaderWeights.reads,{','.join(f'step{j}' for j in range(i,i+4))},
    bind_tc_ok,Aeneas.Std.uncurry]
  rfl
#print axioms source
end AspisR1.JFq_WeightBlock{group:02}
end
'''
 f=R/'lean'/f'JFq_Weights{group:02}.lean'
 if '--check' in sys.argv:assert f.read_text()==content,f
 else:f.write_text(content)
 if '--check' not in sys.argv:
  for name,_ in weight_sources[4*group:4*group+4]:(R/'lean'/f'JFq_{name}.lean').unlink(missing_ok=True)
(P/'JFq_WINDOWS.json').write_text(json.dumps(dict(checkpoint_source_sha256=hashlib.sha256(src.encode()).hexdigest(),checkpoint_bytes_sha256=hashlib.sha256(bytes(data)).hexdigest(),windows=config),indent=2)+'\n')
print(len(config),'windows')
