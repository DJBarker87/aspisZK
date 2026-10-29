"""Make the retained full caller a typed functor over explicit external dictionaries.
No implementation or source-refinement law is inferred from a dictionary field.
"""
from pathlib import Path
import re,json,hashlib
I=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/output-73331')
O=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/full-adapter');O.mkdir(exist_ok=True)
E=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/full-adapter')
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
def extern(file):
 s=(I/file).read_text()
 blocks=re.findall(r'^axiom\s+([A-Za-z0-9_.]+)\s*([\s\S]*?)(?=\n/--|\Z)',s,re.M)
 assert len(blocks)==len(re.findall(r'^axiom\b',s,re.M))
 return [(n,t.strip()) for n,t in blocks]
def header(imports):
 return ''.join('import '+i+'\n' for i in imports)+'open Aeneas Aeneas.Std Result ControlFlow Error\nnamespace ProverRwFull\n\n'
def dictionary(kind,blocks,imports):
 cname='External'+kind
 s=header(imports)+'class '+cname+(' [ExternalTypes]' if kind=='Funs' else '')+' where\n'
 mapping=[]
 for i,(n,t) in enumerate(blocks):
  op='op'+str(i);s+='  '+op+' '+t.replace('\n','\n    ')+'\n'
  mapping.append(dict(name=n,field=op,signature=t))
 s+='\n'
 for i,(n,t) in enumerate(blocks):
  args='[ext : ExternalTypes]' if kind=='Types' else '[types : ExternalTypes] [ext : ExternalFuns]'
  rhs='@'+cname+'.op'+str(i)+(' ext' if kind=='Types' else ' types ext')
  s+='abbrev '+n+' '+args+' := '+rhs+'\n'
 s+='\nend ProverRwFull\n'
 return s,mapping
te,tm=dictionary('Types',extern('TypesExternal_Template.lean')+[('F64',': Type'),('core.fmt.Formatter',': Type')],['Aeneas'])
te=te.replace('end ProverRwFull', '''structure core.fmt.Debug [ExternalTypes] (Self : Type) where
  fmt : Self → core.fmt.Formatter → Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

end ProverRwFull''')
(O/'ProverRwFullExternalTypes.lean').write_text(te)
t=(I/'Types.lean').read_text()
t=t.replace('import ProverRwCaller.TypesExternal','import R1Z.ProverRwFullExternalTypes').replace('namespace ProverRwCaller','namespace ProverRwFull\nvariable [ExternalTypes]').replace('end ProverRwCaller','end ProverRwFull')
t=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',t,flags=re.M)
adapters=[]
# The backend generates global names from the final enum segment; replace them
# with named fully qualified instances, preserving constructor order and codes.
pat=r'(@\[[^\]]*\]\n)?inductive ([A-Za-z0-9_.]+) where\n((?:\|[^\n]*\n(?:  [^\n]*\n)*)+)'
for m in list(re.finditer(pat,t)):
 if not m[1] or 'discriminant isize' not in m[1]:continue
 n=m[2];attr=m[1].replace('discriminant isize, ','').replace('@[discriminant isize]\n','')
 ctors=[(r[1],r[2].count('→')) for r in re.finditer(r'^\| ([A-Za-z0-9_]+) :([\s\S]*?)(?=^\||\Z)',m[3],re.M)]
 d='\ndef '+n+'.read_discriminant (x : '+n+') : Isize :=\n  match x with\n'
 d+=''.join('  | .'+c+' _'*args+' => '+str(i)+'#isize\n' for i,(c,args) in enumerate(ctors))
 d+='\ninstance _root_.ProverRwFull.'+n+'.instDiscriminant : Discriminant '+n+' Isize where\n  read_discriminant := '+n+'.read_discriminant\n'
 t=t.replace(m[0],attr+'inductive '+n+' where\n'+m[3]+d)
 adapters.append(dict(name=n,constructors=ctors))
(O/'ProverRwFullTypes.lean').write_text(t)
fe,fm=dictionary('Funs',extern('FunsExternal_Template.lean')+[('std.fs.File.Insts.StdIoWrite.write_all',': std.fs.File → Slice Std.U8 → Result ((core.result.Result Unit std.io.error.Error) × std.fs.File)')],['R1Z.ProverRwFullTypes'])
(O/'ProverRwFullExternalFuns.lean').write_text(fe)
f=(I/'Funs.lean').read_text().replace('import ProverRwCaller.Types','import R1Z.ProverRwFullTypes').replace('import ProverRwCaller.FunsExternal','import R1Z.ProverRwFullExternalFuns').replace('namespace ProverRwCaller','namespace ProverRwFull\nvariable [ExternalTypes] [ExternalFuns]').replace('end ProverRwCaller','end ProverRwFull')
f=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',f,flags=re.M)
f=f.replace('variable [ExternalTypes] [ExternalFuns]', '''variable [ExternalTypes] [ExternalFuns]

def unwrapSlice {T E : Type} : core.result.Result T E → Result T
  | .Ok v => .ok v
  | .Err _ => .fail .panic
''')
f=f.replace('core.result.Result.unwrap core.fmt.DebugTryFromSliceError','unwrapSlice')
f=f.replace('core.result.Result.unwrap aspis_core.r0.Error.Insts.CoreFmtDebug','unwrapSlice')
# Expand recursive PartialEq defaults, whose emitted impl_def is incompatible
# with section dictionary instances in this backend. No equality operation changes.
def expand_eq(m):
 name=m[1]; sig=m[2]; body=m[3]
 eq=body.split('eq :=',1)[1].split('ne :=',1)[0].strip()
 return 'def '+name+sig+' := {\n  eq := '+eq+'\n  ne := fun a b => do\n    let equal ← '+eq+' a b\n    ok (!equal)\n}'
f=re.sub(r'impl_def\s+([A-Za-z0-9_.]+)([\s\S]*?) := \{([\s\S]*?)\n\}',lambda m: expand_eq(m) if 'CoreCmpPartialEq' in m[1] else m[0],f)
f=f.replace('impl_def std.fs.File.Insts.StdIoWrite','def std.fs.File.Insts.StdIoWrite')
f=f.replace('std.io.Write.write_all.default std.fs.File.Insts.StdIoWrite','std.fs.File.Insts.StdIoWrite.write_all')
# Avoid capture by the source helper host_semantic.lift.
f=re.sub(r'(?<![A-Za-z0-9_.])lift(?=\s*\()', 'Aeneas.Std.lift',f)
# Shift API normalization: backend operations take U32 counts.
shift_changes=[]
pattern=r'(Std\.(?:Usize|U8|U16|U32|U64)\.wrapping_sh[lr]) ([A-Za-z0-9_]+(?:#[a-z0-9]+)?) ([A-Za-z0-9_]+(?:#[a-z0-9]+)?)'
def shift(m):
 op,x,y=m.groups()
 if y.endswith('#u32'): return m[0]
 if '#' in y: rhs=y.split('#')[0]+'#u32'
 else: rhs='(UScalar.cast .U32 '+y+')'
 shift_changes.append(dict(before=m[0],after=op+' '+x+' '+rhs))
 return op+' '+x+' '+rhs
f=re.sub(pattern,shift,f)
# Stateful closure lowering emits identity backwards continuations while the
# standard Fn traits have consumed/returned state in their existing API.
root='RealR1_client.prove_for_proof_accounts.closure.'
fn1=root+'Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once'
fnm=root+'Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut'
f=f.replace('call_once :=\n    '+fn1+'\n    coreopsfunctionFnMutT0TupleUsizeArrayU832Inst', 'call_once := fun c i => do\n    let (r, _) ← '+fn1+' coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i\n    ok r')
f=f.replace('call_mut :=\n    '+fnm+'\n    coreopsfunctionFnMutT0TupleUsizeArrayU832Inst', 'call_mut := fun c i => do\n    let (r, c1, back) ← '+fnm+' coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i\n    ok (r, back c1)')
f=f.replace('let (r, nonce_store1, _) ←\n    prover.prove_masked_retrying_with','let (r, nonce_store1) ←\n    prover.prove_masked_retrying_with')
# Rust has one BlockSize associated type inherited through both parents;
# the emission incorrectly invents two unrelated carrier parameters here.
start=f.index('def digest.core_api.wrapper.CoreWrapper.Insts.DigestFixedOutput ')
end=f.index('\n/--',start)
block=f[start:end]
for suffix in ['BlockSize','Clause0_ArrayType']:
 duplicate='Clause0_Clause1_Clause0_'+suffix
 original='Clause0_Clause0_Clause0_'+suffix
 assert '{'+duplicate+' : ' in block or duplicate in block
 # Drop the duplicated binder, then use the one actual associated carrier.
 block=re.sub(r'\{'+duplicate+r'\s*:\s*Type\}\s*','',block)
 block=block.replace(duplicate,original)
f=f[:start]+block+f[end:]
# toStr's default proof uses decide +native in the backend. Supply kernel
# proofs for these 33 tiny literal byte-length bounds instead.
f=re.sub(r'toStr ("[^"\n]*")',lambda m: 'toStr '+m[1]+' (by rw [String.size_toByteArray]; change '+str(len(m[1][1:-1].encode()))+' ≤ U32.max; norm_num [U32.max,U32.numBits])',f)
(O/'ProverRwFullFuns.lean').write_text(f)
(E/'caller-dictionary-adapter.json').write_text(json.dumps(dict(inputs={p.name:sha(p.read_text()) for p in I.glob('*.lean')},outputs={p.name:sha(p.read_text()) for p in O.glob('ProverRwFull*.lean')},types=tm,functions=fm,discriminants=adapters,shift_changes=shift_changes,additional_boundaries=["F64 backend type", "Formatter backend type and Debug carrier", "std::fs::File Write::write_all"],qualification='Typed external dictionary parameters only. No implementations, contracts or native refinement supplied by parameterization. Generated resource overrides removed. No template axioms imported.'),indent=2)+'\n')
print(len(tm),len(fm),len(adapters))
