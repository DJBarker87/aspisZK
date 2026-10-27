from pathlib import Path
import re,json,hashlib,subprocess
E=Path(__file__).resolve().parent
RAW=Path('evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean')
KIT=Path('evidence/extraction-assoc6-20261027')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def clean(s):
 out=list(s);i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s[i:i+2]=='/-':out[i:i+2]='  ';depth+=1;i+=2
   elif s[i:i+2]=='-/':out[i:i+2]='  ';depth-=1;i+=2
   else:
    if s[i]!='\n':out[i]=' '
    i+=1
  elif s[i:i+2]=='/-' and not string:out[i:i+2]='  ';depth=1;i+=2
  elif s[i:i+2]=='--' and not string:
   j=s.find('\n',i);j=len(s) if j<0 else j;out[i:j]=' '*(j-i);i=j
  else:
   if s[i]=='"' and (i==0 or s[i-1]!='\\'):string=not string
   i+=1
 return ''.join(out)
def decls(p):
 s=p.read_text();c=clean(s)
 matches=list(re.finditer(r'(?m)^(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(def|abbrev|structure|inductive|theorem|lemma|opaque)\s+([^\s{(:]+)',c))
 out=[]
 for i,m in enumerate(matches):
  stop=matches[i+1].start() if i+1<len(matches) else len(s)
  part=c[m.start(1):stop];part=re.split(r'(?m)^\s*(?:end\b|namespace\b|#print\b|@\[)',part)[0].strip()
  before=s[:m.start(1)];meta=re.findall(r"Source: '([^']+)', lines ([0-9:]+)-([0-9:]+)",before[-1600:])
  out.append(dict(name=m[2],kind=m[1],line=before.count('\n')+1,text=part,source=(meta[-1] if meta else None)))
 return out
raw={r['name']:r for r in decls(RAW)}
external=Path('evidence/extraction-assoc2-20261027/XRj_L012/sources/XRj_generated/XRh_Release/FunsExternal.lean')
types=Path('evidence/extraction-assoc2-20261027/XRj_L002/sources/XRj_generated/XRh_Release/Types.lean')
rawtypes={r['name']:r for r in decls(types)}
ext={r['name']:r for r in decls(external)} if external.exists() else {}
# Direct source paths, with exact function line candidates. No guessed line is accepted.
rustpaths=list(Path('crates').glob('*/src/**/*.rs'))+list(Path('programs').glob('*/src/**/*.rs'))
index={}
for p in rustpaths:
 s=p.read_text()
 for m in re.finditer(r'(?m)^\s*(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?(?:unsafe\s+)?fn\s+([A-Za-z_0-9]+)',s):index.setdefault(m[1],[]).append(f'{p}:{s[:m.start()].count(chr(10))+1}')
rows=[];diffs=[];files=[]
for p in sorted(KIT.glob('XRn_Join_*.lean')):
 files.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
 for d in decls(p):
  n=d['name'];r=(rawtypes if p.stem=='XRn_Join_Types' else raw).get(n);norm=lambda s:re.sub(r'\s+',' ',s.replace('_root_.XRn_Join_Release.','').replace('_root_.XRh_Release.','').replace('XRn_Join_Release.','').replace('XRh_Release.','')).strip()
  same=r is not None and norm(d['text'])==norm(r['text'])
  if p.stem=='XRn_Join_Types' and same:continue
  if p.stem=='XRn_Join_Funs':
   diffs.append(dict(name=n,kit_line=d['line'],raw_line=r['line'] if r else None,equal_after_release_namespace_and_whitespace=bool(same),kit_text=d['text'] if not same else None,raw_text=r['text'] if r and not same else None))
   if same:continue
  # Include all non-Funs definitions, types/abbreviations too, rather than silently excluding carrier models.
  md=(r or ext.get(n) or {}).get('source')
  if p.stem=='XRn_Join_Field':md=d.get('source')
  rust=(md[0]+':'+md[1]) if md else None
  for prefix,path in [('aspis_core.field.wide_exact.','crates/aspis-core/src/field/wide_exact.rs'),('aspis_core.field.','crates/aspis-core/src/field.rs'),('aspis_core.circle.','crates/aspis-core/src/circle.rs'),('aspis_core.state_only_hiding.','crates/aspis-core/src/state_only_hiding.rs'),('fast_pairing.','crates/aspis-r1-cost-probe/src/fast_pairing.rs'),('r1_wire.','crates/aspis-r1-cost-probe/src/r1_wire.rs'),('r1_semantic.','crates/aspis-r1-cost-probe/src/r1_semantic.rs'),('verifier.','crates/aspis-r1-cost-probe/src/verifier.rs'),('compact.','crates/aspis-r1-cost-probe/src/compact.rs')]:
   if n.startswith(prefix) and not rust:
    hits=[x for x in index.get(n.rsplit('.',1)[-1],[]) if x.startswith(path+':')]
    if hits:rust='; '.join(hits)
    break
  candidates=index.get(n.rsplit('.',1)[-1],[])
  if not rust and len(candidates)==1:rust=candidates[0]
  if n=='aspis_core.r0.domain.FibreIndex.new':rust='crates/aspis-core/src/r0/domain.rs:11 (macro instantiated at 24)'
  if n=='aspis_core.r0.domain.FibreIndex.get':rust='crates/aspis-core/src/r0/domain.rs:18 (macro instantiated at 24)'
  if n=='aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31':rust='crates/aspis-core/src/r0/scalar.rs:89'
  if n=='aspis_core.r0.heap.filled':rust='crates/aspis-core/src/r0/heap.rs:5'
  if n=='aspis_core.r0.merkle.C1_TAG':rust='crates/aspis-core/src/r0/merkle.rs:15'
  if n=='aspis_core.r0.merkle.C2_TAG':rust='crates/aspis-core/src/r0/merkle.rs:16'
  if n=='sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once':rust='crates/aspis-r1-cost-probe/src/sampler.rs:122 (closure; aspis-core transcript fallback)'
  if rust and rust.startswith('src/'):rust='crates/aspis-core/'+rust
  if n=='field.M31.add':rust='crates/aspis-core/src/field.rs:62'
  if n=='field.P':rust='crates/aspis-core/src/field.rs:19'
  if n.startswith('aspis_core.field.') and not rust:
   path=Path('crates/aspis-core/src/field/wide_exact.rs') if '.wide_exact.' in n else Path('crates/aspis-core/src/field.rs')
   leaf=n.rsplit('.',1)[-1]
   hits=[m for m in re.finditer(r'(?m)^.*\b(?:const|struct) '+re.escape(leaf)+r'\b',path.read_text())]
   rust=str(path)+':'+str(path.read_text()[:hits[0].start()].count(chr(10))+1) if hits else 'library model (derived Clone/PartialEq, '+str(path)+')'
  if n=='aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq':rust='crates/aspis-core/src/circle.rs:10 (derived PartialEq)'
  if not rust and (n.startswith('XRn_Join_') or p.stem=='XRn_Join_TypesExternal' or n in ['oldQ','newQ','qzero','qone','qeq','canon','le32','validChunk','chunksValid','field.M31','field.CM31','field.QM31']):rust='library model'
  library=n.startswith(('core.','alloc.','Slice.','MutAArray.')) or p.stem.endswith('TypesExternal')
  verdict='UNDETERMINED';why='No complete source association; a small test cannot certify all inputs/effects.'
  if n in ['XRn_Join_mpow','XRn_Join_qpow','aspis_core.field.M31.inv']:
   verdict='UNFAITHFUL';why='Predecessor recursion; see XSd inverse-two and LPo exponent-two kernel counterexamples.'
  rows.append(dict(file=str(p),file_sha256=sha(p),line=d['line'],name=n,kind=d['kind'],counterpart=rust or ('library model' if library or n.startswith('XRn_Join_') else 'UNRESOLVED shipped counterpart'),rust_candidates=candidates,raw_body_line=r['line'] if r else None,text_comparison='MATCH modulo release namespace/whitespace' if same else 'DIFFERENT' if r else 'NO EMITTED BODY in raw Funs',verdict=verdict,reason=why,text_sha256=hashlib.sha256(d['text'].encode()).hexdigest()))
out=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),raw=dict(path=str(RAW),sha256=sha(RAW)),files=files,rows=rows,emitted_comparison=diffs,notes=['Lexical inventory; namespace resolution is separately kernel-audited.','Rust candidate lists are disambiguation data, not asserted identities.','All definition forms included; Funs matches omitted from stand-in table.'])
(E/'KSA_inventory.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['# Stand-in inventory','',f'Raw release: `{RAW}`, SHA256 `{sha(RAW)}`.','', 'Each row is a definition/carrier in the non-emitted files or a changed emitted declaration. UNDETERMINED means no complete association was established; source candidates are in JSON.','', '| File:line | Definition | Shipped counterpart or model | Raw comparison | Verdict |','|---|---|---|---|---|']
for r in rows:lines.append(f"| {Path(r['file']).name}:{r['line']} | `{r['name']}` | {r['counterpart']} | {r['text_comparison']} | {r['verdict']} |")
(E/'KSA_INVENTORY.md').write_text('\n'.join(lines)+'\n')
print('inventory',len(rows),'Funs',len(diffs),'changed',sum(not d['equal_after_release_namespace_and_whitespace'] for d in diffs))
