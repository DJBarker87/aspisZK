#!/usr/bin/env python3
"""Audit actual Reader/scalar_k canonicality and the reused parser/sampler pins."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4]
ev=area/'evidence/cu-equivalence-20261019';start=time.monotonic();sha=lambda b:hashlib.sha256(b).hexdigest()
parse_axioms=lambda s:list(filter(None,re.sub(r'\s+','',s).split(',')))
checks=['prepare-rho-parser-reuse.py','extract-rho-reader.py','emit-rho-reader.py','extract-rho-scalar-k.py','emit-rho-scalar-k.py']
for name in checks:subprocess.run([sys.executable,str(here/name),'--check'],check=True,capture_output=True)
targets={
'DecodeKOptionDiscriminantBridge':'rho-parser-option-bridge-a',
'AspisR1RhoParser/Funs':'rho-parser-funs-a',
'CuSavingsRhoParserM31':'rho-parser-m31-a',
'CuSavingsRhoParserCanonicality':'rho-parser-cmq-a',
'AspisR1RhoReader/Types':'rho-reader-types-a',
'AspisR1RhoReader/FunsExternal':'rho-reader-externals-a',
'AspisR1RhoReader/Funs':'rho-reader-funs-a',
'CuSavingsRhoReader':'rho-reader-proof-c',
'AspisR1RhoScalarK/Types':'rho-scalar-k-types-a',
'AspisR1Qm31SamplerIndex/Types':'rho-sampler-repin-types-a',
'AspisR1Qm31SamplerIndex/Funs':'rho-sampler-repin-funs-a',
'ExtractedQM31SamplerDigits':'rho-sampler-repin-digits-a',
'AspisR1RhoScalarK/FunsExternal':'rho-scalar-k-externals-c',
'AspisR1RhoScalarK/Funs':'rho-scalar-k-funs-b',
'CuSavingsRhoScalarK':'rho-scalar-k-proof-c'}
results={};receipts={};objects={}
for module,attempt in targets.items():
 path=ev/attempt/'receipt.json';r=json.loads(path.read_text());receipts[module]=r
 assert r['exit_status']==0
 source=area/'lean'/(module+'.lean')
 if module=='DecodeKOptionDiscriminantBridge':
  source=area/'lean/extracted-decode-k-canonicality-20261018/DecodeKOptionDiscriminantBridge.lean'
 if module.startswith('AspisR1Qm31SamplerIndex/'):
  source=area/'lean/extracted-qm31-index-sampler-20261016'/(module+'.lean')
 assert sha(source.read_bytes())==r['source_sha256']==sha((ev/attempt/'source.lean').read_bytes())
 log=(ev/attempt/'stdout.log').read_text();assert log==r['print_axioms_output']
 assert 'sorryAx' not in log and 'error:' not in log
 decls=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert decls
 allowed={'propext','Classical.choice','Quot.sound'}
 if module in ['AspisR1RhoReader/Funs','CuSavingsRhoReader']:allowed.add('core.fmt.Formatter')
 for name,axioms in decls:assert set(parse_axioms(axioms)) <= allowed,(module,name,axioms)
 if module=='CuSavingsRhoReader':assert 'axiom Aeneas.Std.core.fmt.Formatter : Type' in log
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 objects[module.replace('/','.')]=r['object_sha256']
 results[module]=dict(attempt=attempt,source_repository_path=str(source.relative_to(repo)),source_sha256=r['source_sha256'],
  receipt_sha256=sha(path.read_bytes()),object_sha256=r['object_sha256'],command=r['command'],source_revision=r['source_revision'],features=r['features'],
  exit=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],cgroup_swap_bytes=r['cgroup_swap_bytes'],
  declarations=[dict(name=n,axioms=parse_axioms(a)) for n,a in decls])
for module,r in receipts.items():
 for item in r['direct_imports']:
  if item['module'] in objects:assert item['sha256']==objects[item['module']],(module,item['module'])
# Preserve the source identities of the original proofs being reused.
mapping=json.loads((area/'lean/extracted-qm31-index-sampler-20261016/SOURCE-MAPPING.json').read_text())
for module,entry in mapping['modules'].items():assert results[module.replace('.','/')]['source_sha256']==entry['sha256']
old_digits=json.loads((area/'evidence/qm31-index-sampler-digits-432-20261016/manifest.json').read_text())
assert results['ExtractedQM31SamplerDigits']['source_sha256']==old_digits['source_sha256']
fmt=json.loads((ev/'rho-reader-fmt-boundary.json').read_text())
assert fmt[0]['sha256']=='7c17a7af2952203781321279f0c569410d27bd9f1233fa3f5d1ec6f67a07f068'
assert 'axiom core.fmt.Formatter : Type' in fmt[-1]['text']
assert '(_ : core.fmt.Debug E)' in fmt[-1]['text']
assert '#print axioms unwrap_debug_unused' in (area/'lean/CuSavingsRhoReader.lean').read_text()
for folder in ['AspisR1RhoParser','AspisR1RhoReader','AspisR1RhoScalarK']:
 for p in (area/'lean'/folder).glob('*.lean'):assert not re.search(r'(?m)^axiom\s',p.read_text()),p
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
usage=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='SOURCE_READER_AND_RHO_SAMPLING_CANONICALITY_CHECKED_CALLER_COMPOSITION_OPEN',candidate_complete=False,
 source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),source_checks=checks,successes=results,
 covered=['Byte-identical old/candidate/current Reader.raw and Reader.k emitted whole; strict parser proof bodies reused by identifier/import transport.',
 'Every successful actual k read yields canonical QM31, keeps bytes and advances at by 16; complete k outcome equation retains raw/parser errors and divergence.',
 'Exact unchanged scalar_k emitted whole with only its common block operation universally parameterized; actual source sampler/constructors/trace are bound.',
 'Actual scalar_k outcome and success theorems derive canonical rho and the successful block/sampler calls; no child-call success or canonicality assumption is supplied.',
 'Only source sampler modules and digits theorem re-pinned after discovering the current cached object lacked a matching source receipt. No soundness rebuild or full regression.'],
 inherited_opaque_type=dict(name='Aeneas.Std.core.fmt.Formatter',kind='Type',scope=['AspisR1RhoReader/Funs','CuSavingsRhoReader'],
  selected_original_object_sha256=fmt[0]['sha256'],reason='Unchanged original unwrap API takes Debug; no property of Formatter is postulated. unwrap_debug_unused proves this parameter computationally irrelevant.',new_equivalence_premise=False),
 remaining=['Actual resume weights traversal and complete Prepared/resume output dataflow','Power/count/length invariants through complete accumulate and transaction callers',
 'Optimized coefficient Option reborrow source binding','Reserve/SDK sufficient-resource source binding and final transaction observable-context theorem'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,
  peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,
  print_axioms='N/A source/receipt audit; per-target exact axiom lists above'))
(ev/'RHO-CANONICAL-INPUTS.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])
