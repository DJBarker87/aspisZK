#!/usr/bin/env python3
"""Read-only source coverage audit. No extraction, compiler, or native execution."""
from pathlib import Path
import hashlib, json, re, subprocess, time

BASE = '946718387da2351a46a3a095a94f1f003d5f8185'
ROOT = Path('/Users/dominic/ZK/.worktrees/pv-evh')
E = ROOT / 'evidence/pv-evh3-20261029'
assert Path.cwd() == ROOT
assert subprocess.check_output(['git','branch','--show-current'], text=True).strip() == 'codex/pv-evh-20261029'
started = time.monotonic()

def read(path):
    return subprocess.check_output(['git','show',BASE+':'+path]).decode()

def pin(path):
    b = read(path).encode()
    return dict(path=path, revision=BASE, git_blob=subprocess.check_output(
        ['git','rev-parse',BASE+':'+path],text=True).strip(),
        sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))

def write(name, value):
    (E/name).write_text(json.dumps(value,indent=2)+'\n')

prefix='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'
funs_path=prefix+'ProverRwFullFuns.lean'
ext_path=prefix+'ProverRwFullExternalFuns.lean'
funs, ext = read(funs_path), read(ext_path)
# Every class field, including generic and non-effect operations. No purity inference.
class_text=ext.split('class ExternalFuns [ExternalTypes] where\n',1)[1].split('\nabbrev ',1)[0]
fields=list(re.finditer(r'^  (op\d+)\b',class_text,re.M))
aliases={op:name for name,op in re.findall(r'^abbrev (\S+) .*? := @ExternalFuns\.(op\d+) types ext$',ext,re.M)}
assert len(aliases)==len(fields)==262
assert set(aliases)=={f'op{i}' for i in range(262)}
# Source comments identify the enclosing Rust function and callsite provenance.
lines=funs.splitlines()
declarations={funs[:m.start()].count('\n')+1:m[1] for m in re.finditer(r'^(?:def|abbrev)\s+(\S+)',funs,re.M)}
source=''; enclosing=''; contexts={}
for n,line in enumerate(lines,1):
    if "Source: '" in line: source=line.strip()
    if n in declarations: enclosing=declarations[n]
    contexts[n]=(source,enclosing)
ops=[]
for index,match in enumerate(fields):
    op=match[1]; end=fields[index+1].start() if index+1<len(fields) else len(class_text)
    signature=class_text[match.start():end].strip()
    name=aliases[op]
    sites=[]
    for n,line in enumerate(lines,1):
        if re.search(r'(?<![\w.])'+re.escape(name)+r'(?![\w.])',line):
            sites.append(dict(path=funs_path,line=n,text=line.strip(),
                              rust_source=contexts[n][0],enclosing_declaration=contexts[n][1]))
    category='opaque/helper: effect closure requires source inspection'
    event='UNBOUND; no native-event implementation'
    if name.startswith('std.fs.') or name.startswith('std.io.Write.'):
        category='file/effect or file configuration'; event='otherFile (payload association OPEN)'
    if name=='getrandom.fill':
        category='entropy'; event='side (visible metadata only; payload and world association OPEN)'
    if name.startswith('alloc.'):
        category='allocation/container: allocation-failure closure OPEN'; event='side / diagnostic terminal on failure (OPEN)'
    if 'zeroize' in name or name=='core.sync.atomic.compiler_fence' or name=='core.mem.drop':
        category='erasure/drop/runtime effect'; event='side / diag3 and terminal on unwind/abort (OPEN)'
    if name=='host_work.map':
        category='worker/scheduling/panic effects'; event='side / diag3 and terminal (OPEN)'
    assert 'Result' in signature
    ops.append(dict(op=op,alias=name,signature=signature,category=category,
                    planned_native_event=event,implementation='ABSENT',textual_call_sites=sites))
write('external-interface.json',dict(pins=[pin(ext_path),pin(funs_path)],
      method='All 262 op fields and aliases; textual call sites, not a resolved call graph or macro expansion.',operations=ops))
# Check selected source authority agrees with the inherited h5 resolution.
authority=json.loads(read('evidence/pv-rj4idb-20261029/source-resolution.json'))['projects']
resolution=[]
for module in ['R1Z.ProverRwFullFuns','R1Z.ProverRwFullExternalFuns','R1Z.ProverRwFullTypes','R1Z.ProverRwFullExternalTypes']:
    record=authority[module]
    selected=pin(record['path'])
    assert selected['sha256']==record['source_sha256']
    resolution.append(dict(module=module,inherited=record,baseline=selected))
write('source-authority.json',resolution)

sources=[
 'tools/r1-cost-probe/src/bin/devnet_spend.rs',
 'tools/r1-cost-probe/src/bin/devnet_spend/plan.rs',
 'tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs',
 'tools/r1-cost-probe/Cargo.toml',
 'tools/r1-cost-probe/Cargo.lock',
 'crates/aspis-r1-cost-probe/src/RealR1_client.rs',
 'crates/aspis-prover/src/state_only_entropy.rs',
 'lean/PV_RJ4IDB_NativeTrace.lean', 'lean/PV_EVH_RuntimeBinding.lean',
 'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwEntropyIteration.lean',
 'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_Source.lean',
 'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_W_ProverEntry.lean',
 'evidence/pv-diag3-20261029/PV_DIAG3_Client.lean']
write('source-pins.json',[pin(p) for p in sources])
# Never infer complete executable coverage from a library root or arbitrary handlers.
pattern="Source: 'tools/r1-cost-probe/src/bin/devnet_spend"
scan=subprocess.run(['git','grep','-n','-F',pattern,BASE,'--','*.lean','*.lean.txt'],capture_output=True,text=True)
assert scan.returncode in (0,1),scan.stderr
assert scan.returncode==1 and not scan.stdout
assert 'def RealR1_client.prove_for_proof_accounts\n' in funs
assert 'devnet_spend' not in funs
assert not re.search(r'^abbrev .*?(?:Instant|stdout|stderr|println|process\.exit|abort)',ext,re.M)
write('executable-coverage.json',dict(command=scan.args,exit=scan.returncode,stdout=scan.stdout,stderr=scan.stderr,
    interpretation='No executable-source provenance marker in tracked .lean/.lean.txt at baseline; no main/plan definition in selected extraction. This is not a claim about untracked host files.',
    extracted_library_entry='ProverRwFull.RealR1_client.prove_for_proof_accounts',
    missing_executable_entries=['devnet_spend::main','devnet_spend::plan::run','devnet_spend::plan::prove'],
    result_dictionary_has_world=False,result_dictionary_has_writer=False))
# Direct visible Rust anchors: an audit map, NOT a complete dependency call cone.
patterns=[
 ('stdin',r'read_to_string|stdin\(', 'side'),
 ('file',r'fs::|file\.write_all|file\.sync_all', 'otherFile / proofWrite / statementWrite'),
 ('stdout',r'println!', 'printed'),
 ('clock',r'Instant::now|started\.elapsed', 'wall / side'),
 ('panic',r'panic!|unwrap\(|expect\(', 'diag3 / terminal panic'),
 ('entropy',r'getrandom::fill', 'side (visible metadata only)'),
 ('result/publication',r'RealR1_client::prove_for_proof_accounts|Ok\(json!', 'count / returned / publication binding')]
anchors=[]
for p in sources[:3]+[sources[5],sources[6]]:
    for n,line in enumerate(read(p).splitlines(),1):
        for kind,pat,event in patterns:
            if re.search(pat,line):
                anchors.append(dict(path=p,line=n,kind=kind,source=line,planned_event=event,status='NO executable writer binding'))
write('rust-effect-anchors.json',dict(scope='Direct textual anchors only, macro/dependency/internal callees are not certified covered.',anchors=anchors))
# Mechanically associate the already-proved fixed-dictionary obstruction with
# the emitted retry cell and native advancing-draw/retry source shape; no execution.
entropy=read(sources[6]); theorem=read(sources[9]); boundary=read(sources[10])
assert entropy.count('getrandom::fill(')>=2
assert 'no_retry_then_success' in theorem and 'same_iteration_shape' in theorem
assert 'fixed_dictionary_obstruction' in boundary
body_start=funs.index('  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body\n')
body=funs[body_start:funs.index('/--',body_start)]
assert body.count('getrandom.fill')==1
fill=next(o for o in ops if o['alias']=='getrandom.fill')
assert fill['op']=='op129'
assert 'Slice Std.U8' in fill['signature']
write('checked-obstruction.json',dict(
    class_='Source/interface obstruction; existing Lean theorem cited, not freshly compiled here',
    source_shape='Native generator can consume a zero first iteration then nonzero seeds at a later iteration. Fixed pure dictionary repeats the same zero-buffer call across iterations.',
    extracted_call_sites=[s for s in fill['textual_call_sites'] if 'generate_for_mask_nonce' in s['enclosing_declaration']],
    existing_theorem='R1Z.ProverRwEntropyIteration.no_retry_then_success',
    existing_entry_theorem='R1Z.PV_RunJoin_Source.fixed_dictionary_obstruction',
    statement='For all fixed ExternalFuns dictionaries, an in-bound emitted entropy iteration cannot return cont followed by done(.Ok secret) for the same nonce and limit.',
    limitation='Does not refute syntax-directed effect re-extraction. Does not assert an admitted deployed privacy counterexample. It refutes using the unchanged fixed dictionary as a general per-call native world.'))
write('checks.json',dict(status='ACCEPTANCE PREFLIGHT FAILED',baseline=BASE,
      a='FAIL: executable extraction absent from selected artifact and tracked provenance scan',
      b='FAIL: incomplete executable effect coverage; no installed writer operations',
      c='NOT IMPLEMENTED',d='Existing trust/obligations named; no T additions',
      e='0 of 19 OPEN fields defined; 7 intended, 12 retained',
      v='No joint source-associated witness supplied; no skeleton credit claimed',
      rows_removed=[],rows_added=[],premises_changed=[],
      lean_attempts=0,native_attempts=0,kani_attempts=0,
      elapsed_seconds=time.monotonic()-started))
print('Audit complete: 262 external operations inventoried; executable extraction acceptance gate fails.')
