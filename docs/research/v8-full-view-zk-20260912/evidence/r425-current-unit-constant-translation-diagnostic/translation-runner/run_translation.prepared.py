#!/usr/bin/env python3
"""Prepared-only R419 translation runner; launch is gated by lead delta evidence."""
import argparse, datetime, hashlib, json, pathlib, shlex, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
WORKTREE = pathlib.Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
HOST = 'dombarker@100.108.41.90'
SSH_OPTS = ['-o', 'BatchMode=yes', '-o', 'StrictHostKeyChecking=no', '-o', 'UserKnownHostsFile=/dev/null']
CANDIDATE = WORKTREE / '.r21-scratch/r419-try-fold-equality-elimination/runs/aspis-r419-candidate-1790967913444473000/candidate.llbc'
BASELINE = WORKTREE / 'docs/research/v8-full-view-zk-20260912/evidence/r405-generic-batch-translation-frontier/provenance/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc'
CANDIDATE_REMOTE = '/home/dombarker/project-offloads/aspis-r419-native-20261002-a/aspis-r419-candidate-1790967913444473000/candidate.llbc'
BASELINE_REMOTE = '/home/dombarker/project-offloads/aspis-r396-private-batch-unmonomorphized-20261002-a/R396PrivateBatchUnmonomorphized.llbc'
BINARY = '/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a/UNRESOLVED_AENEAS_EXECUTABLE'
WORKROOT = '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
REMOTE_OUTPUT = '/home/dombarker/project-offloads/aspis-r425-unit-translation-20261002-a'
CANDIDATE_SHA = '7f82eaabe855e89d735b21f9af5f6a983abea6b2f4d93d4b8bae747abd2829e2'
BASELINE_SHA = '399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
CANDIDATE_RECEIPT_SHA = '67acbca4d5080c32ea5b2c47240670617908a91d58f1af08bb1e650c300c0ef5'
BINARY_SHA = 'R425_BINARY_SHA_UNRESOLVED'
CANDIDATE_SOURCE_REVISION = '3f22e765d32b16d016f4ff603d599ea72838c37a'
NAMESPACE = 'AspisR425UnitConstant'
ROOT_RUST = 'aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch'
ROOT_SPAN = ((61, 0), (69, 1))
CAPS = {'MemoryHigh': '5G', 'MemoryMax': '7G', 'MemorySwapMax': '0', 'TasksMax': 128}
REVIEW = HERE / 'lead-translation-approval.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def rust_name(row):
    parts = []
    for item in row.get('item_meta', {}).get('name') or []:
        if 'Ident' in item:
            parts.append(item['Ident'][0])
        elif 'Impl' in item:
            parts.append('{impl}')
        elif 'Instantiated' in item:
            parts.append('{instantiated}')
    return '::'.join(parts)


def root_row(data):
    matches = []
    for row in data['translated']['fun_decls']:
        if not isinstance(row, dict) or rust_name(row) != ROOT_RUST:
            continue
        span = row.get('item_meta', {}).get('span', {}).get('data', {})
        beg, end = span.get('beg', {}), span.get('end', {})
        if ((beg.get('line'), beg.get('col')), (end.get('line'), end.get('col'))) == ROOT_SPAN:
            matches.append(row)
    assert len(matches) == 1, f'expected one full-batch root, got {len(matches)}'
    return matches[0]


def inventory(path, expected_sha):
    assert sha(path) == expected_sha, f'input SHA mismatch: {path}'
    data = json.loads(path.read_text())
    assert data.get('has_errors') is False
    tr = data['translated']
    root = root_row(data)
    assert tr['options']['start_from'] == ['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch']
    counts = {
        'type_rows': len(tr['type_decls']), 'function_rows': len(tr['fun_decls']),
        'nonnull_functions': sum(isinstance(x, dict) for x in tr['fun_decls']),
        'global_rows': len(tr['global_decls']), 'trait_rows': len(tr['trait_decls']),
        'trait_impl_rows': len(tr['trait_impls']), 'ordered_decls': len(tr['ordered_decls']),
    }
    assert counts == {'type_rows': 63, 'function_rows': 243, 'nonnull_functions': 88,
                      'global_rows': 33, 'trait_rows': 32, 'trait_impl_rows': 47,
                      'ordered_decls': 161}, counts
    assert isinstance(root.get('body'), dict) and 'Structured' in root['body']
    assert root['item_meta'].get('opacity') == 'Transparent'
    assert root['item_meta'].get('is_local') is True
    target = []
    for row in tr['fun_decls']:
        if not isinstance(row, dict) or rust_name(row) != 'core::iter::traits::iterator::Iterator::try_fold':
            continue
        span = row.get('item_meta', {}).get('span', {}).get('data', {})
        beg, end = span.get('beg', {}), span.get('end', {})
        if (beg.get('line'), beg.get('col'), end.get('line'), end.get('col')) == (2486, 4, 2490, 35):
            target.append(row)
    assert len(target) == 1 and target[0].get('body') not in (None, 'Opaque')
    return {
        'sha256': expected_sha, 'has_errors': False, 'counts': counts,
        'start_from': tr['options']['start_from'], 'include': tr['options']['include'],
        'root': {'def_id': root['def_id'], 'name': rust_name(root), 'span': root['item_meta']['span'],
                 'body_kind': 'Structured', 'body_sha256': digest(root['body']),
                 'item_meta_sha256': digest(root['item_meta'])},
        'ordered_decls_sha256': digest(tr['ordered_decls']),
        'try_fold': {'def_id': target[0]['def_id'], 'name': rust_name(target[0]),
                     'source_span': target[0]['item_meta']['span'], 'body_present': True},
    }


def local_gate():
    assert sha(CANDIDATE) == CANDIDATE_SHA
    baseline = inventory(BASELINE, BASELINE_SHA)
    candidate = inventory(CANDIDATE, CANDIDATE_SHA)
    assert baseline['counts'] == candidate['counts']
    assert baseline['ordered_decls_sha256'] == candidate['ordered_decls_sha256']
    assert baseline['root']['item_meta_sha256'] == candidate['root']['item_meta_sha256']
    # Root body's structure is present in both; typed call arguments changed in
    # the transformed candidate, so equality requires the missing reviewed delta.
    review = None
    if REVIEW.is_file():
        review = json.loads(REVIEW.read_text())
    return {'candidate': candidate, 'baseline': baseline,
            'root_body_hash_equal': baseline['root']['body_sha256'] == candidate['root']['body_sha256'],
            'expected_delta_review_path': str(REVIEW), 'expected_delta_review': review,
            'candidate_transform_source_revision': CANDIDATE_SOURCE_REVISION,
            'candidate_receipt_sha256': CANDIDATE_RECEIPT_SHA,
            'binary_sha256': BINARY_SHA, 'caps': CAPS}


REMOTE = r'''import datetime,hashlib,json,pathlib,subprocess,sys,re,os
facts=json.loads(sys.argv[1]);src=pathlib.Path(facts['candidate_remote']);base=pathlib.Path(facts['baseline_remote']);binary=pathlib.Path(facts['binary']);out=pathlib.Path(facts['remote_output']);work=pathlib.Path(facts['workroot'])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not out.exists(),f'fresh output path already exists: {out}'
assert sha(src)==facts['candidate_sha'],sha(src);assert sha(base)==facts['baseline_sha'],sha(base);assert sha(binary)==facts['binary_sha'],sha(binary)
for p,expected in ((src,facts['candidate_sha']),(base,facts['baseline_sha'])):
 d=json.loads(p.read_text());assert d.get('has_errors') is False;tr=d['translated'];assert tr['options']['start_from']==['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch'];assert len(tr['ordered_decls'])==161
# Aggregate gate: preserve current host evidence and require spare reserve before entering the capped scope.
mem={k:v for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
avail=int(mem['MemAvailable'].split()[0])*1024;cap=7*1024**3;reserve=24*1024**3;assert avail-cap>=reserve,{'meminfo':mem,'cap':cap,'reserve':reserve}
heavy=[]
for p in pathlib.Path('/proc').iterdir():
 if p.name.isdigit():
  try:
   comm=(p/'comm').read_text().strip()
   if comm in ('cargo','rustc','rustc_driver','charon','aeneas','lean','lean4'):heavy.append({'pid':p.name,'comm':comm})
  except (OSError,FileNotFoundError):pass
assert not heavy,heavy
out.mkdir(parents=True)
pre={'candidate_sha256':sha(src),'baseline_sha256':sha(base),'binary_sha256':sha(binary),'source_revision':'@CANDIDATE_REV@','translation_launch_revision':'@LAUNCH_REV@','meminfo_before':mem,'candidate_memory_max_bytes':cap,'reserve_bytes':reserve,'heavy_processes':heavy,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}}
(out/'host-reservation-before.json').write_text(json.dumps(pre,indent=2))
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','@NAMESPACE@','-dest',str(out/'generated'),'-subdir','@NAMESPACE@','-split-files','-emit-json',str(src)]
(out/'translate-command.json').write_text(json.dumps({'command':cmd,'candidate_sha256':sha(src),'baseline_sha256':sha(base),'binary_sha256':sha(binary),'source_revision':'@CANDIDATE_REV@','translation_launch_revision':'@LAUNCH_REV@','namespace':'@NAMESPACE@','flags':['-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','@NAMESPACE@','-dest','<fresh>/generated','-subdir','@NAMESPACE@','-split-files','-emit-json']},indent=2))
with (out/'translate.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
gen=out/'generated';manifest=gen/'translation.json';md=json.loads(manifest.read_text()) if manifest.is_file() else {};functions=md.get('functions',[])
rootrows=[f for f in functions if f.get('rust_name')=='@ROOT_RUST@'];warnings=[x for x in (out/'translate.log').read_text(errors='replace').splitlines() if '[Warn' in x]
holes={}
for fname in ('FunsExternal_Template.lean','TypesExternal_Template.lean'):
 p=gen/'@NAMESPACE@'/fname
 holes[fname]=re.findall(r'^axiom\s+([^\s(]+)',p.read_text(errors='replace'),re.M) if p.is_file() else []
files={str(p.relative_to(out)):sha(p) for p in sorted(gen.rglob('*')) if p.is_file()} if gen.is_dir() else {}
result={'translator_exit_status':r.returncode,'generated_dir_exists':gen.is_dir(),'translation_json_exists':manifest.is_file(),'manifest_function_entries':len(functions),'batch_root_matches':len(rootrows),'batch_root_entry':rootrows[0] if len(rootrows)==1 else None,'external_template_axiom_holes':holes,'warnings':warnings,'generated_file_sha256':files,'input_has_errors':False,'input_ordered_decls':161,'source_gate_boundary':'R419 candidate is the only input; root body was inventoried before launch and expected-delta review was required locally.'}
(out/'translation-result.json').write_text(json.dumps(result,indent=2))
after={'meminfo_after':{k:v for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}}
(out/'host-reservation-after.json').write_text(json.dumps(after,indent=2));(out/'result.json').write_text(json.dumps({'translator_exit_status':r.returncode,'candidate_sha256':sha(src),'baseline_sha256':sha(base),'binary_sha256':sha(binary),'candidate_transform_source_revision':'@CANDIDATE_REV@','translation_launch_revision':'@LAUNCH_REV@','translation_result':result,'scope':'Translation inventory only; no Lean compile, template fill, proof, or source claim.'},indent=2))
print((out/'translate.log').read_text()[-12000:]);print('R424_TRANSLATE_EXIT',r.returncode);raise SystemExit(r.returncode)
'''


def build_remote(facts, launch_revision):
    content = REMOTE
    replacements = {
        '@CANDIDATE_REV@': CANDIDATE_SOURCE_REVISION,
        '@LAUNCH_REV@': launch_revision,
        '@NAMESPACE@': NAMESPACE,
        '@ROOT_RUST@': ROOT_RUST,
    }
    for old, new in replacements.items():
        content = content.replace(old, new)
    return content


def approved_review(gate):
    assert REVIEW.is_file(), f'blocked: lead expected-delta review is not present at {REVIEW}'
    r = json.loads(REVIEW.read_text())
    assert r.get('review_status') == 'APPROVED_BY_LEAD', r
    assert r.get('candidate_sha256') == CANDIDATE_SHA
    assert r.get('baseline_sha256') == BASELINE_SHA
    assert r.get('candidate_root_body_sha256') == gate['candidate']['root']['body_sha256']
    assert r.get('baseline_ordered_decls_sha256') == gate['baseline']['ordered_decls_sha256']
    evidence_path = r.get('independent_evidence_path')
    assert isinstance(evidence_path, str) and evidence_path, r
    evidence_file = pathlib.Path(evidence_path)
    assert evidence_file.is_file(), f'approved delta evidence is missing: {evidence_file}'
    assert r.get('independent_evidence_sha256') == sha(evidence_file), r
    return r


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--launch', action='store_true', help='requires separate lead-approved expected-delta evidence')
    args = parser.parse_args()
    gate = local_gate()
    if not args.launch:
        print(json.dumps({'status': 'PREPARED_ONLY_NOT_LAUNCHED', 'local_input_gate': gate,
                          'launch_enabled': False, 'required_external_review': str(REVIEW),
                          'next_action': 'Lead must provide and review exact expected-delta evidence before --launch can pass.'}, indent=2))
        return 0
    assert BINARY_SHA != 'R425_BINARY_SHA_UNRESOLVED', 'blocked: fill the R425 binary path and SHA only after the reviewed R425 main build'
    review = approved_review(gate)
    assert review.get('translator_binary_sha256') == BINARY_SHA, review
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=WORKTREE, text=True).strip()
    assert len(revision) == 40
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    hist = HERE / 'launch-history' / f'{revision[:12]}-{stamp}'
    hist.mkdir(parents=True, exist_ok=False)
    facts = {'candidate_remote': CANDIDATE_REMOTE, 'baseline_remote': BASELINE_REMOTE,
             'binary': BINARY, 'remote_output': REMOTE_OUTPUT, 'workroot': WORKROOT,
             'candidate_sha': CANDIDATE_SHA, 'baseline_sha': BASELINE_SHA,
             'binary_sha': BINARY_SHA}
    remote = build_remote(facts, revision)
    (hist / 'remote_translate.py').write_text(remote)
    command = ['systemd-run', '--user', '--wait', '--collect', '--pipe',
               '--unit=aspis-r425-unit-translation',
               '--working-directory=' + WORKROOT,
               '-p', 'MemoryHigh=5G', '-p', 'MemoryMax=7G',
               '-p', 'MemorySwapMax=0', '-p', 'TasksMax=128',
               'python3', '-c', remote, json.dumps(facts, separators=(',', ':'))]
    ssh = ['ssh', *SSH_OPTS, HOST, shlex.join(command)]
    receipt = {'candidate_transform_source_revision': CANDIDATE_SOURCE_REVISION,
               'translation_launch_revision': revision, 'started_at_utc': stamp,
               'candidate_sha256': CANDIDATE_SHA, 'baseline_sha256': BASELINE_SHA,
               'candidate_receipt_sha256': CANDIDATE_RECEIPT_SHA, 'binary_sha256': BINARY_SHA,
               'expected_delta_review': review, 'local_gate': gate,
               'caps': CAPS, 'systemd_argv': command, 'ssh_argv': ssh,
               'remote_payload_sha256': hashlib.sha256(remote.encode()).hexdigest()}
    (hist / 'launch.json').write_text(json.dumps(receipt, indent=2) + '\n')
    with (hist / 'launch.log').open('w') as out:
        run = subprocess.run(ssh, stdout=out, stderr=subprocess.STDOUT)
    receipt['launcher_exit_status'] = run.returncode
    output = HERE / 'output' / f'{revision[:12]}-{stamp}'
    output.mkdir(parents=True, exist_ok=False)
    fetch = subprocess.run(['scp', '-r', *SSH_OPTS, HOST + ':' + REMOTE_OUTPUT + '/.', str(output)])
    receipt['scp_exit_status'] = fetch.returncode
    receipt['local_output'] = str(output)
    (hist / 'launch-result.json').write_text(json.dumps(receipt, indent=2) + '\n')
    raise SystemExit(run.returncode if run.returncode else fetch.returncode)


if __name__ == '__main__':
    raise SystemExit(main())
