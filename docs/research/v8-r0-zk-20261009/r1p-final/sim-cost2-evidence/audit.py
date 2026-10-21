"""Audit focused receipts and current host hashes; never rerun a Lean target."""
import hashlib, json, pathlib, re, subprocess
p = pathlib.Path(__file__).resolve().parent
root = p.parents[1]
base = 'facfc1092'
receipts = [json.loads(f.read_text()) for f in sorted(p.glob('receipt-*.json'))]
accepted = [r for r in receipts if r['exit'] == 0]
assert len({r['attempt'] for r in receipts}) == len(receipts)
assert all(9540 <= r['attempt'] <= 9599 for r in receipts)
assert all(r['dependencies_stable'] for r in receipts)
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {}
count = 0
for r in accepted:
    src = root/'lean'/f"{r['module']}.lean"
    assert sha(src) == r['source_sha256']
    rel = src.relative_to(pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'], text=True).strip()))
    assert subprocess.run(['git','cat-file','-e',f'{base}:{rel}'], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode != 0
    text = src.read_text()
    assert not re.search(r'^\s*(axiom\b|.*\bsorry\b|.*\badmit\b|.*\bnative_decide\b)', text, re.M)
    assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)', text)
    theorems = re.findall(r'^theorem (\w+)', text, re.M)
    assert len(r['axioms']) == len(theorems)
    count += len(theorems)
    for line in r['axioms']:
        m = re.search(r'depends on axioms: \[([^]]*)\]', line)
        if m:
            assert set(map(str.strip, m[1].split(','))) <= allowed
        else:
            assert 'does not depend on any axioms' in line
    expected[f"sources/{r['module']}.lean"] = r['source_sha256']
    expected[f"objects/{r['module']}.olean"] = r['object']['sha256']
    for d in r['dependencies']:
        for sub, ext, key in [('sources','lean','source_sha256'), ('objects','olean','object_sha256')]:
            name = f"{sub}/{d['module']}.{ext}"
            assert name not in expected or expected[name] == d[key]
            expected[name] = d[key]
remote = 'import hashlib,json,pathlib\np=pathlib.Path("/home/dombarker/project-offloads/aspis-joint-20261019")\n'
remote += 'expected=' + repr(expected) + '\n'
remote += 'print(json.dumps({k:hashlib.sha256((p/k).read_bytes()).hexdigest()==v for k,v in expected.items()}))\n'
checked = json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'], input=remote, text=True))
assert all(checked.values())
diff = subprocess.check_output(['git','diff','--name-status',base,'--',str(root/'lean')],text=True)
assert all(l.startswith('A\t') for l in diff.splitlines())
result = dict(status='pass', base=base, audited_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
    accepted_modules=[r['module'] for r in accepted], accepted_attempts=[r['attempt'] for r in accepted],
    failed_attempts=[r['attempt'] for r in receipts if r['exit'] != 0], theorem_audits=count,
    current_host_hash_checks=checked, source_changes_additive_only=True,
    swaps=sum(r['swaps'] for r in receipts),
    accepted_peak_rss_kib=max(r['peak_rss_kib'] for r in accepted),
    release_replay_performed=False, unconditional_efficiency_closure=False,
    obstruction='The actual protocol preparation cannot satisfy Sizes for all unrestricted byte-string adversary queries.',
    stored_table_contracts_proved=True, concrete_preparation_certified=False,
    concrete_field_stages_certified=False, sampler_source_coupling_proved=False,
    truncation_budget_numerics_proved=True)
(p/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='current_host_hash_checks'},indent=2))
