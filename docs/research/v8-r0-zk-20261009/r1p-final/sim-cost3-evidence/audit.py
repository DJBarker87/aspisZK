"""Read-only audit: source signatures, retained receipts, and current host hashes."""
import hashlib, json, pathlib, re, subprocess
E = pathlib.Path(__file__).resolve().parent
R = E.parents[1]
L = R/'lean'
base = '5efd4f378'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipts = [json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
accepted = [r for r in receipts if r['exit'] == 0]
current = {r['module']: r for r in accepted}
assert all(9560 <= r['attempt'] <= 9599 for r in receipts)
assert len({r['attempt'] for r in receipts}) == len(receipts)
assert len({(r['source_sha256'],r['deps_fingerprint']) for r in receipts}) == len(receipts)
assert all(r['dependencies_stable'] and r['swaps'] == 0 for r in receipts)
assert all(r['caps'] == dict(lean_memory_mb=7000,MemoryHigh='5G',MemoryMax='7G',MemorySwapMax=0,TasksMax=128) for r in receipts)
allowed = {'propext','Classical.choice','Quot.sound'}
paths = {}
statements = {}
axiom_count = 0
theorem_count = 0
for module, r in current.items():
    p = L/f'{module}.lean'
    s = p.read_text()
    assert sha(p) == r['source_sha256'], module
    rel = p.relative_to(pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip()))
    assert subprocess.run(['git','cat-file','-e',f'{base}:{rel}'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode != 0
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option (maxRecDepth|maxHeartbeats|pp\.)',s,re.M), module
    names = re.findall(r'^theorem (\w+)',s,re.M)
    theorem_count += len(names)
    for name in names:
        assert f'#print axioms {name}' in s,(module,name)
        assert any(f'.{name}\'' in line for line in r['axioms']),(module,name)
    assert len(re.findall(r'^#print axioms ',s,re.M)) == len(r['axioms']),module
    for line in r['axioms']:
        if 'depends on axioms:' in line:
            assert set(re.search(r'\[([^]]*)\]',line).group(1).replace(' ','').replace('\n','').split(',')) <= allowed,line
        else:
            assert 'does not depend on any axioms' in line,line
    axiom_count += len(r['axioms'])
    declarations = []
    for m in re.finditer(r'^theorem (\w+)',s,re.M):
        end = re.search(r' :=(?: by\b|\n)',s[m.start():])
        assert end,(module,m.group(1))
        declaration = s[m.start():m.start()+end.start()]
        declarations.append(dict(name=m.group(1),statement=declaration,sha256=hashlib.sha256(declaration.encode()).hexdigest()))
    statements[module] = declarations
    paths[f'sources/{module}.lean'] = r['source_sha256']
    paths[f'objects/{module}.olean'] = r['object']['sha256']
    for d in r['dependencies']:
        for sub,ext,key in [('sources','lean','source_sha256'),('objects','olean','object_sha256')]:
            path = f"{sub}/{d['module']}.{ext}"
            assert path not in paths or paths[path] == d[key],path
            paths[path] = d[key]
old = (L/'R1Z/PrivacyR1HeadlineV2.lean').read_text()
new = (L/'R1Z/PrivacyR1HeadlineV2SimProto.lean').read_text()
a = old.index('theorem privacy_headline_v2\n')
b = old.index(' :\n    ZK_FSS',a)
c = old.index(' := by',b)
x = new.index('theorem privacy_headline_v2_sim_proto\n')
y = new.index('\n    (C : Nat)',x)
assert old[a:b].replace('theorem privacy_headline_v2\n','theorem privacy_headline_v2_sim_proto\n') == new[x:y]
assert '('+old[b+3:c].strip()+') ∧\n    ∀' in new
assert 'sim_sizes' not in new and '(C L T : Nat)' not in new
assert 'relativeCoefficient C' in new and '+ 1)^1' in new
signature = dict(original_binders_preserved_verbatim=True,original_privacy_conclusion_preserved_verbatim=True,
    removed_privacy_premises=[],added_endpoint_binders=['C : Nat','sim_preparation : Preparation ... C'],
    discharged_contracts=['protocol table length','stored-key length','all adversary address restrictions removed'],
    unconditional_efficiency_closure=False,statements=statements)
(E/'signatures.json').write_text(json.dumps(signature,indent=2,ensure_ascii=False)+'\n')
remote = 'import hashlib,json,pathlib\np=pathlib.Path("/home/dombarker/project-offloads/aspis-joint-20261019")\n'
remote += 'expected='+repr(paths)+'\n'
remote += 'print(json.dumps({k:hashlib.sha256((p/k).read_bytes()).hexdigest()==v for k,v in expected.items()}))\n'
checks = json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=remote,text=True))
assert all(checks.values())
changes = subprocess.check_output(['git','diff','--name-status',base],text=True).splitlines()
assert all(line.startswith('A\t') for line in changes),changes
result = dict(status='pass',baseline=base,audited_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
    current_modules=list(current),current_accepted_attempts=[r['attempt'] for r in current.values()],
    superseded_accepted_attempts=[r['attempt'] for r in accepted if r not in current.values()],
    failed_attempts=[r['attempt'] for r in receipts if r['exit'] != 0],
    all_attempts=[r['attempt'] for r in receipts],current_axiom_audits=axiom_count,theorem_count=theorem_count,
    all_standard_axioms=True,all_zero_swap=True,accepted_peak_rss_kib=max(r['peak_rss_kib'] for r in accepted),
    source_changes_additive_only=True,exact_original_binders_preserved=True,exact_original_conclusion_preserved=True,
    host_current_hash_checks=checks,relative_replay_proved=True,protocol_stored_contracts_discharged=True,
    prepared_state_lazy_rom_source_law=True,binary_word_batch_source_coupling=True,actual_protocol_tape_source_coupling=True,
    protocol_tape_samples_upper_bound=417792,protocol_tape_draws_upper_bound=3342336,
    concrete_field_stages_certified=False,concrete_preparation_certified=False,lazy_cache_byte_work_certified=False,
    joint_preparation_random_source_factorization=False,truncated_full_experiment_privacy_join=False,
    unconditional_efficiency_closure=False,full_frozen_manifest_replayed=False,
    compiled_example='One fixed callback outputs replicate x.handle 0; no uniform n-only metadata-byte bound over all allowed handles.')
(E/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='host_current_hash_checks'},indent=2))
