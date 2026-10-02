import hashlib,json,pathlib,subprocess,sys,time,re
root=pathlib.Path('/home/dombarker/project-offloads/aspis-r424-concrete-associated-types-candidate-20261002-a')
audit=root/'candidate-audit/r424-fixture-execution-v1'
exe=root/'src/_build/default/ConcreteAssociatedTypesFixture.exe'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs=json.loads(pathlib.Path('/tmp/aspis-r424-fixture-build-v3-inputs.json').read_text())
assert not audit.exists();audit.mkdir(parents=True)
assert sha(exe)=='a8f7fec43708590d256b7a4f313bb63814f9075deb77ef064768ba13318c055f'
for rel,h in inputs['source_sha256'].items(): assert sha(root/rel)==h,rel
fixture=root/'source-fixtures/R396PrivateBatchUnmonomorphized.llbc'
assert sha(fixture)=='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
command=['/usr/bin/time','-v',str(exe),str(fixture)]
receipt={**inputs,'target':'ConcreteAssociatedTypesFixture.exe against exact frozen R396 input','exe_sha256':sha(exe),'argv':command,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'print_axioms':'Not applicable: finite OCaml AST fixtures, no Lean theorem.','proved_boundary':'Finite actual impl24 and synthetic type/capture/rejection checks only; no actual callback execution or compiler/security theorem.','first_remaining_proposition':'Build and consume changed Aeneas translator, then prove full actual callback chronology without assumptions.'}
(audit/'command.json').write_text(json.dumps(receipt,indent=2)+'\n')
start=time.monotonic()
with (audit/'raw.log').open('w') as f:
 r=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT)
s=(audit/'raw.log').read_text();m=re.search(r'R424 fixture assertions passed: (\d+)',s)
receipt.update({'exit_status':r.returncode,'wrapper_wall_seconds':time.monotonic()-start,'assertions_passed':int(m.group(1)) if m else None,'all_checks_passed':r.returncode==0 and m is not None and int(m.group(1))==14,'raw_log_sha256':sha(audit/'raw.log')})
(audit/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(s);print(json.dumps(receipt,indent=2));sys.exit(0 if receipt['all_checks_passed'] else r.returncode or 1)
