from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).parent
J=lambda n:json.loads((E/n).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
w=J('NDC_WARNINGS.json');assert len(w)==34
assert sum(len(x['diagnostics']) for x in w)==62
for x in w:
 for d in x['diagnostics'].values():assert d['offset']>4096 and d['offset']-4096==d['excess'] and d['frame']>=d['offset']
for mode,j in J('NDC_LINKAGE.json').items():
 assert j['text_equal'] and j['text_sha256']==j['unstripped_text_sha256']
 exact=J('NDC_EXACT_SYMBOLS.json')['pool' if mode=='pool' else 'verifier'];assert len(exact)==62 and not any(exact.values())
 s=(E/('NDC_'+('pool' if mode=='pool' else 'verifier')+'_symbols.txt')).read_text()
 for name in exact:assert name not in s
for mode,j in J('NDC_CALLGRAPH_FINAL.json').items():assert j['e_flags']==0 and not j['unresolved_direct'] and max(j['direct_r10_max_negative_offsets'].values())==4096
rows=J('NDC_TABLE.json');assert len(rows)==102 and len({(r['id'],r['elf']) for r in rows})==102
assert all(not r['present'] and not r['reachable'] and r['classification']=='omitted' for r in rows)
for name,pin in J('NDC_TEXT_PINS.json').items():
 b=lzma.decompress((E/(name+'.xz')).read_bytes());assert len(b)==pin['bytes'] and hashlib.sha256(b).hexdigest()==pin['sha256']
 assert (E/(name+'.sha256')).read_text().split()[0]==pin['sha256']
for path,row in J('NDC_SOURCE_SLICES.json').items():
 b=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path]);assert b.decode()==row['text'] and hashlib.sha256(b).hexdigest()==row['sha256']
assert J('NDC_NATIVE_SOURCE_CHECK.json')['checked']==391 and not J('NDC_NATIVE_SOURCE_CHECK.json')['mismatches']
b=J('NDC_NATIVE_BUILD.json');assert b['exit']==0 and b['lock_before']==b['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
nat=J('NDC_NATIVE_SYMBOLS.json');present={k for v in nat.values() for k,a in v['matches'].items() if a}
assert sum(x['identity'] in present for x in w)==33
assert any('EncodingDomain6encode' in a['text'] for v in J('NDC_NATIVE_GENERIC_HEADERS.json').values() for a in v['headers'])
a=[json.loads(l) for l in (E/'NDC_ATTEMPTS.jsonl').read_text().splitlines()];assert len(a)==10
assert [r['attempt'] for r in a if r['exit_status']!=0]==['NDC_I006','NDC_I010']
for r in a:
 assert r['admission_allowed'] and r['admission_exit']==0 and r['swaps']==0 and r['print_axioms']=='N/A: no Lean'
 assert sha(E/(r['attempt']+'.py'))==r['source_sha256']
 cmd=r['scope_command'];assert all(x in cmd for x in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
 assert J(r['attempt']+'-reservation.json')['allowed'] is True
for p in E.iterdir():assert p.stat().st_size<=20*1024*1024
assert 'NDC_target_native' in J('NDC_CLEANUP.json')['removed_only']
result={'status':'PASS','warned_families':34,'exact_diagnostic_symbols':62,'elf_rows':102,'scope_attempts':10,'successful_scopes':8,'failed_own_input_inspections':2,'kani_runs':0,'lean_runs':0,'sbf_vm_runs':0,'sbf_builds':0,'native_optimized_builds':2,'frozen_native_source_hashes':391,'print_axioms':'N/A: no Lean','checks':'Artifact-text association, diagnostic symbol omission, relocation graph, archive digests, source hashes, native membership, admission/resources, script identity, file limits'}
(E/'NDC_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
