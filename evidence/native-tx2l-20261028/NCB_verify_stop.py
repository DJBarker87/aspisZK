from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent
rows=[json.loads(p.read_text()) for p in sorted(E.glob('NCB_[KL][0-9][0-9][0-9]/receipt.json'))]
(E/'NCB_ATTEMPTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
lean=[r for r in rows if r['kind']=='lean'];kani=[r for r in rows if r['kind']=='kani']
assert len(lean)==20 and len(kani)==55
for r in rows:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},r['attempt']
 assert int(r['swaps'])==0,r['attempt']
 if r['kind']=='kani':
  a=r['attempt'];g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen'] and not g['edge_errors'] and not g['new_package_tuples']
  assert (E/(a+'-lock-before.log')).read_text().strip()==(E/(a+'-lock-after.log')).read_text().strip()=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
valid=[]
for p in sorted(Path('lean').glob('NCB_*.lean')):
 src=p.read_bytes();h=hashlib.sha256(src).hexdigest()
 matching=[r for r in lean if r['exit_status']==0 and r['module']==p.stem and h in r['source_hashes'].values()]
 assert matching,('no passing exact snapshot',str(p))
 r=matching[-1];assert r['print_axioms']
 assert not any('sorryAx' in x for x in r['print_axioms'])
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',src.decode()),p
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',src.decode()),p
 valid.append({'module':p.stem,'source_sha256':h,'attempt':r['attempt'],'axioms':r['print_axioms']})
initial='1d36cda6864ff826d993c6b60ff4f974faa43d0f'
changed=subprocess.check_output(['git','diff','--name-only',initial],text=True).splitlines()
assert all(n.startswith('lean/NCB_') or n.startswith('evidence/native-tx2l-20261028/') for n in changed),changed
assert not subprocess.check_output(['git','diff',initial,'--','crates','programs'],text=True)
freeze=json.loads((E.parent/'native-tx2i-20261028/NBS_REPOSITORY_SOURCE_CHECK.json').read_text())
errors=[]
# Check the frozen repository corpus; retain the three previously declared tools-only differences.
manifest=json.loads((E.parent/'native-tx2h-20261028/NBQ_SCRATCH_MANIFEST.json').read_text())
overrides={r['path']:r['inherited_head_sha256'] for r in freeze['inherited_non_target_differences']}
for name,pin in manifest.items():
 p=Path(name);expected=overrides.get(name,pin)
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:errors.append(name)
assert not errors,errors
end=json.loads((E/'NCB_END.json').read_text());start=json.loads((E/'NCB_CACHE_IMPORT.json').read_text());lib=json.loads((E/'NCB_LIBRARY_PIN.json').read_text())
assert all(end['cache'].get(k)==v for k,v in start.items()),'inherited cache drift'
assert end['library']==lib,'Aeneas library drift'
assert not end['source']['errors'] and not end['owned_active_scopes']
report={'status':'focused results only; all units OPEN; infrastructure stop','revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'lean_attempts':len(lean),'kani_runs':len(kani),'lean_exit_zero':sum(r['exit_status']==0 for r in lean),'kani_exit_zero':sum(r['exit_status']==0 for r in kani),'expected_negative_controls':['NCB_K001','NCB_K012','NCB_K014','NCB_K046'],'rejected_codegen':['NCB_K004','NCB_K005','NCB_K006'],'rejected_timeouts':['NCB_K003','NCB_K015','NCB_K016'],'validated_modules':valid,'all_caps_verified':True,'all_swaps_zero':True,'source_scope_only_owned_files':True,'repository_crates_programs_unchanged':True,'imported_cache_pins_unchanged':len(start),'aeneas_library_pins_unchanged':len(lib),'source_check':end['source'],'wall_seconds_sum':sum(r['wall_seconds'] for r in rows),'peak_rss_kib':max(int(r['peak_rss_kib']) for r in rows),'full_coimport_audit':'UNRUN due infrastructure stop; each new theorem has its own successful printed standard-axiom audit','release_replay':'not run; no shipped source/artifact changed; no release claim'}
(E/'NCB_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['validated_modules','source_check']}))
