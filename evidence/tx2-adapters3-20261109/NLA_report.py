from pathlib import Path
import json,lzma,re,hashlib,subprocess
E=Path(__file__).resolve().parent
all_rows=[json.loads(l) for l in (E/'NLA_ATTEMPTS.jsonl').read_text().splitlines()]
rows=[r for r in all_rows if r['kind']!='prelaunch']
fsout=0;pre=[]
for r in rows:
 a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 disk=json.loads((E/(a+'-disk-0.json')).read_text());assert disk['allowed'] and disk['free_bytes']>=40_000_000_000;pre.append(disk['free_bytes'])
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
 s=lzma.decompress((E/a/'time.log.xz').read_bytes()).decode();m=re.search(r'File system outputs: (\d+)',s)
 if m:fsout+=int(m[1])*512
peak=max(int(r['peak_rss_kib']) for r in rows)
assert fsout<25_000_000_000
export=json.loads((E/'NLA_EXPORT.json').read_text())
resources=dict(kani_used=70,kani_budget=70,formal_support_used=19,formal_support_budget=80,measured_scope_receipts=88,formal_support_measured=18,prelaunch_unmeasured='NLA_L001_PRELAUNCH.json',extraction_used=0,extraction_budget=0,peak_rss_kib=peak,swaps=0,sum_filesystem_outputs_bytes=fsout,workspace_bytes=export['workspace_bytes'],workspace_limit_bytes=25_000_000_000,minimum_prescope_free_bytes=min(pre),final_free_bytes=export['free_bytes'],wall_seconds=sum(r['wall_seconds'] for r in rows),caps_verified=True,timeout_increase=False,memory_cap_increase=False,cache_retained=True)
(E/'NLA_RESOURCES.json').write_text(json.dumps(resources,indent=1)+'\n')
rawlog=lzma.decompress((E/'NLA_L022/stdout.log.xz').read_bytes()).decode();raw=[json.loads(l.split('NEP_RESULT ',1)[1]) for l in rawlog.splitlines() if l.startswith('NEP_RESULT ')]
assert len(raw)==108 and all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw)
fixtures=lzma.decompress((E/'NLA_L021/stdout.log.xz').read_bytes()).decode();fx=[json.loads(l.split('NEP_RESULT ',1)[1]) for l in fixtures.splitlines() if l.startswith('NEP_RESULT ')]
assert len(fx)==8 and all(x['equal'] for x in fx)
assert sum(bool(x['walked_axioms']) for x in fx)==4
pins=json.loads(lzma.decompress((E/'NLA_CLOSURE_PINS.json.xz').read_bytes()));assert pins['scan_pass'] and not pins['mismatches']
scan=lzma.decompress((E/'NLA_L025/stdout.log.xz').read_bytes()).decode();assert 'NFN_SCAN_ZERO_DANGLING' in scan
for a in ['NLA_L020','NLA_L021','NLA_L022','NLA_L023','NLA_L024','NLA_L025','NLA_L026','NLA_L027']:
 assert next(r for r in rows if r['attempt']==a)['exit_status']==0
obj=dict(status='PASS_LOCAL_SUPPORT_GATE',headline='AspisR1.RPx_Deployed.deployed',combined_audits_used=1,combined_audits_limit=2,combined_import='NLA_L020',raw_ax2={'attempt':'NLA_L022','roots':108,'all_equal_collectAxioms':True,'allowed_axioms':['propext','Classical.choice','Quot.sound']},fixtures={'attempt':'NLA_L021','same_binary':True,'checks':8,'planted_axioms_detected':4,'mutations_clear':4,'reason_for_replay':'new private workspace and LEAN_PATH selection; same pinned walker binary'},NFX={'attempt':'NLA_L025','exit':0,'modules':pins['modules'],'dangling':0,'conflicting_owners':0,'import_mismatches':0},pins={'attempt':'NLA_L026','predecessor_files':pins['predecessor_files'],'mismatches':0,'manifest':'NLA_CLOSURE_PINS.json.xz'},validation='NLA_VALIDATION.json',resources='NLA_RESOURCES.json',hypotheses='NLA_HYPOTHESES.json',credited_rows=0,proposed_rows=0,owned_rows={'TX2:217':'OPEN','TX2:234':'OPEN'},security_target_established=False)
(E/'NLA_AUDIT.json').write_text(json.dumps(obj,indent=1)+'\n')
(E/'NLA_FROZEN.json').write_text(json.dumps(dict(crates_program_verifier_lock='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',pool_source='b936275465',default_elf='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet_elf='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',pool_elf='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc',ELF_pins='inherited, not rebuilt or reverified',shipped_files_changed=False,ELF_rebuild_trigger=False,trust_changes=[],transport_reclassification='Existing P6/D188 option-A only, not removal',RuntimeCpiReadonlyEntry7_used=False,keys_wallets_funds_authorities_touched=False),indent=1)+'\n')
print(json.dumps(dict(audit=obj['status'],raw_roots=108,modules=pins['modules'],peak_rss_kib=peak,filesystem_output_bytes=fsout,formal_support=19,native=70,export_bytes=export['export_bytes'])))
