"""Fail-closed Stage 1 provenance audit. No compilation or graph inference."""
import json, pathlib, hashlib, subprocess, re, lzma
E=pathlib.Path(__file__).resolve().parent; R=E.parents[1]; N=R/'evidence/pool-inventory2-20261109'
sha=lambda b:hashlib.sha256(b).hexdigest()
load=lambda p:json.loads(p.read_text())
d=load(N/'NKZ_DEPLOYED_BUILD.json'); b=d['pool_build']; h=load(E/'PCH_HOST_AUDIT.json')
expected='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc'
inputs={}
for prefix, names in [(N,['NKZ_DEPLOYED_BUILD.json','NKZ_NATIVE_SBF.json','NKZ_HANDOFF.md','NKZ_INVENTORY.json','NKZ_TRACTABILITY.json','NKZ_GRAPH.json.xz']), (R/'evidence/inv-repair-20261104',['NGB_HANDOFF.md','NGB_mir.py','NGB_EXCLUDED.json','NGB_MIR_EDGES.json']), (R/'evidence/pool-borrow-20261107',['NIK_CENSUS.json']), (R/'evidence/pc-helpers1-20261110',['PCB_REACH.json','PCB_REACH.md']), (R/'evidence/pool-ledger1-20261110',['PCE_LEDGER.json.xz']), (R/'evidence/pc-helpers2-20261110',['PCG_LEDGER_DELTA.json'])]:
 for name in names:
  p=prefix/name;inputs[str(p.relative_to(R))]={'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
artifacts=[]; commands={}
for crate in ['aspis_core','aspis_statement','aspis_pool']:
 p=N/f'NKZ_{crate}.command.json'; cmd=load(p); inputs[str(p.relative_to(R))]={'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
 commands[crate]={'argv':cmd,'compiler':cmd[0],'target':cmd[cmd.index('--target')+1],'features':sorted(x[9:-1] for i,x in enumerate(cmd) if i and cmd[i-1]=='--cfg' and x.startswith('feature="'))}
 for ext in ['mir.xz','ll.xz','mono.txt']:
  p=N/f'NKZ_{crate}.{ext}'; raw=p.read_bytes(); un=lzma.decompress(raw) if ext.endswith('.xz') else raw
  artifacts.append({'path':str(p.relative_to(R)),'sha256':sha(raw),'bytes':len(raw),'uncompressed_sha256':sha(un),'uncompressed_bytes':len(un),'authority_admitted':False})
checks=[]
for c in d['compiler_input_checks']:
 p=c['path']; revision=d['frozen_revision'] if p.startswith('programs/aspis-pool/') else d['crates_revision']
 raw=subprocess.check_output(['git','show',revision+':'+p],cwd=R)
 checks.append({'path':p,'revision':revision,'sha256':sha(raw),'expected':c['expected'],'matches':sha(raw)==c['expected']})
lock=subprocess.check_output(['git','show',d['crates_revision']+':Cargo.lock'],cwd=R)
assert all(c['matches'] for c in checks)
assert sha(lock)==d['lock_sha256']==b['lock_before']==b['lock_after']
elf_match=any(a['sha256']==expected for a in b['artifacts'])
assert elf_match
sbf=h['tools']['retained_sbf']; native=h['tools']['required_native']
assert sbf['sha256']==next(v for k,v in b['tool_pins'].items() if k.endswith('/rustc'))
a={'schema':'PCH-AUTHORITY-1','status':'BLOCKED_TOOLCHAIN_CONTRADICTION','admitted':False,'required':{'compiler':'rustc 1.94.1','target':'sbpf-solana-solana','elf_sha256':expected,'pool_revision':d['frozen_revision'],'crates_revision':d['crates_revision'],'lock_sha256':sha(lock)},'retained_elf_hash_comparison':{'matches':elf_match,'artifacts':b['artifacts'],'receipt': 'evidence/pool-inventory2-20261109/NKZ_DEPLOYED_BUILD.json#pool_build','fresh_ELF_hash':None,'receipt_reused_only_for_its_actual_inputs':True},'toolchain_audit':h,'compiler_commands':commands,'source_checks':checks,'input_pins':inputs,'artifacts':artifacts,'resolved_packages_as_reported_by_receipt':b['resolved_packages'],'metadata_feature_warning':'resolved_packages is metadata output; actual per-crate SBF cfg is separately recorded in compiler_commands. Do not equate host metadata and emitted SBF features.','retained_build_receipt':b,'reason':'Receipt native_rustc_version is rustc 1.94.1, but the actual Pool compiler command selects 1.89.0-sbpf-solana-v1.52; the pinned binary reports rustc 1.89.0-dev. Installed 1.94.1 target-list lacks sbpf-solana-solana. No retained receipt here establishes the requested compiler/target/ELF conjunction. Rebuilding with 1.89 would not satisfy (c-g)(2)(a); choosing a compiler/target specification or changing the ruling is outside this job.','stage2_permitted':False,'stage3_permitted':False,'stage4_permitted':False,'no_exclusion_recorded':True,'axioms':'N/A: no Lean theorem or proof scope','budget':{'Kani':0,'Lean':0,'build_scopes':0,'host_script_audit_scopes':1}}
(E/'PCH_AUTHORITY.json').write_text(json.dumps(a,indent=2)+'\n')
time=(E/'PCH_A001.time').read_text(); rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',time)
receipt={'attempt':'PCH_A001','target':'PCH_host_audit.py: compiler identity and target-list','exit_status':0,'admission_exit_status':0,'admission_allowed':load(E/'PCH_A001-reservation.json')['allowed'],'wall_seconds':0.12,'peak_rss_kib':int(rss[1]),'swaps':0,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'source_sha256':sha((E/'PCH_host_audit.py').read_bytes()),'input_fingerprint':sha(json.dumps(inputs,sort_keys=True).encode()),'limits':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64},'disk_free_before_bytes':h['disk_free_before_bytes'],'print_axioms':'N/A: no theorem','scope_kind':'script/audit','command':'systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 /usr/bin/time -v -o PCH_A001.time python3 PCH_host_audit.py','outcome':'Audit succeeded; authority gate BLOCKED','build_scopes':0}
(E/'PCH_ATTEMPTS.jsonl').write_text(json.dumps(receipt)+'\n')
print('PCH Stage 1: retained ELF matches; required compiler/target authority blocked')
