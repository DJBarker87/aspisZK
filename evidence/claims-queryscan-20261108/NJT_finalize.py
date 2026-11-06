"""Assemble existing checked evidence; never launches a prover or changes credit."""
from pathlib import Path
import json,hashlib,re,subprocess,lzma,shutil
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads((E/p).read_text())
modules=load('NJT_MODULES.json');receipts=[]
for pattern in ['NJT_L[0-9][0-9][0-9]/receipt.json','NJT_K[0-9][0-9][0-9]/receipt.json','NJT_E[0-9][0-9][0-9]/receipt.json','NJT_QL[0-9][0-9][0-9]/receipt.json','NJT_QK[0-9][0-9][0-9]/receipt.json']:
 for p in sorted(E.glob(pattern)):receipts.append(json.loads(p.read_text()))
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==limits,r['attempt']
 assert str(r['swaps'])=='0',r['attempt']
 ad=load(r['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True,r['attempt']
for m in modules:
 p=E/m['source'];assert sha(p)==m['sha256'],m
 r=next(r for r in receipts if r['attempt']==m['attempt']);assert r['exit_status']==0 and m['sha256'] in r['source_hashes'].values()
 assert not re.search(r'(?m)^\s*(axiom\s|sorry\b|admit\b)|\bnative_decide\b',p.read_text()),p
 if m['module']!='NJT_ClaimsRef_Funs':assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text()),p
raw=[]
for mode,name in [('batch0','proof0'),('batch1','proof1')]:
 r=load('NJT_audit/'+mode+'/'+name+'.json');assert r['policy_pass'] and r['exit_status']==0;raw+=r['results']
wanted=sum(load('NJT_AUDIT_ROOTS.json')['groups'],[])
assert [r['root'] for r in raw]==wanted
for r in raw:assert r['equal'] and r['walked_axioms']==r['collect_axioms'] and set(r['walked_axioms'])<={'Classical.choice','Quot.sound','propext'}
fixture=load('NJT_audit/fixtures/fixtures.json');assert fixture['policy_pass'] and len(fixture['results'])==8
scan=[json.loads(l) for l in (E/'NJT_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
shape=load('NJT_QSHAPE_FIDELITY.json');assert shape['status'].startswith('PASS') and len(shape['cases'])==6
assert all(r['expected_exit']==r['actual_exit'] for r in shape['cases'])
assert shape['production_stub_verified_used'] is False
assert load('NJT_FINAL_HOST_VALIDATION.json')['status']=='PASS' and load('NJT_CLEANUP.json')['status']=='PASS'
assert next(r for r in receipts if r['attempt']=='NJT_L043')['exit_status']==0
assert next(r for r in receipts if r['attempt']=='NJT_L044')['exit_status']==0
assert next(r for r in receipts if r['attempt']=='NJT_E001')['exit_status']==0
subprocess.run(['git','diff','--quiet','HEAD','--','crates','programs','Cargo.lock'],check=True)
base=Path('evidence/ledger15-20261108/NJO_LEDGER.json.xz');ledger=json.loads(lzma.decompress(base.read_bytes()));index={r['row']:r for r in ledger['rows']}
packet=load('NJT_CLOSED.json');delta=load('NJT_LEDGER_DELTA.json')
assert {r['row'] for r in delta['updates']}=={'TX1:066','TX1:067','TX1:068','TX1:070'}
for f in packet['functions']:
 for row in f['rows']:
  old=index[row];assert old['status']=='OPEN' and f['function']==old['function'] and f['frozen_body_sha256']==old['frozen_body_sha256'] and f['obligation_statement_hash']==old['obligation_statement_hash']
packet['status']='Four locally gated CLOSED candidates; credit waits for next ledger gate; authoritative ledger unchanged'
packet['gate']={'combined':'NJT_L043','coherence':'NJT_L044','raw':['NJT_L045','NJT_L046'],'fixtures':'NJT_L038','strict_t':'NJT_QSHAPE_FIDELITY.json'}
(E/'NJT_CLOSED.json').write_text(json.dumps(packet,indent=2)+'\n')
root=[r for r in receipts if not r['attempt'].startswith('NJT_Q')]
child=[r for r in receipts if r['attempt'].startswith('NJT_Q')]
support=[r for r in receipts if r['attempt'].startswith(('NJT_L','NJT_QL'))]
kani=[r for r in receipts if r['kind']=='kani'];extractions=[r for r in receipts if r['kind']=='extraction']
assert len(support)<=100 and len(kani)<=80 and len(extractions)<=2
budget=dict(lean_support=len(support),kani=len(kani),extractions=len(extractions),limits={'lean_support':100,'kani':80,'extractions':2},prelaunch_exclusions=['NJT_L006 missing prerequisite object','first local NJT_L020 active-client guard refusal, eventual compile submitted once'])
summary=dict(status='PASS for four QueryScan candidates;129/069 OPEN',security_target_established=False,branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',headline='AspisR1.RPx_Deployed.deployed',baseline={'ledger':str(base),'sha256':sha(base),'counts':{'CLOSED':463,'QUALIFIED':0,'OPEN':136}},candidate_rows=['TX1:066','TX1:067','TX1:068','TX1:070'],open_rows=['TX1:069','TX1:129'],authoritative_ledger_changed=False,full_combined_import_attempts=['NJT_L036','NJT_L043'],final_scan={'attempt':'NJT_L044','exit_status':0,'modules':len(scan),'dangling':0,'incompatible_declarations':0,'import_mismatches':0},raw={'attempts':['NJT_L045','NJT_L046'],'roots':len(raw),'all_equal_collectAxioms':True,'axioms':sorted({a for r in raw for a in r['walked_axioms']}),'headline':raw[0]},fixtures={'attempt':'NJT_L038','cases':8,'pass':True},strict_t={'path':'NJT_QSHAPE_FIDELITY.json','sha256':sha(E/'NJT_QSHAPE_FIDELITY.json'),'expected_verdicts':6,'pass':True,'production_stub_verified':False},new_modules=len(modules),budget=budget,max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),all_swaps_zero=True,exact_limits=limits,all_admissions_allowed_and_exit0=True,timeout_or_memory_killed=[],unchanged_failed_elaboration_rerun=['NJT_L022 replacement pattern missed token; excluded, repaired L023/L024'],quarantined=[],suspended=[],trust_changes={'added':[],'removed':[],'widened':[],'transport':'P6/D188 option A RECLASSIFICATION only'},shipped_source_changed=False,elf_rebuilt=False,inherited_elf_pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},export=load('NJT_EXPORT.json'),cleanup=load('NJT_CLEANUP.json'),working_object_cleanup=load('NJT_CLEAN_OBJECTS.json'),child_object_cleanup=load('NJT_QOBJECT_CLEANUP.json'),limitations=['Cached coherent closure, not a cold release replay','129 returning-value Std is not native allocator/heap interpretation; unsafe full P6 join OPEN','069 retains explicit conservative child202','Next ledger gate required; no headline extraction premise removed'])
(E/'NJT_AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'NJT_ROOT_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in root))
# Complete public register, preserving every full per-attempt receipt separately.
(E/'NJT_ATTEMPTS.jsonl').write_text(''.join(json.dumps({**{k:v for k,v in r.items() if k!='deps_fingerprint'},'full_receipt':r['attempt']+'/receipt.json'})+'\n' for r in receipts))
(E/'NJT_PRINTED_ROOTS.md').write_text('# Printed root statements\n\nExact definitions, quantifiers and hidden cut/domain fields from L047; these are statement inspections, not native closure claims.129 is support only.\n\n```text\n'+(E/'NJT_L047/stdout.log').read_text()+'\n```\n')
cert=['# NJT certificates','', 'Target not yet established. Only TX1:066/067/068/070 are locally gated candidates; next ledger review supplies credit.129/069 remain OPEN. No imported, model-only or partial native fact is promoted to row closure.','', '| Module | Focused passing receipt | Source SHA256 |','|---|---|---|']
cert += ['| '+m['module']+' | '+m['attempt']+' | '+m['sha256']+' |' for m in modules]
cert += ['', 'Final combined L043 prints all42 roots; NFX L044 checks all15,734 loaded modules with zero dangling/incompatible/import errors; raw L045/L046 walks42 roots and equals collectAxioms with only propext/Classical.choice/Quot.sound. L038 passes all eight planted/mutated fixtures. Strict(t) array8 calibration passes all six expected verdicts; see NJT_QFIDELITY.md. Exact tool/driver diff and walker/object pins are NJT_DRIVER.diff, NJT_WALKER_PIN.json and NJT_AUDIT_TOOL_PINS.json.', '', 'Every formal/native attempt records exact target/command/env, source revision plus source/dependency hashes, exit, wall, peakRSS, swaps, caps and printed axioms (or N/A for native). Rust reference L003 is optimized; E001 Charon0/Aeneas0. Only the first changed shape was extracted; no second extraction or patched extractor was used. All Kani runs validate frozen offline dependency resolution, all-crate features and unchanged Cargo.lock.', '', 'The formal consumer gate is the frozen3 deployed headline; digest/error remain op43/op44. Borrowed inputs retain their full records. There is no new security metric, privacy or two-transaction change, no new trust row and no premise removal.', '', 'L048 exports19 modules/1,941,608 bytes; L049 verifies all32,327 selected object/sidecar/IR hashes and identical consumer resolution, including actual Aeneas library objects. No third combined compile was run. L050/L051 and QL033/QL034 clean only owned rebuildable outputs, preserving every retained cache/export. ELF pins are inherited only; crates/programs/lock remain frozen.']
(E/'NJT_CERTIFICATES.md').write_text('\n'.join(cert)+'\n')
for p in E.rglob('__pycache__'):shutil.rmtree(p)
large=[str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024];assert not large,large
(E/'NJT_VALIDATION.json').write_text(json.dumps(dict(status='PASS',validator='NJT_finalize.py',new_modules=len(modules),raw_roots=len(raw),candidate_rows=summary['candidate_rows'],open_rows=summary['open_rows'],budget=budget,files_over20MB=large,diff_check='Source/manifests checked; verbatim raw .log bytes retain original whitespace',shipped_files_unchanged=True,axiom_policy='standard only',target_not_yet_established=True),indent=2)+'\n')
print(json.dumps(dict(status='PASS',candidates=4,open=['069','129'],raw_roots=len(raw),modules=len(scan),budget=budget)))
