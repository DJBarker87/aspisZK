"""Reconcile the resumed receipts without promoting ungated native rows."""
from pathlib import Path
import json,lzma,re,hashlib,subprocess
E=Path(__file__).resolve().parent
write=lambda n,x:(E/n).write_text(json.dumps(x,indent=1)+'\n')
rs=[json.loads(l)for l in(E/'NKF_ATTEMPTS.jsonl').read_text().splitlines()]
resume=[r for r in rs if r['attempt']=='NKF_K081' or (r['attempt'].startswith('NKF_L') and int(r['attempt'][-3:])>=16)]
log=lambda a:lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
results=lambda a:[json.loads(l[len('NEP_RESULT '):])for l in log(a).splitlines()if l.startswith('NEP_RESULT ')]
raw=results('NKF_L028');fixtures=results('NKF_L027');allowed={'propext','Classical.choice','Quot.sound'}
assert len(raw)==50 and all(x['equal']and set(x['walked_axioms'])<=allowed for x in raw)
assert len(fixtures)==8 and all(x['equal'] for x in fixtures)
assert sum(bool(x['walked_axioms'])for x in fixtures)==4
loaded=[json.loads(l)for l in lzma.decompress((E/'NKF_NKF_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert len(loaded)==15978 and all(x['imports_match']and not x['dangling']and not x['duplicate_owners']for x in loaded)
pins=json.loads((E/'NKF_PREDECESSOR_COMPARISON.json').read_text());assert pins['status']=='PASS'and not pins['mismatches']
formal=[r for r in resume if r['kind']!='kani'];assert len(formal)==19
current=[]
for p in sorted(E.glob('NKF_*.lean')):
 if p.stem in ['NKF_COMBINED_IMPORT','NKF_ScanDriver']:continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 matches=[r for r in rs if r['kind']=='lean'and r['module']==p.stem and r['exit_status']==0 and h in r['source_hashes'].values()]
 assert matches,p
 r=matches[-1];current.append(dict(module=p.stem,source_sha256=h,attempt=r['attempt'],roots=re.findall(r'^theorem (\w+)',p.read_text(),re.M),axioms=r['print_axioms']))
write('NKF_FOCUSED_FORMAL.json',dict(modules=current,failed_drafts_excluded=True,standard_axioms=sorted(allowed)))
disks=[json.loads((E/(r['attempt']+'-disk.json')).read_text())for r in resume]
assert all(x['allowed']and x['free_bytes']>=40_000_000_000 for x in disks)
resources=dict(resumed_scopes=len(resume),resumed_formal_support_scopes=len(formal),resumed_lean_compiles=sum(r['kind']=='lean'for r in resume),resumed_kani_invocations=1,kani_remaining=0,formal_support_remaining_conservative=77-len(formal),extraction_remaining=0,combined_audits_used=1,combined_audits_remaining=1,wall_seconds=sum(r['wall_seconds']for r in resume),peak_rss_kib=max(int(r['peak_rss_kib'])for r in resume),swaps=sum(int(r['swaps'])for r in resume),minimum_pre_scope_free_bytes=min(x['free_bytes']for x in disks),host_end=json.loads((E/'NKF_RESUME_HOST_END.json').read_text()))
write('NKF_RESUME_RESOURCES.json',resources)
write('NKF_AUDIT.json',dict(status='PASS_SUPPORT_ONLY_NATIVE_ROWS_OPEN',headline='AspisR1.RPx_Deployed.deployed',combined_import=dict(attempt='NKF_L024',exit=0,completed=1,limit=2),raw_ax2=dict(attempt='NKF_L028',exit=0,roots=len(raw),standard_axioms=sorted(allowed),all_equal_collectAxioms=True),fixtures=dict(attempt='NKF_L027',exit=0,checks=8,planted=4,mutations=4,same_binary=True),NFX=dict(attempt='NKF_L034',exit=0,modules=len(loaded),dangling=0,conflicting_owners=0,import_mismatches=0),pins=dict(attempt='NKF_L035',exit=0,previous_files=pins['previous_files'],mismatches=0),closed_rows=0,open_rows=['TX2:216','TX2:217','TX2:218','TX2:233','TX2:234','TX2:242'],resources=resources,target_not_yet_established=True))
x=json.loads((E/'NKF_CLOSED.json').read_text());x.update(admission='Joint support audit PASS; no complete native packet admitted',status='NO_CLOSED_ROWS_NATIVE_OBLIGATIONS_OPEN',validation='NKF_L024 combined, L027 eight fixtures, L028 raw ax2, L034 NFX, L035 coherent pins all exit0; K081 compilation failure earns no native credit');write('NKF_CLOSED.json',x)
x=json.loads((E/'NKF_LEDGER_DELTA.json').read_text());x['status']='ZERO_DELTA_NATIVE_OBLIGATIONS_OPEN';x['audit']='NKF_AUDIT.json';write('NKF_LEDGER_DELTA.json',x)
write('NKF_UNRUN.json',dict(native=['Returned-Box explicit-constructor/logging control for both records','K064 split native iteration/window/control','K067 split constructor/control','Full ordered registry source invocation and syscall ABI/frame','Seven-account authentication parent cuts','validate_asq8 ordered parent cuts'],combined_remaining=1,reason='No complete native row; unchanged combined regression forbidden without new inputs; no remaining independent native cut awaiting Lean-only discharge'))
write('NKF_HYPOTHESES.json',dict(positive_roots=['NKF_Roots.master','NKF_Roots.checkpoint'],statements='NKF_L024/stdout.log.xz; definitions also NKF_COMBINED_IMPORT.lean',retained=['arbitrary Reservation, no success premise','SAME immutable bytes and raw/result carriers','reviewed MasterCut/CheckpointCut; raw decoder theorem applied internally at SAME arguments'],discharged=['raw152/153 value/error laws at same bytes, from CLOSED NJY/NJQ packets','bounded/modulo windows reconstruct complete master/checkpoint records'],not_discharged=['native fidelity/control certification of returned-Box cut','native allocation-to-source total transport on abort prefix'],new_support_only=['NKF_SeedWindows.invocation explicitly takes op and window cut; NOT an (aq)(2) implementation root','NKF_LaneConstructor.constructor takes field windows; native producer OPEN','NKF_LaneFactor and NKF_LanePrefix are model lemmas, not parent invocation roots'],trust_changes='NONE; no new ReviewedTranscription admitted, no runtime row added or removed'))
# Check frozen shipped input identity, rather than infer it from evidence-only edits.
frozen=subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs','Cargo.lock']).returncode
assert frozen==0
write('NKF_RESUME_FINAL_CHECK.json',dict(frozen_shipped_sources_unchanged=True,elf_rebuild_trigger=False,elf_pins_inherited_not_rebuilt=True,quarantined=[],suspended=[],new_trust_rows=[],target_not_yet_established=True))
print(json.dumps(dict(audit='PASS_SUPPORT_ONLY',closed=0,roots=50,modules=15978,remaining_formal_support=58)))
