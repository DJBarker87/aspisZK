"""Pin reused sources and validate the INCOMPLETE vertical-slice checkpoint.
No native/source association is inferred from these textual checks.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,re
E=Path('evidence/pv-stx-20261104');out=E/'reuse-source';out.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
imports=[
 ('fd4a644fd414079022f8781c14a6683b41504ab7','PV_EVH_World','PV_STX_World','Base/FileState; machine replaces M/bind'),
 ('fd4a644fd414079022f8781c14a6683b41504ab7','PV_EVH_Runtime','PV_STX_World','State/Layout/Block/Handle; source machine Fault replaces runtime Fault'),
 ('fd4a644fd414079022f8781c14a6683b41504ab7','PV_EVH_Entropy','PV_STX_EntropyWorld','cursor advancement and entropy request/delivery events; pending has no committed draw'),
 ('fd4a644fd414079022f8781c14a6683b41504ab7','PV_EVH_ZeroWrappers','PV_STX_EntropyWorld','transparent new/asMut/deref/derefMut/restoration; destruction remains separate'),
 ('fd4a644fd414079022f8781c14a6683b41504ab7','PV_EVH_NonceWorld','PV_STX_NonceWorld','file-state transitions and open/write/sync primitives; Answer extends Result'),
 ('fd4a644fd414079022f8781c14a6683b41504ab7','PV_EVH_LiteralDiagnostics','PV_STX_Diagnostics','literal bytes and ignored-error drop continuation; actual writer remains open'),
 ('058c4c764ca7daa9953491ec9a41b36a605121c7','PV_EVH_AllocatorWorld','PV_STX_AllocatorWorld','tryAllocate state/events; Code replaces runtime bind'),
 ('058c4c764ca7daa9953491ec9a41b36a605121c7','PV_EVHB_CallbackEffects','PV_STX_CallbackEffects','argument then capture destruction; primitive requests replace Q computations'),
 ('058c4c764ca7daa9953491ec9a41b36a605121c7','PV_EVHB_ReserveWorld',None,'INSPECTED ONLY; V183 owner/RawVec-specific reserve NOT ported or imported'),
 ('058c4c764ca7daa9953491ec9a41b36a605121c7','PV_EVHB_RawVecOwner',None,'INSPECTED ONLY; owner registry NOT ported or imported')]
rows=[]
for rev,mod,port,note in imports:
 p='lean/'+mod+'.lean';b=subprocess.check_output(['git','show',rev+':'+p]);q=out/(mod+'.lean.txt')
 if '--check' in sys.argv: assert q.read_bytes()==b,q
 else:q.write_bytes(b)
 rows.append(dict(revision=rev,path=p,sha256=sha(b),retained=str(q),port=port,mode='source port' if port else 'inspection only',limits=note))
manifest=json.dumps(dict(reused=rows,streamA_method='ruling (y): local full-answer logs plus caller/child substitution; NO Kani execution or credited native caller bridge',kani_budget=0,k3='logs/counters are local records; no writable static introduced; historical writable-static entropy harnesses receive no new credit',status='vertical slice INCOMPLETE; no source_entry_world or projections'),indent=2)+'\n'
p=E/'reuse-source/manifest.json'
if '--check' in sys.argv: assert p.read_text()==manifest
else:p.write_text(manifest)
for p in Path('lean').glob('PV_STX_*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom |set_option max(RecDepth|Heartbeats)',p.read_text(),re.M),p
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
print('reuse sources pinned; ports and inspection-only modules distinguished; slice remains incomplete')
