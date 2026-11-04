"""Final source/artifact and budget checks; no compilation or proof invocation."""
from pathlib import Path
import json,hashlib,re,subprocess,collections
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=[json.loads(x) for x in (E/'NFM_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(a)==len({r['attempt'] for r in a})==160
assert sum(r['kind']=='kani' for r in a)==100
assert sum(r['kind']!='kani' for r in a)==60
assert all(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} for r in a)
proof=[]
for p in sorted(E.glob('NFM_*.lean')):
 s=p.read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',s),p
 passing=[r for r in a if r['kind']=='lean' and r.get('module')==p.stem and r['exit_status']==0 and r.get('source_hashes',{}).get('NFM_generated/'+p.name)==sha(p)]
 assert passing,p
 proof.append(dict(path=str(p.relative_to(R)),sha256=sha(p),compiled_attempt=passing[-1]['attempt']))
assert len(proof)==13
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<20_000_000,p
 if p.is_symlink():assert p.resolve().is_relative_to(E),p
changed=subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(p.startswith('evidence/slice-q-mul9-20261104/') for p in changed+untracked)
exports=json.loads((E/'NFM_OBJECT_EXPORTS.json').read_text());assert exports['exit']==0 and exports['admission']['allowed'] is True
assert exports['own_cache_retained'].endswith('codex-cx-slice-q-mul9-cache-20261104')
out=dict(status='PASS_SOURCE_ARTIFACT_BUDGET',proofs=proof,budget={'kani':100,'lean_audit':60,'extraction':0},new_unchecked_modules=[],shipped_changes=[],all_files_under_20MB=True,symlinks_owned_content_only=True,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_sha256='53fa714e84ded64b844061f4d1b66ad20ee1ba48c3873a73970f80ede8a0b602',ELF_rebuild_required=False,ELF_hashes_inherited_only={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','Pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},compiled_cache_retained=True,scope='Cached focused development evidence; not cold release replay or security-target closure')
(E/'NFM_PREFLIGHT.json').write_text(json.dumps(out,indent=1)+'\n');print(out['status'],len(proof),'unchanged passed modules')
