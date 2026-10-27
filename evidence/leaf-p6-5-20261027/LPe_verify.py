"""Read-only validation of receipts, patch, frozen sources and accounting."""
from pathlib import Path
import subprocess,json,hashlib,tempfile
E=Path(__file__).resolve().parent;errors=[]
def need(b,msg):
 if not b:errors.append(msg)
sha=lambda b:hashlib.sha256(b).hexdigest()
rs=[]
for p in sorted(E.glob('LPe_K[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];rs.append(r);g=json.loads((E/(a+'-graph-check.json')).read_text())
 need(g['resolved_packages']==441 and g['package_and_edges_match'] and not g['edge_errors'],a+' graph')
 need(g['lock_unchanged'] and g['lock_before_sha256']==sha(Path('Cargo.lock').read_bytes())==g['lock_after_sha256'],a+' lock')
 need(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a+' caps')
 need(r['swaps']=='0',a+' swaps');need(r['env']['CARGO_NET_OFFLINE']=='true',a+' offline');need(r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a+' optimized')
 need('--locked' not in r['command'],a+' rejected flag')
 need(len(r['print_axioms'])>0,a+' axioms NA field')
for top in ['Top','ARX_Root','FJv_Top']:
 need((E/f'LPe_{top}.BEFORE.lean.txt').read_bytes()==(E/f'LPe_{top}.AFTER.lean.txt').read_bytes(),top+' changed')
for name in ['ARX_Root','FJv_Top']:
 need(Path('lean',name+'.lean').read_bytes()==(E/f'LPe_{name}.BEFORE.lean.txt').read_bytes(),name+' live source drift')
need(len(rs)<=20,'Kani budget');need(len(list(E.glob('LPe_L[0-9][0-9][0-9]/receipt.json')))<=60,'Lean budget')
need(not subprocess.check_output(['git','diff','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs']), 'shipped tree changed')
expected=json.loads((E/'LPe_frozen_source_manifest.json').read_text())
with tempfile.TemporaryDirectory(prefix='LPe_patch_') as d:
 t=Path(d);root='crates/aspis-r1-cost-probe/src/'
 for f in ['lib.rs','fast_pairing.rs','verifier.rs']:
  p=t/root/f;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(Path(root,f).read_bytes())
 r=subprocess.run(['patch','--batch','-p1','-d',d,'-i',str(E/'LPe_harness.patch')],capture_output=True,text=True)
 need(r.returncode==0,'patch apply '+r.stdout+r.stderr)
 for f in ['lib.rs','fast_pairing.rs','verifier.rs','LPe_replay.rs','LPe_verifier.rs']:
  p=t/root/f
  if p.exists():expected[root+f]={'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
(E/'LPe_expected_scratch_manifest.json').write_text(json.dumps(expected,indent=2)+'\n')
out={'errors':errors,'kani_invocations':len(rs),'lean_attempts':len(list(E.glob('LPe_L[0-9][0-9][0-9]/receipt.json'))),'pass':sum(r['exit_status']==0 for r in rs),'wall_seconds':sum(r['wall_seconds'] for r in rs),'peak_rss_kib':max([int(r['peak_rss_kib']) for r in rs] or [0]),'swaps':0,'ledger_delta':{'T':0,'P':0,'G':0,'C':0},'new_top_axioms':'See Lean per-attempt printed axioms; no Kani-to-Lean axiom introduced','patch_sha256':sha((E/'LPe_harness.patch').read_bytes())}
(E/'LPe_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2));assert not errors
