#!/usr/bin/env python3
"""Read-only checks of retained CPH proof, source, runtime and artifact evidence."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    start=time.monotonic()
    records=sorted((json.loads(p.read_text()) for p in E.glob('CPH_L*/receipt.json')),key=lambda r:r['attempt'])
    assert len(records)==100
    good=[r for r in records if r['exit_status']==0]
    assert len(good)==88
    allowed={'propext','Classical.choice','Quot.sound'}
    for r in records:
        assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
        assert r['swaps']=='0'
        assert '-M7000' in r['command']
        for name,h in r['source_hashes'].items():
            assert sha(E/r['attempt']/'sources'/name)==h
        if r['exit_status']==0:
            for line in r['print_axioms']:
                if 'depends on axioms:' in line:
                    names=set(line.split('[',1)[1].split(']',1)[0].split(', '))
                    assert names <= allowed,(r['attempt'],line)
    modules={}
    for src in sorted((ROOT/'lean').glob('CPH_*.lean')):
        h=sha(src)
        matches=[r for r in good if r['source_hashes'].get(src.name)==h]
        assert matches,src
        modules[src.name]={'source_sha256':h,'accepted_receipt':matches[-1]['attempt']}
        text=src.read_text()
        code=re.sub(r'/\-.*?\-/','',text,flags=re.S)
        code=re.sub(r'--[^\n]*','',code)
        assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',code),src
        assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',code),src
    top=(ROOT/'lean/CPH_Top.lean').read_text()
    assert top.count('(game : CPH_Game.DeployedPairExecution')==1
    assert top.count('(RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw')==1
    assert 'programNotSystem' not in top and '(program :' not in top
    assert 'CPH_Recorder.Facts' in top and 'CPH_Trace.Facts' in top
    assert 'Port1_CanonicalJoin.AcceptedVerifierJoin' not in top
    assert 'CPH_Rc2Source.source' in (ROOT/'lean/CPH_Pair.lean').read_text()
    game=(ROOT/'lean/CPH_Game.lean').read_text().split('/-- Field (d)')[0]
    assert re.findall(r'^  (\w+) :',game,re.M)==['consecutive','checkpoint','parent','recorded']
    final=next(r for r in records if r['attempt']=='CPH_L101')
    assert final['exit_status']==0 and len(final['print_axioms'])==55
    pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
    low=ROOT/'evidence/lowering2-20261026'
    manifest=json.loads((low/'Low2_build_manifest.json').read_text())
    for b in manifest['builds']:
        assert b['artifact']['sha256']==pins[b['mode']]
        assert b['artifact']['byte_identical']
    sources=json.loads((low/'Low2_build_inputs.json').read_text())['files']
    for name,h in sources.items():assert sha(ROOT/name)==h,name
    pin=json.loads((E/'CPH_PROGRAM_PIN.json').read_text())
    for name,h in pin['evidence'].items():assert sha(ROOT/name)==h,name
    keys=json.loads((E/'CPH_RECORDED_KEYS.json').read_text())
    for name,h in keys['source_receipts'].items():assert sha(ROOT/name)==h,name
    p=ROOT/'docs/research/100bit-spend-path-20261013/evidence/s9-h5-adoption-review-20261023/gate-evidence/runs/readonly/2/runtime'
    a=json.loads((p/'after/stage1.json').read_text());b=json.loads((p/'after/stage2.json').read_text());loaded=json.loads((p/'after/loaded-program.json').read_text());inputs=json.loads((p/'input-manifest.json').read_text());comp=json.loads((p/'comparison.json').read_text())
    assert a['error'] is None and b['error'] is None
    assert a['instruction']['program']==b['instruction']['program']==loaded['program']==pin['verifier_base58']
    assert a['instruction']['accounts'][2]['key']==b['instruction']['accounts'][6]['key']==inputs['checkpoint']
    assert a['instruction']['accounts'][2]['writable'] and not b['instruction']['accounts'][6]['writable']
    assert loaded['elf_sha256']==inputs['after_elf_sha256']==pins['default']
    assert comp['both_admitted_pairs_accepted'] and comp['checkpoint_equal'] and inputs['keys_retained']
    changes=subprocess.check_output(['git','diff','--name-only',json.loads((E/'CPH_INPUTS.json').read_text())['revision']],cwd=ROOT,text=True).splitlines()
    assert all(n.startswith('lean/CPH_') or n.startswith('evidence/cp-game2-20261026/') for n in changes),changes
    usage=resource.getrusage(resource.RUSAGE_SELF)
    out={'target':'CPH focused source/receipt/artifact audit','command':['python3','-B','evidence/cp-game2-20261026/CPH_validate.py'],'exit_status':0,'wall_seconds':time.monotonic()-start,'peak_rss_bytes':usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,'swaps':usage.ru_nswap,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'checker_sha256':sha(Path(__file__)),'lean_invocations':100,'successful':88,'failed_excluded':12,'kani_runs':0,'modules':modules,'source_input_files_rechecked':len(sources),'artifact_pins_reused':pins,'final_audit_receipt':final['attempt'],'final_axiom_lines':55,'standard_axioms_only':True,'runtime_fixture':'REUSED successful exact-default-ELF pair; candidate readonly-metadata/synthetic registry limits retained','full_joint_retained_root_fixture':False,'print_axioms':'No new Lean invocation in this read-only checker; final55 axiom lines checked in CPH_L101.'}
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
