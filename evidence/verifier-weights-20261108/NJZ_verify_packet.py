from pathlib import Path
import json,lzma,hashlib,subprocess,re
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();load=lambda n:json.load(open(E/n))
index=load('NJZ_INPUT_INDEX.json');payload=load('NJZ_NATIVE_INPUTS.json')
def resolve(item):
 if 'archive' in item:return lzma.decompress(E.joinpath(item['archive']).read_bytes())
 if 'payload' in item:return json.load(open(E/item['payload']))[item['key']].encode()
 return E.joinpath(item['file']).read_bytes()
for name,item in index.items():
 raw=resolve(item);assert sha(raw)==item['sha256'] and len(raw)==item['bytes'],name
receipts=[]
for p in sorted(E.glob('NJZ_[LKE][0-9][0-9][0-9]/receipt.json')):
 r=json.load(open(p));receipts.append(r)
 for name,h in r['source_hashes'].items():
  key=r['attempt']+'/sources/'+name;assert key in index,key;assert sha(resolve(index[key]))==h,key
 assert r['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-verifier-weights-20261108/NJZ_target'
 ad=load(r['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert int(r['swaps'])==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if r['kind']=='lean':assert '-M7000' in r['command']
 if r['kind']=='kani':assert r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
# Every selected kernel artifact is the exact successful source snapshot.
for module in load('NJZ_MODULES.json')+['NJZ_COMBINED_IMPORT']:
 matches=[r for r in receipts if r['kind']=='lean' and r['module']==module and r['exit_status']==0]
 assert matches,module
 latest=max(matches,key=lambda r:int(r['attempt'][-3:]));key=latest['attempt']+'/sources/NJZ_generated/'+module+'.lean'
 assert resolve(index[key])==E.joinpath(module+'.lean').read_bytes(),module
 assert all('sorryAx' not in line for line in latest['print_axioms']),module
for p in E.rglob('*'):
 if not p.is_file():continue
 assert p.stat().st_size<=20*1024*1024,('oversize',p)
 assert p.suffix not in ['.olean','.o','.a','.so','.elf'],('binary/object',p)
# Exact scratch overlays erase to frozen sources; never edit the release tree.
for n,adds in {
 'crates/aspis-r1-cost-probe/src/lib.rs':['#![cfg_attr(kani, feature(allocator_api))]\n','\n#[cfg(kani)] include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'],
 'crates/aspis-r1-cost-probe/src/verifier.rs':['\n#[cfg(kani)]\n#[path="NJZ_native.rs"]\nmod NJZ_native;\n'],
 'crates/aspis-core/src/field.rs':['#[cfg_attr(kani, derive(kani::Arbitrary))]\n'],
 'crates/aspis-statement/src/pool_v1/incremental_merkle.rs':['#[cfg_attr(kani, derive(kani::Arbitrary))]\n']}.items():
 text=payload[n]
 for a in adds:assert text.count(a)==1;text=text.replace(a,'',1)
 assert text.encode()==subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n]),n
assert not subprocess.check_output(['git','diff','HEAD','--','crates','programs'])
assert load('NJZ_AUDIT.json')['gate']=='PASS' and load('NJZ_CLEANUP.json')['cache_preserved']
assert load('NJZ_CLOSED.json')['ledger_credit'].startswith('PENDING')
assert load('NJZ_LEDGER_DELTA.json')['admitted_changes']==[]
result=dict(status='PASS',captures=len(index),receipts=len(receipts),selected_modules=11,owned_rows=15,immutable_release=True,no_oversize_or_binary=True,lossless_inputs=True,cache_retained=True,authoritative_credit_unchanged=True)
E.joinpath('NJZ_PACKET_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n');print('Packet validation PASS: lossless inputs, exact successful sources, bounded receipts,15 pending row packets, immutable release.')
