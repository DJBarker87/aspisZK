"""Full current-entry native/source/model association, strict retained receipts."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry4-20261106';R=E.parents[1]
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';S='crates/aspis-statement/src/pool_v1/verifier_registry.rs'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
def fun(s,name):
 m=re.search(r'\bfn '+re.escape(name)+r'\s*\(',s);assert m,name;a=s.index('{',m.end());i=a+1;d=1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
def tokens(s):return re.findall(r'\w+|[^\w\s]',s)
def source(root,a,rel):
 p=root/a/'sources'/rel
 if p.exists():return p.read_text()
 idx=read(root/('NIJ_INPUTS.json' if root==E else 'NHY_INPUTS.json'));h=idx['attempts'][a][rel];b=lzma.decompress((root/idx['objects'][h]['path']).read_bytes());assert sha(b)==h;return b.decode()
def passing(root,a,neg=False):
 r=read(root/a/'receipt.json');s=lzma.decompress((root/a/'stdout.log.xz').read_bytes()).decode()
 assert r['exit_status']==(1 if neg else 0) and 'timed out' not in s
 if neg:assert re.search(r'\*\* 1 of \d+ failed',s) and 'Failed Checks:' in s and 'unwinding assertion' not in s
 else:assert 'VERIFICATION:- SUCCESSFUL' in s
 assert read(root/(a+'-graph-check.json'))['graph_matches_frozen'];assert read(root/(a+'-erasure-check.json'))['passed'];assert read(root/(a+'-lock-check.json'))['unchanged']
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert r['source_hashes'].get(('NIJ_src/' if root==E else 'NHY_src/')+'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 return r
pairs=[(P,'NHY_K051','NHY_K052'),(P,'NHY_K055','NHY_K056'),(P,'NHY_K059','NHY_K060'),(P,'NHY_K095','NHY_K096'),(P,'NHY_K108','NHY_K109'),(E,'NIJ_K056','NIJ_K057')]
for root,p,n in pairs:
 a,b=passing(root,p),passing(root,n,True);ac,bc=a['native_command'],b['native_command'];assert ac[ac.index('--features')+1]==bc[bc.index('--features')+1]
 assert ac[ac.index('--features')+1]==','.join(read(E/'NIJ_STATEMENT_FEATURES.json'))
# Retained all-u8 status bridge (K043 feature mismatch excluded, K044 used).
passing(P,'NHY_K042');passing(P,'NHY_K044',True)
closed=read(P/'NHY_CLOSED.json');assert any(c['id']=='NHY::status' for c in closed['functions']);assert any(c['id']=='NHY::entry_v2_validator' for c in closed['functions'])
src=subprocess.check_output(['git','show',F+':'+S],cwd=R,text=True);f=fun(src,'decode_verifier_registry_entry_v2');a=f.index('    let entry');b=f.index('    };',a)+6;literal=f[a:b];prefix=f[1:a]
# Header cuts retain every original guard and first error.
cut=prefix
for label,tag in {'WrongLength':1,'WrongMagic':2,'WrongVersion':3,'InvalidDeploymentMode':4,'NonZeroReserved':5}.items():cut=cut.replace('return Err(PoolV1VerifierRegistryFormatError::'+label+');','return '+str(tag)+';')
old=source(P,'NHY_K059','NHY_src/crates/aspis-statement/src/pool_v1/NHY_registry.rs');assert tokens(fun(old,'entry_v2_header'))==tokens('{'+cut+'0}')
# The new producer executes the EXACT original complete constructor, status ? included.
for attempt in ['NIJ_K056','NIJ_K057']:
 text=source(E,attempt,'NIJ_src/crates/aspis-statement/src/pool_v1/NIJ_registry.rs');assert literal in fun(text,'producer')
 assert 'static ' not in text and 'stub_verified' not in text
 assert 'kani::assume(field<9)' in text and 'kani::assume(j<32)' in text
assert f[b:].strip()=='validate_verifier_registry_entry_v2(&entry)?;\n    Ok(entry)\n}',f[b:]
ranges=[(int(a),int(b)) for a,b in re.findall(r'bytes\[(\d+)\.\.(\d+)\]',literal)]
assert [a for a,b in ranges if b-a==32]==[8,40,72,104,136,168,200,232,280]
assert [a for a,b in ranges if b-a==8]==[264,272]
assert re.findall(r'bytes\[(\d+)\](?!\.)',literal)==['5','6','312','313']
assert all(0<=a<b<=320 for a,b in ranges)
# Same-variable return-stage map: exact source field order, no second record producer.
ssa=source(P,'NHY_K108','NHY_src/crates/aspis-statement/src/pool_v1/NHY_registry.rs');body=fun(ssa,'entry_ssa_packet')
fields=re.findall(r'^        (\w+):',literal,re.M)
constructed=re.search(r'let entry=VerifierRegistryEntryV2\{(.*?)\};',body,re.S)[1]
assert re.findall(r'(\w+):',constructed)==fields
assert 'reply?;Ok(entry)' in body and 'arrays[field as usize][j]' in body
for name in ['status','statement_version','bump','programdata_bump','activation_slot','retirement_slot']:assert 'value.'+name+'=='+name in body
# The model proof and dictionary join are checked in the actual coherent headline import.
for a in ['NIJ_L005','NIJ_L006','NIJ_L008','NIJ_L010','NIJ_L018','NIJ_L021']:assert read(E/a/'receipt.json')['exit_status']==0
raw=read(E/'NIJ_stage1_audit/proof0.json');assert raw['exit_status']==0
for name in ['NIJ_EntryModel.source','NIJ_EntryJoin.source','NIJ_EntryJoin.cohort','AspisR1.RPx_Deployed.deployed']:
 r=next(r for r in raw['results'] if r['root']==name);assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}
scan=read(E/'NIJ_stage1_audit/scan_summary.json');assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
out=dict(status='PASS_ENTRY_NATIVE_MODEL_ASSOCIATION',row='TX2:202',frozen_revision=F,function=S+'::decode_verifier_registry_entry_v2',frozen_file_sha256=sha(src.encode()),constructor_sha256=sha(literal.encode()),prefix_sha256=sha(prefix.encode()),fields=fields,ranges=ranges,byte_offsets=[5,6,312,313],native_pairs=[dict(directory=str(root.relative_to(R)),positive=p,negative=n) for root,p,n in pairs],all_lengths='WrongLength before payload for every non320 descriptor; retained all-usize NHY_K008/009 and exact std metadata; length320 proves every actual field/read/unwrap bound.',native_chain='Header K059/060; original buffer producer NIJ_K056/057 includes actual status call/early Err and all fields. Arbitrary field/byte plus scalars give complete record by NHY_RecordExt.entry_injective and exact NCX two-sided carriers. SAME fields enter validator (shared reference, no copy); CLOSED TX2:207 every complete typed record. NHY_K108/109 independent post-read SSA packet transports every validator Result/error and exact returned fields. No successful-parser/validator premise.',model='NIJ_EntryStatus.rejected handles first invalid status; NIJ_EntryModel.source is universal full first-error natural model; NIJ_EntryJoin.cohort selects NCX_Install.op34 and preserves digest/error slots43/44.',effects='Pure original immutable source and shared record, no allocator/account mutation, all Result labels retained; every reached unwrap exact-length. No discarded write or cleanup.',trust='P6/D188 native semantic transport retained as option-A reclassification; existing std/compiler/ABI trust retained. No added runtime trust or source change.',whole_entry_path=False)
(E/'NIJ_ENTRY_ASSOCIATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(status=out['status'],row=out['row'])))
