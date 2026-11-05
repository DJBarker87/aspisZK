"""Strict source/packet association for the all-input current registry decoder."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';S='crates/aspis-statement/src/pool_v1/verifier_registry.rs'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
src=(R/S).read_text();assert src==subprocess.check_output(['git','show',F+':'+S],cwd=R,text=True)
def fun(s,name):
 m=re.search(r'\bfn '+re.escape(name)+r'\s*\(',s);assert m,name;a=s.index('{',m.end());i=a+1;d=1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
def tokens(s):return re.findall(r'\w+|[^\w\s]',s)
def source(a,name):
 rel='NHY_src/'+name;p=E/a/'sources'/rel
 if p.exists():return p.read_text()
 idx=read(E/'NHY_INPUTS.json');h=idx['attempts'][a][rel];b=lzma.decompress((E/idx['objects'][h]['path']).read_bytes());assert sha(b)==h;return b.decode()
def passing(a,negative=False):
 r=read(E/a/'receipt.json');s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert r['exit_status']==(1 if negative else 0) and 'timed out' not in s
 if negative:assert re.search(r'\*\* 1 of \d+ failed',s) and 'Failed Checks:' in s
 else:assert 'VERIFICATION:- SUCCESSFUL' in s
 assert read(E/(a+'-graph-check.json'))['graph_matches_frozen'];assert read(E/(a+'-erasure-check.json'))['passed'];assert read(E/(a+'-lock-check.json'))['unchanged']
 return r
pairs=[(49,50),(53,54),(57,58),(63,64),(93,94)]
for pos,neg in pairs:
 p,n=passing(f'NHY_K{pos:03}'),passing(f'NHY_K{neg:03}',True)
 pc,nc=p['native_command'],n['native_command'];assert pc[pc.index('--features')+1]==nc[nc.index('--features')+1]
 # Every selected statement feature equals the deployed caller's statement closure.
 assert pc[pc.index('--features')+1]==','.join(read(E/'NHY_STATEMENT_FEATURES.json'))
for n in ['NHY_L052','NHY_L053','NHY_L055','NHY_L074','NHY_L075','NHY_L078','NHY_L079','NHY_L080']:assert read(E/n/'receipt.json')['exit_status']==0
f=fun(src,'decode_verifier_registry_v2');prefix=f[1:f.index('    let registry')];mapping={'WrongLength':1,'WrongMagic':2,'WrongVersion':3,'InvalidDeploymentMode':4,'NonZeroReserved':5};cut=prefix
for label,tag in mapping.items():cut=cut.replace('return Err(PoolV1VerifierRegistryFormatError::'+label+');','return '+str(tag)+';')
current=(E/'NHY_registry.rs.txt').read_text();assert tokens(fun(current,'registry_v2_header'))==tokens('{'+cut+'0}')
for k in [57,58]:assert tokens(fun(source(f'NHY_K{k:03}','crates/aspis-statement/src/pool_v1/NHY_registry.rs'),'registry_v2_header'))==tokens('{'+cut+'0}')
# Every original source read is enumerated, not a manufactured backing slice.
a=f.index('let registry = VerifierRegistryV2');b=f.index('    };',a)+6;literal=f[a:b]
fields=re.findall(r'^        (\w+):',literal,re.M)
ranges=[(int(a),int(b)) for a,b in re.findall(r'bytes\[(\d+)\.\.(\d+)\]',literal)]
assert [a for a,b in ranges if b-a==32]==[8,40,72,120,152,184,216]
assert [a for a,b in ranges if b-a==8]==[104,112]
assert all(0<=a<b<=256 for a,b in ranges)
assert re.findall(r'bytes\[(\d+)\](?!\.)',literal)==['5','7','248']
for k,name in [(63,'registry_record_packet'),(93,'registry_args_packet')]:
 text=source(f'NHY_K{k:03}','crates/aspis-statement/src/pool_v1/NHY_registry.rs');body=fun(text,name)
 built=re.search(r'let registry\s*=\s*VerifierRegistryV2\s*\{(.*?)\};',body,re.S);assert built
 observed=re.findall(r'(\w+)\s*:\s*input\.(\w+)',built[1]);assert observed==[(n,n) for n in fields]
 assert 'kani::assume((field as usize)<7)' in body and 'kani::assume(j<32)' in body
 assert not re.search(r'\bstatic\b',body)
args=fun(source('NHY_K093','crates/aspis-statement/src/pool_v1/NHY_registry.rs'),'registry_args_packet');assert 'NHY_registry_byte(&registry,field,j)' in args
# Natural model and record extensionality are actual raw-walked roots, not
# model-only substitutions for a missing native or child packet.
raw=[]
for n in ['NHY_stage9_audit/proof15.json','NHY_stage10_audit/proof16.json']:
 p=read(E/n);assert p['exit_status']==0;raw+=p['results']
for n in ['NHY_RegistryModel.source','NHY_RegistryJoin.cohort','NHY_RegistryJoin.source']:
 assert n in json.dumps(raw)
scan=read(E/'NHY_stage10_audit/scan_summary.json');assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
out=dict(status='PASS_REGISTRY_NATIVE_MODEL_ASSOCIATION',row='TX2:204',function=S+'::decode_verifier_registry_v2',frozen_revision=F,frozen_file_sha256=sha(src.encode()),prefix_sha256=sha(prefix.encode()),constructor_sha256=sha(literal.encode()),fields=fields,ranges=ranges,byte_offsets=[5,7,248],native_pairs=pairs,all_lengths='Native unrestricted descriptor classifier K008/009 and retained SDK/std Slice.len metadata law; all non256 lengths return WrongLength before payload access. K057/058 is the physical256-byte header cut, every byte unrestricted. No fake large slice or malloc bound.',field_association='K049/050 embeds the same original256-byte source in a contained64-byte window, arbitrary offset and byte; retained NCX_K027/028 cast value/frame. K053/054 embeds word reads in contained16-byte windows; NCX_K029/030 little-endian value. NHY_WindowTransport.field/bounds and NHY_NaturalReads give the same symbolic fields and all bounds. No64/16 restriction imposed on original buffer.',record_association='K093/094 logs every constructed validator argument field independent of validator reply; K063/064 transports every Result error and every returned record field/scalar. NHY_RecordExt.registry_injective turns arbitrary field/byte observations into complete record equality. Exact original constructor order and all source reads enumerated above.',child='TX2:209 CLOSED by NHY current-registry validator certificate, every complete typed record; no success premise. Std array/word/length calls have exact retained domains and P6/D188 ABI/compiler realization.',model='NHY_RegistryModel.source is universal in Slice U8, including every first error; NHY_RegistryJoin.source/cohort selects actual NCX_Install.op33 with full error/record ports, preserves op43/op44.',effects='Input immutable, no allocator or mutable account; all field reads/casts pure, complete Result and panic-unreachable exact length domains. No discarded writes or callback/std allocation cleanup.',trust='Native-contract semantic transport is retained P6/D188 option-A reclassification, not removal. No new trust row, RuntimeCpiReadonlyEntry7, fixture PDA, success hypothesis or SameExecution wrapper.',whole_entry_path=False)
(E/'NHY_REGISTRY_ASSOCIATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(status=out['status'],row=out['row'])))
