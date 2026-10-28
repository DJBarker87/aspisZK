from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def frozen(p):return subprocess.check_output(['git','show',REV+':'+p],text=True)
def body(s,name):
 i=s.index('fn '+name);a=s.index('{',i);d=1;j=a+1
 while d:
  d+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[a:j]
def norm(s):return re.sub(r'\s+','',s)
p='crates/aspis-statement/src/pool_v1/pair_terminal.rs';s=frozen(p)
a=body(s,'decode_pool_v1_pair_verified_afterstate_v1')
a=a.replace('decode_digest_canonical','decode').replace('validate_verified_afterstate(&afterstate)','validate(&afterstate)').replace('super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION','super::super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION')
b=body((E/'NBU_decode.rs.txt').read_text(),'NBU_decode_cut');assert norm(a)==norm(b),'decoder cut changed outside named child substitutions'
ranges=re.findall(r'decode\(&exact\(&bytes\[(\d+)\.\.(\d+)\]\)\?\)',a)
assert [(int(l),int(r)) for l,r in ranges]==[(16+32*k,48+32*k) for k in range(21)]
x=dict(frozen_revision=REV,decoder_cut=dict(body_equal_after_named_substitutions=True,substitutions=['decode_digest_canonical -> decode on the SAME exact32 input','validate_verified_afterstate -> validate on the SAME parsed record','one parent-module qualification'],source_sha256=hashlib.sha256(s.encode()).hexdigest(),ordered_digest_ranges=ranges,induction='Imported NBN_AfterstateDecoderDependency.source; K005 receives no credit; exact32/exact8 and one arbitrary range replace native whole decoder'),windows=dict(afterstate_rows=dict(base=48,width=32,count=20,limit=688),live_rows=dict(base=160,width=32,count=20,limit=800),late=dict(header=[0,32],live=[32,832],after=[832,1520]),asf8=dict(header=[0,8],master=[8,40],checkpoint=[40,72],lane=[72,104],sequence=[104,112],anchor=[112,144],late=[144,1664],payment=[1664,1880])),kernel_value_laws=['NBU_CopyWindows.window_spec','NBU_CopyWindows.disjoint','NBU_CopyWindows.rows_spec','NBU_SourceWindows.array_window','NBU_SourceWindows.live_row','NBU_AnyWindow.source'],scope='Local P6 native/source-model association only; inherited platform and source-to-ELF boundaries unchanged')
(E/'NBU_SOURCE_ASSOCIATION.json').write_text(json.dumps(x,indent=2)+'\n')
print('decoder substitutions and every ordered digest window match frozen source')
