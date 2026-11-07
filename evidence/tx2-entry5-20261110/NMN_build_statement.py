from pathlib import Path
import re,subprocess,json,hashlib
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'crates/aspis-statement/src/pool_v1'],text=True).splitlines()
structs={};pins={}
for p in files:
 if not p.endswith('.rs'):continue
 t=subprocess.check_output(['git','show',rev+':'+p],text=True);pins[p]=hashlib.sha256(t.encode()).hexdigest()
 for m in re.finditer(r'pub struct (\w+)\s*\{([^}]+)\}',t,re.S):
  fields=re.findall(r'pub\s+(\w+)\s*:\s*([^,]+),',re.sub(r'//[^\n]*','',m[2]));structs[m[1]]=fields
out=[];used=set()
def make(ty):
 ty=ty.strip().removeprefix('super::')
 if ty in ['u8','u16','u32','u64','usize','bool']:return 'kani::any()'
 if ty=='M31':return 'M31(kani::any())'
 if ty=='Digest':return 'core::array::from_fn(|_|M31(kani::any()))'
 if ty.startswith('['):
  element,n=ty[1:-1].split(';',1)
  if element.strip() in ['u8','u16','u32','u64','usize','bool']:return 'kani::any()'
  return 'core::array::from_fn(|_|'+make(element)+')'
 if ty in used:return 'NMN_any_'+ty+'()'
 assert ty in structs,ty
 used.add(ty);fields=structs[ty]
 body=',\n'.join(n+':'+make(t) for n,t in fields)
 out.append('fn NMN_any_'+ty+'()->'+ty+'{'+ty+'{'+body+'}}')
 return 'NMN_any_'+ty+'()'
common=make('PoolV1PairForestTerminalCommonV1');transfer=make('PoolV1PrivateTransferPublicV1');withdraw=make('PoolV1WithdrawalPublicV1')
s='use aspis_statement::pool_v1::*;\nuse aspis_statement::poseidon2::Digest;\nuse aspis_core::field::M31;\n'+'\n'.join(out)+'\nfn NMN_any_statement()->PoolV1PairForestTerminalStatementV1{if kani::any(){PoolV1PairForestTerminalStatementV1::PrivateTransfer{common:'+common+',public:'+transfer+'}}else{PoolV1PairForestTerminalStatementV1::Withdrawal{common:'+common+',public:'+withdraw+'}}}\n'
(E/'NMN_statement.rs').write_text(s);(E/'NMN_STATEMENT_BUILDER.json').write_text(json.dumps({'source_revision':rev,'source_pins':pins,'structs':{t:structs[t] for t in used},'full_raw_M31_words':True,'no_field_arithmetic':True,'status':'generated, not yet compiled'},indent=1)+'\n')
print(json.dumps({'structs':len(used),'bytes':len(s)}))
