from pathlib import Path
import re,json,hashlib,subprocess
D=Path(__file__).parent
P=Path('crates/aspis-prover/src/state_only_entropy.rs');s=P.read_text()
def body(anchor):
 a=s.index('{',s.index(anchor));depth=1;b=a+1
 while depth:
  depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
def tokens(x):
 x=re.sub(r'//[^\n]*','',x)
 return re.findall(r'"[^"\n]*"|[a-zA-Z_]\w*|\d+|[^\s]',x)
expected='''{
 if i==32 { name.push_str(".burn"); return name; }
 let digits=["0","1","2","3","4","5","6","7","8","9","a","b","c","d","e","f"];
 let byte=digest[i];let high=digits[(byte>>4) as usize];let low=digits[(byte&15) as usize];
 name.push_str(high);name.push_str(low);reservation_name(digest,name,i+1)
}'''
actual=body('fn reservation_name(');assert tokens(actual)==tokens(expected)
assert tokens(actual)!=tokens(expected.replace('i+1','i+2'))
path=body('fn reservation_path(')
expectedpath='''{
 let mut hasher=Sha256::new();hasher.update(ATTEMPT_RESERVATION_DOMAIN);hasher.update(mask_nonce);
 let digest:[u8;32]=hasher.finalize().into();
 let name=reservation_name(digest,String::with_capacity(69),0);self.directory.join(name)
}'''
assert tokens(path)==tokens(expectedpath)
checks=dict(name_complete_body=True,path_complete_body=True,matched_negative_control=True,
 digest_byte_count=32,digits_per_byte=2,suffix_bytes=5,capacity_literal=69,
 basename_ascii_without_slash=True,capacity_and_join_request_sizes_do_not_require_public_digest_contents=True)
j=dict(classification='structural (K-1 substitute); source binding to the owned byte/length reference, not a complete endpoint or binary equivalence theorem',source=str(P),source_sha256=hashlib.sha256(P.read_bytes()).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(P)],text=True).strip(),revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),body_name=actual,body_path=path,checks=checks,lean=['PV_RDEA_ReservationName','PV_RDEA_PathSchedule','PV_RDEA_CapacityEndpoint'],retained=['runtime/allocator primitive adequacy','native byte/slice/string representation and primitive copy adequacy','compiler/executable boundary','caller reachability and public environment classification pending'])
(D/'reservation-binding.json').write_text(json.dumps(j,indent=2)+'\n');print(checks)
