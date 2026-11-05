"""Check frozen byte spans, reverse the one-word oracle erasure, and inspect full native membership coverage."""
from pathlib import Path
import json,hashlib,lzma,re
E=Path(__file__).resolve().parent;P=E.parent/'transcript-queries-20261105';B=E.parent/'transcript-queries2-20261105'
frozen=json.loads(lzma.decompress((P/'NGQ_FROZEN_INPUTS.json.xz').read_bytes()))
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
transcript=frozen['crates/aspis-r1-cost-probe/src/transcript.rs'];r0=frozen['crates/aspis-core/src/r0_transcript.rs'];checks=[]
for r in json.loads((P/'NGQ_PAIR_CUTS.json').read_text()):
 cut=transcript[r['source_start']:r['source_end']];assert sha(cut)==r['sha256'];assert cut.count('hash.digest')==2
 checks.append(dict(kind='eager pair',stage=r['stage'],sha256=sha(cut),source_start=r['source_start'],source_end=r['source_end']))
r=json.loads((P/'NGQ_OUTER_CUT.json').read_text());cut=r0[r['start']:r['end']];assert sha(cut)==r['sha256'];checks.append(dict(kind='outer iteration',sha256=sha(cut),source_start=r['start'],source_end=r['end']))
for row in json.loads((B/'NHB_SOURCE_CORRESPONDENCE.json').read_text())['functions']:
 start=r0.index(row['needle']);i=r0.index('{',start)+1;depth=1
 while depth:depth+=(r0[i]=='{')-(r0[i]=='}');i+=1
 assert sha(r0[start:i])==row['frozen']['sha256'];checks.append(dict(kind='sampler source body',function=row['needle'],sha256=sha(r0[start:i])))
source=(B/'NHB_K053/sources/NHB_src/crates/aspis-core/src/NHB_harness.rs').read_text()
a=source.index('            if self.accepted_len == QUERY_COUNT');b=source.index('\n false\n }',a);body=source[a:b]
old='self.accepted[..self.accepted_len].contains(&candidate)';new='NHB_member_logged(&self.accepted[..self.accepted_len],&candidate,self.draws,reply,window,log)'
assert body.count(new)==1;restored=body.replace(new,old)
a=r0.index('            if self.accepted_len == QUERY_COUNT');b=r0.index('\n        }\n        false',a)
assert restored==r0[a:b];checks.append(dict(kind='word iteration reverse-erasure',frozen_sha256=sha(r0[a:b]),native_source_sha256=sha(source),log_is_local=True))
for row in json.loads((E/'NHK_FIXED_PROGRESS.json').read_text()):
 n=row['length'];s=(E/row['positive']/'sources/NHK_src/crates/aspis-core/src/NHK_harness.rs').read_text()
 assert f'let result=a[..{n}].contains(&x);' in s
 indices=[int(x) for x in re.findall(r'\(a\[(\d+)\]==x\)',s)]
 assert indices==list(range(n)),(n,indices)
 assert 'kani::requires' not in s and 'kani::assume' not in s and 'static ' not in s
 assert re.search(r'fn NHK_contains\(a:&\[u32;22\],x:u32\)->bool',s)
 checks.append(dict(kind='fixed native membership / both reference windows',length=n,sha256=sha(s),indices=indices,full_raw_u32_domain=True,empty_external_modifies=True))
result=dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',checks=checks,source_checks=True,whole_original_emission_claimed=False,reviewed_reference_route='ah',sampler_shape='one native iteration + raw local windows + child substitution + word/block induction',event_order='absorb then8 ordered block/advance pairs, sampler, successful22 trace arguments')
(E/'NHK_CORRESPONDENCE.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(source_checks=True,checked_cuts=len(checks))))
