#!/usr/bin/env python3
"""Prepare a review-only verify prefix boundary; never apply/probe it."""
from pathlib import Path
import argparse,difflib,hashlib,importlib.util,json,subprocess,textwrap
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);p.add_argument('--revision',default='e5c186ba3');a=p.parse_args();revision=subprocess.check_output(['git','-C',str(R),'rev-parse',a.revision],text=True).strip()
spec=importlib.util.spec_from_file_location('cut',H.parent/'public-serializer-extraction-kit/extract.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b
file='crates/aspis-r1-cost-probe/src/r1_semantic.rs';full=subprocess.check_output(['git','-C',str(R),'show',revision+':'+file]).decode();old,*_=m.find_item(Source(full.encode()),'#[inline(never)]\npub fn verify_observed<H: Digest32>');old=old.decode();mark,*_=m.find_item(Source(old.encode()),'fn mark(obs: crate::verifier::Observer, i: u8)');mark=mark.decode();assert old.count(mark)==1
start=old.index('    let mut running = prefix.validated_record(14)?.decode_k::<1>(0)?[0];');end=old.rindex('\n}');tail=old[start:end]
assert old.index('    mark(obs, 1);')<start
helper='''fn verify_finish<H: Digest32>(public: Public<'_>, prefix: Prefix<'_>, mut transcript: SemanticTranscript<H>, challenges: Challenges, obs: crate::verifier::Observer) -> Result<Verified<H>, Error> {
'''+tail+'\n}\n'
new=old[:start]+'    verify_finish(public, prefix, transcript, challenges, obs)'+old[end:]
new=new.replace(mark+'\n','',1);modulemark=textwrap.dedent(mark)+'\n';newfull=full.replace(old,modulemark+'\n'+helper+'\n'+new,1)
assert new.count('public_transcript(public, hash, prefix.c1_root)?')==1 and new.count('wire::begin(&prefix, &mut transcript)?')==1
assert all('fn mark(' not in f for f in [helper,new]) and modulemark.startswith('fn mark(')
a.out.mkdir(parents=True,exist_ok=True)
files={'source-before.rs':full.encode(),'r1_semantic.rs':newfull.encode(),'verify_observed.rs':new.encode(),'verify_finish.rs':helper.encode(),'mark.rs':modulemark.encode(),'proposal.patch':''.join(difflib.unified_diff(full.splitlines(True),newfull.splitlines(True),fromfile='a/'+file,tofile='b/'+file)).encode()}
for n,b in files.items():(a.out/n).write_bytes(b)
audit={'classification':'REVIEW-ONLY SOURCE PROPOSAL; no application, compile or extraction probe','revision':revision,'source':file,'old_source_sha256':sha(full.encode()),'proposed_source_sha256':sha(newfull.encode()),'old_verify_sha256':sha(old.encode()),'proposed_verify_sha256':sha(new.encode()),'finish_sha256':sha(helper.encode()),'moved_tail_sha256':sha(tail.encode()),'mark_before_sha256':sha(mark.encode()),'mark_after_sha256':sha(modulemark.encode()),'mark_equivalence':'Original nested noncapturing mark body lifted to same private module name with indentation only; all cfg(feature=detail-phases) / non-detail code and every call retained, no capture/environment parameter.','tail_equivalence':'All text after mark(obs,1) and before outer function closing brace copied byte-for-byte into verify_finish. No loop/iterator/arithmetic/reseed/error/trace operation rewritten.','owned_signature':helper.split('{\n',1)[0],'ownership':'Own Public, Prefix, SemanticTranscript, Challenges, Observer. Prefix/shared external bytes and C1 root borrows do not escape public_transcript/begin in the returned owned types; their borrowed arguments may end before the helper call. All five values have no custom Drop; H:Digest32:Copy. Caller hash/bytes remain borrowed/copy-only locals. No clone, allocation or extra fallible step introduced.','prefix_order':['Prefix::parse(bytes)?','mark(obs,0)','public_transcript(public,hash,prefix.c1_root)?','wire::begin(&prefix,&mut transcript)?','mark(obs,1)','verify_finish owned transfer'],'limitations':'Intended to expose actual parse→public_transcript→begin success inversion with one real explicit tail boundary; does not prove actual rows15–26/all33/log bytes/hread, arithmetic tail, SDK/custody. Extractor/borrowchecker success not yet claimed. Lead/user source decision required before application or rewritten extraction probe.','files':{n:sha(b) for n,b in files.items()}}
(a.out/'audit.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n');print(json.dumps(audit,indent=2))
