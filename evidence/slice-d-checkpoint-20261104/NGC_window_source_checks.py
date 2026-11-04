from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());s=x['crates/aspis-r1-cost-probe/src/NGC_windows.rs'];src=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
def body(t,signature):
 a=t.index('{',t.index(signature));b=a+1;d=1
 while d:d+=(t[b]=='{')-(t[b]=='}');b+=1
 return t[a+1:b-1]
def norm(t):return re.sub(r'\s+','',t)
def check(t):
 b=body(src,'pub fn checkpoint<')
 b=b.replace('let mut out=Vec::with_capacity(checkpoint_size(p.variant));','let mut out=Recorder::new(checkpoint_size(p.variant),selected);').replace('hash.digest(&[proof])','digest_control(0,proof.len(),out.count,digests)').replace('hash.digest(&[public])','digest_control(1,public.len(),out.count,digests)').replace('hash.digest(&[b"UNPROVED:R1:checkpoint",&out])','digest_control(2,out.len(),out.count,digests)').replace('put(&mut out,','put_control(&mut out,').replace('put_k(&mut out,','put_k_control(&mut out,')
 assert norm(body(t,'fn checkpoint_control('))==norm(b),'checkpoint control erasure'
 assert norm(body(src,'fn finish(&self'))==norm('for (i,w) in weights.iter_mut().enumerate(){*w=self.value(i);}'),'frozen finish body'
 assert norm(body(t,'fn finish_window('))==norm('let mut iter=weights.iter_mut().enumerate();let (i,w)=iter.nth(index).unwrap();*w=b.value(i);iter.len()'),'one native arbitrary-cursor assignment'
 return dict(checkpoint_frozen_body_sha256=hashlib.sha256(body(src,'pub fn checkpoint<').encode()).hexdigest(),finish_frozen_body_sha256=hashlib.sha256(body(src,'fn finish(&self').encode()).hexdigest(),checksum_domain_bytes=22)
r=check(s);controls=[]
for label,old,new in [('finish-value-index','*w=b.value(i)','*w=b.value(0)'),('finish-cursor','iter.nth(index)','iter.nth(0)'),('checkpoint-hash-order','digest_control(0,proof.len()','digest_control(1,proof.len()'),('checkpoint-weight-argument','put_k_control(&mut out,a.power)','put_k_control(&mut out,K::ZERO)')]:
 assert old in s,label
 try:check(s.replace(old,new))
 except AssertionError:controls.append(label)
 else:raise AssertionError('accepted mutation '+label)
r.update(status='PASS',native_input_sha256=hashlib.sha256((E/'NGC_NATIVE_INPUTS.json').read_bytes()).hexdigest(),controls_rejected=controls,scope='Control and one-window source association only; chronological hash arguments are fixed by the exact frozen call expressions, data values by separate codecs/Lean laws; no checkpoint row closure')
(E/'NGC_WINDOW_ASSOCIATION.json').write_text(json.dumps(r,indent=1)+'\n');print('PASS',len(controls),'window/source mutations')
