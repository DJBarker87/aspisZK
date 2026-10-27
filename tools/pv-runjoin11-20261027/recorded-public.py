#!/usr/bin/env python3
"""Read pinned fixture bytes; emit literal public/transition carriers, no compiler theorem."""
import hashlib,json,pathlib,struct,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[2]; evidence=root/'evidence/pv-runjoin11-20261027'
rev='ed1c1cef71'; sources={}
def arr(values,bits=32):
 return 'Array.make '+str(len(values))+'#usize ['+', '.join(str(x)+'#u'+str(bits) for x in values)+']'
def dig(b):
 v=list(struct.unpack('<8I',b));assert all(x<2147483647 for x in v);return arr(v)
def nested(b):return 'Array.make 20#usize [\n    '+',\n    '.join(dig(b[32*i:32*i+32]) for i in range(20))+'\n  ]'
def u(b):return int.from_bytes(b,'little')
for variant in ['transfer','withdrawal']:
 p='results/r0-e2e-20261009/final-fixtures/'+variant+'.public.bin'
 b=subprocess.check_output(['git','show',rev+':'+p],cwd=root);assert len(b)==1880
 sources[variant]={'revision':subprocess.check_output(['git','rev-parse',rev],cwd=root,text=True).strip(),'path':p,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 t=b[144:1664];s=t[32:832];a=t[832:];pmt=b[1664:]
 assert len(s)==800 and len(a)==688 and len(pmt)==216
 assert s[48:80]==pmt[8:40]==bytes([1])*32
 assert s[80:112]==pmt[40:72]==bytes([5])*32
 assert u(s[112:120])==u(s[120:128])==0 and u(a[8:16])==1
 fields=['pool := '+arr(pmt[8:40],8),'deployment_domain := '+arr(pmt[40:72],8),'anchor_sequence := '+str(u(pmt[72:80]))+'#u64','anchor_root := '+dig(pmt[80:112]),'nullifier := '+dig(pmt[112:144]),'asset_id := '+str(u(pmt[144:148]))+'#u32']
 if variant=='transfer':fields+=['recipient_commitment := '+dig(pmt[152:184])]
 else:fields+=['amount := '+str(u(pmt[148:152]))+'#u32','destination_token_account := '+arr(pmt[152:184],8)]
 fields+=['change_commitment := '+dig(pmt[184:216])]
 ns='PV_RunJoin_Recorded'+variant.title()
 text='import R1Z.PV_Src_NativeInput\nset_option autoImplicit false\nnamespace R1Z.'+ns+'\nopen Aeneas Aeneas.Std\n\n/-! Literal public data read from the pinned terminal bytes. No compilation\nsuccess, source decoder equation, or deployed selected-input association is claimed. -/\n\ndef publicRecord : BuilderPublicProjection.'+variant.title()+' where\n  '+'\n  '.join(fields)+'\n\ndef transition : BuilderPublicProjection.Transition where\n  live_snapshot := {\n    pool := '+arr(s[48:80],8)+'\n    deployment_domain := '+arr(s[80:112],8)+'\n    sequence := '+str(u(s[112:120]))+'#u64\n    next_pair_index := '+str(u(s[120:128]))+'#u64\n    current_root := '+dig(s[128:160])+'\n    frontier := '+nested(s[160:])+' }\n  candidate_afterstate := {\n    next_pair_index := '+str(u(a[8:16]))+'#u64\n    next_root := '+dig(a[16:48])+'\n    next_frontier := '+nested(a[48:])+' }\n\ndef publicInput : PV_Src_Public.Input := .'+variant+' publicRecord transition\n\n#print axioms publicRecord\n#print axioms transition\n#print axioms publicInput\nend R1Z.'+ns+'\n'
 out=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'/ (ns+'.lean')
 if '--check' in sys.argv:assert out.read_text()==text
 else:out.write_text(text)
 sources[variant]['lean_source']=str(out.relative_to(root));sources[variant]['lean_sha256']=hashlib.sha256(text.encode()).hexdigest()
(evidence/'recorded-public-pins.json').write_text(json.dumps(sources,indent=2)+'\n')
print(json.dumps(sources,indent=2))
