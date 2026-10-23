#!/usr/bin/env python3
"""Inspect saved GOTO source only; certify actual normal cleanup after whole-copy.
This checks operation order/control, not the semantics of the GOTO extractor or
Rust move/drop lowering. SDK/allocator/runtime trust/domain limits stay explicit.
"""
from pathlib import Path
import json,re,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();O=H/'sdk-native-cleanup-order-v1';O.mkdir(exist_ok=False)
raw=H/'receipts/sdk-native-cleanup-goto-inventory-v1/stdout.log';rows=raw.read_text().splitlines();a=next(i for i,s in enumerate(rows) if s.startswith('adapter::stage1 /*'));b=next(i for i in range(a+1,len(rows)) if rows[i].startswith('^^^^^^^^'));body=rows[a:b]
assert sum('copy_from_slice' in s and 'CALL ' in s for s in body)==1
start=next(i for i,s in enumerate(body) if 'copy_from_slice' in s and 'CALL ' in s)
# The actual compiled successful suffix jumps to its shared return label.
end=next(i for i in range(start+1,len(body)) if re.search(r'\bGOTO 160\s*$',body[i]))
suffix=body[start:end+1];calls=[];gotos=[]
for line in suffix:
 s=re.sub(r'^\s*(?:\d+:\s*)?','',line)
 if not s or s.startswith('//'):continue
 if s.startswith('CALL '):calls.append(s)
 elif s.startswith('GOTO '):
  assert re.fullmatch(r'GOTO \d+',s);gotos.append(int(s.split()[1]))
 else:assert s.startswith(('DECL ','ASSIGN ','DEAD ','SKIP')),s
assert gotos==[152,153,154,155,156,157,160]
assert len(calls)==6
roles=[]
for line in calls[1:]:
 assert 'drop_in_place' in line
 m=re.search(r'::var_\d+::([a-z_]+)\)\)$',line);assert m,line;roles.append(m[1])
assert roles==['checkpoint','proof_data','statement','public_data','checkpoint_data']
expected_types=['alloc3vec3Vech','4cell3RefQSh','PoolV1PairForestTerminalStatementV1','4cell3RefQSh','4cell6RefMutQSh']
for line,t in zip(calls[1:],expected_types):assert t in line
ret=next(i for i in range(end+1,len(body)) if re.match(r'\s*160: SET RETURN VALUE ',body[i]))
assert '::var_0' in body[ret]
post=[re.sub(r'^\s*(?:\d+:\s*)?','',s) for s in body[ret+1:]]
assert all(not s or s.startswith(('//','DEAD ','GOTO 161','END_FUNCTION')) for s in post),post[-5:]
(O/'native-stage1-goto.txt').write_text('\n'.join(body)+'\n');(O/'normal-copy-cleanup-goto.txt').write_text('\n'.join(suffix)+'\n')
(O/'certificate.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',roles=roles,call_type_fragments=expected_types,unconditional_jumps=gotos,normal_calls=calls,source_sha256=sha(H/'sdk-shared-prefix-success-bytes-pair-v1/src/lib.rs'),program_sha256=sha(H/'sdk-native-success-bytes-pair-v1/ready.out'),raw_goto_source_sha256=sha(raw),source_fragment_sha256=sha(O/'normal-copy-cleanup-goto.txt'),runner_sha256=sha(Path(__file__)),claim='Actual native compiled normal post-copy suffix invokes precisely Vec reply, Ref proof, Box statement, Ref public, RefMut checkpoint drop glues in the checked direct-cleanup order. No branch or additional call lies between copy and shared return.',remaining='Operation/control binding only; typed-value relocation/move/drop and whole-source runtime/ABI/allocator interpretation remain explicit. Combine exact direct frame and actual region bindings through the kernel footprint rules. Not whole S2.'),indent=2)+'\n')
print(json.dumps(dict(roles=roles,unconditional_jumps=gotos,output=str(O))))
