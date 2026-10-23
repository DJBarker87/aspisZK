#!/usr/bin/env python3
"""Factor exact native snapshot sequences; no Rust or source callee rewrite."""
from pathlib import Path
import re,json,hashlib,sys
from generated_syntax import clean
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
p=B/'lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean'
source=clean(p.read_text());name='pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1'
a=source.index('def '+name+' (');b=source.index('\ndef ',a+4);original=source[a:b];decl=original
expansions={}
pattern=r'(?m)^( +)let (r\d*) ← core.array.TryFromSharedArraySlice.try_from 32#usize (s\d*)\n +let (a\d*) ← atomic_statement.unwrap_fixed_slice \(Shared0T.Insts.CoreMarkerCopy \(Array Std.U8 32#usize\)\) \2\n +let (r\d*) ← atomic_statement.decode_digest_canonical \4'
def digest(m):
 replacement=m[1]+'let '+m[5]+' ← AspisS6NativeSnapshotReadDigest.read_digest '+m[3]
 expansions[replacement.strip()]=m[0];return replacement
assert len(re.findall(pattern,decl))==21
decl=re.sub(pattern,digest,decl)
pattern=r'(?m)^( +)let (r\d*) ← core.array.TryFromArrayCopySlice.try_from (\d+)#usize core.marker.CopyU8 (s\d*)\n +let (a\d*) ← atomic_statement.unwrap_fixed_slice \(Array.Insts.CoreMarkerCopy \3#usize core.marker.CopyU8\) \2'
def array(m):
 replacement=m[1]+'let '+m[5]+' ← AspisS6NativeSnapshotReadArray.read_array '+m[3]+'#usize '+m[4]
 expansions[replacement.strip()]=m[0];return replacement
assert len(re.findall(pattern,decl))==4
decl=re.sub(pattern,array,decl)
normalize=lambda text:re.sub(r'\s+','',text)
expanded='\n'.join(expansions.get(line.strip(),line) for line in decl.splitlines())
assert normalize(expanded)==normalize(original)
lines=decl.splitlines();parts={}
for j in [0,4,8,12,16]:
 start=160+32*j;ix=[i for i,l in enumerate(lines) if re.search(r'let s\d+ ←.*bytes \{ start := '+str(start)+r'#usize,',l)];assert len(ix)==1
 begin=ix[0];indent=len(lines[begin])-len(lines[begin].lstrip())
 end=next(i for i in range(begin+1,len(lines)) if len(lines[i])-len(lines[i].lstrip())==indent-2 and lines[i].lstrip().startswith('| core.ops.control_flow.ControlFlow.Break'))
 parts[j]=dict(begin=begin,end=end,indent=indent)
params=lambda j:['val']+['val'+str(i+1) for i in range(j)]
call=lambda j:'part_'+str(j)+' bytes '+' '.join(params(j))
chunks={}
for j in reversed(list(parts)):
 d=parts[j];fragment=lines[d['begin']:d['end']];nextj=j+4
 if nextj in parts:
  q=parts[nextj];lo=q['begin']-d['begin'];hi=q['end']-d['begin'];fragment=fragment[:lo]+[' '*q['indent']+call(nextj)]+fragment[hi:]
 chunks[j]='\n'.join('  '+l[d['indent']:] for l in fragment)
 check='\n'.join(fragment)
 if nextj in parts:
  q=parts[nextj];check=check.replace(' '*q['indent']+call(nextj),'\n'.join(lines[q['begin']:q['end']]),1)
 assert normalize(check)==normalize('\n'.join(lines[d['begin']:d['end']]))
root=lines[1:parts[0]['begin']]+[' '*parts[0]['indent']+call(0)]+lines[parts[0]['end']:]
assert normalize('\n'.join(root).replace(' '*parts[0]['indent']+call(0),'\n'.join(lines[parts[0]['begin']:parts[0]['end']]),1))==normalize('\n'.join(lines[1:]))
out='''import S6NativeSnapshotReadArrayV1
import Mathlib.Tactic.CongrExclamation
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisS6NativeSnapshotDecoderFactored
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

'''
result='Result (core.result.Result PoolV1PairLiveSnapshotV1 PoolV1PairLiveSnapshotErrorV1)'
for j in reversed(list(parts)):
 out+='def part_'+str(j)+' (bytes : Slice U8) ('+' '.join(params(j))+' : Array aspis_core.field.M31 8#usize) : '+result+' := do\n'+chunks[j]+'\n\n'
out+='def decode (bytes : Slice U8) : '+result+' := do\n'+'\n'.join(root)+'\n\n'
# Independently factor the unchanged original body. The original-to-unpacked
# equality needs no monad reassociation; packed/unpacked joins are local.
rawlines=original.splitlines();rawparts={}
for j in parts:
 start=160+32*j;begin=next(i for i,l in enumerate(rawlines) if re.search(r'let s\d+ ←.*bytes \{ start := '+str(start)+r'#usize,',l));indent=len(rawlines[begin])-len(rawlines[begin].lstrip());end=next(i for i in range(begin+1,len(rawlines)) if len(rawlines[i])-len(rawlines[i].lstrip())==indent-2 and rawlines[i].lstrip().startswith('| core.ops.control_flow.ControlFlow.Break'));rawparts[j]=dict(begin=begin,end=end,indent=indent)
for j in reversed(list(rawparts)):
 d=rawparts[j];fragment=rawlines[d['begin']:d['end']]
 if j+4 in rawparts:
  q0=rawparts[j+4];lo=q0['begin']-d['begin'];hi=q0['end']-d['begin'];fragment=fragment[:lo]+[' '*q0['indent']+call(j+4).replace('part_','unpacked_part_',1)]+fragment[hi:]
 out+='def unpacked_part_'+str(j)+' (bytes : Slice U8) ('+' '.join(params(j))+' : Array aspis_core.field.M31 8#usize) : '+result+' := do\n'+'\n'.join('  '+l[d['indent']:] for l in fragment)+'\n\n'
rawroot=rawlines[1:rawparts[0]['begin']]+[' '*rawparts[0]['indent']+call(0).replace('part_','unpacked_part_',1)]+rawlines[rawparts[0]['end']:]
out+='def unpacked_decode (bytes : Slice U8) : '+result+' := do\n'+'\n'.join(rawroot)+'\n\n'
matcher='''  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeSnapshotDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl
'''
for j in reversed(list(parts)):
 out+='theorem part_'+str(j)+'_eq (bytes : Slice U8) ('+' '.join(params(j))+' : Array aspis_core.field.M31 8#usize) :\n    '+call(j)+'=unpacked_'+call(j)+' := by\n  unfold part_'+str(j)+' unpacked_part_'+str(j)+'\n'
 if j+4 in parts:out+='  simp only [part_'+str(j+4)+'_eq]\n'
 out+='  unfold AspisS6NativeSnapshotReadDigest.read_digest\n  try unfold AspisS6NativeSnapshotReadArray.read_array\n  simp only [bind_assoc_eq]\n'+matcher+'\n'
out+='theorem unpacked_source (bytes : Slice U8) :\n    unpacked_decode bytes=decode_pool_v1_pair_live_snapshot_v1 bytes := by\n  unfold unpacked_decode decode_pool_v1_pair_live_snapshot_v1\n  unfold unpacked_part_0 unpacked_part_4 unpacked_part_8 unpacked_part_12 unpacked_part_16\n'+matcher+'\n'
out+='theorem packed_unpacked (bytes : Slice U8) :\n    decode bytes=unpacked_decode bytes := by\n  unfold decode unpacked_decode\n  simp only [part_0_eq]\n  unfold AspisS6NativeSnapshotReadDigest.read_digest\n  simp only [bind_assoc_eq]\n'+matcher+'\n'
out+='theorem decode_source (bytes : Slice U8) :\n    decode bytes=decode_pool_v1_pair_live_snapshot_v1 bytes :=\n  (packed_unpacked bytes).trans (unpacked_source bytes)\n\n#print axioms decode_source\nend AspisS6NativeSnapshotDecoderFactored\n'
q=S/'S6NativeSnapshotDecoderFactoredV1.lean';m=E/'s6-native-snapshot-decoder-factoring-v1.json'
meta={'schema':'focused-extractor-proof-packet-v1','original_native_source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'source_fragment_sha256':hashlib.sha256(original.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(out.encode()).hexdigest(),'parts':{str(k):v for k,v in parts.items()},'packed_digest_sequences':21,'packed_array_sequences':4,'textual_reexpansion_equal':True,'qualification':'Exact native cast/unwrap/decode sequences and continuations; full original native carriers/callees retained. Kernel full Result equality is required. No Rust changes, opaque replacement, SDK or release closure.'}
if '--check' in sys.argv:assert q.read_text()==out and json.loads(m.read_text())==meta
else:q.write_text(out);m.write_text(json.dumps(meta,indent=2)+'\n')
