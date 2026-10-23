#!/usr/bin/env python3
"""Pack four exact array-copy reads in the native transition decoder."""
from pathlib import Path
import re,json,hashlib,sys
from generated_syntax import clean
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
p=B/'lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean';source=clean(p.read_text());name='pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1'
a=source.index('def '+name+' (');b=source.index('\ndef ',a+4);original=source[a:b];decl=original;expansions={}
pattern=r'(?m)^( +)let (r\d*) ← core.array.TryFromArrayCopySlice.try_from (\d+)#usize core.marker.CopyU8 (s\d*)\n +let (a\d*) ← atomic_statement.unwrap_fixed_slice \(Array.Insts.CoreMarkerCopy \3#usize core.marker.CopyU8\) \2'
def pack(m):
 replacement=m[1]+'let '+m[5]+' ← AspisS6NativeSnapshotReadArray.read_array '+m[3]+'#usize '+m[4]
 expansions[replacement.strip()]=m[0];return replacement
assert len(re.findall(pattern,decl))==4
decl=re.sub(pattern,pack,decl)
normalize=lambda s:re.sub(r'\s+','',s)
assert normalize('\n'.join(expansions.get(line.strip(),line) for line in decl.splitlines()))==normalize(original)
decl=decl.replace('def '+name+' (','def decode (',1)
out='import S6NativeLateChildDecodeV1\nimport S6NativeSnapshotReadArrayV1\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnoncomputable section\nnamespace AspisS6NativeLateDecoderFactored\nopen AspisR1TerminalDecoder\nopen pool_v1.pair_tree_profile\n\n'+decl+'\n\n'+'theorem decode_source (bytes : Slice U8) :\n    decode bytes=decode_pool_v1_pair_late_public_statement_boxed_v1 bytes := by\n  unfold decode decode_pool_v1_pair_late_public_statement_boxed_v1\n  unfold AspisS6NativeSnapshotReadArray.read_array\n  simp only [bind_assoc_eq]\n  run_tac do\n    for _ in [:8] do\n      let g ← Lean.Elab.Tactic.getMainGoal\n      let t ← g.getType\n      let names := t.getUsedConstants.filter fun n =>\n        let s := n.toString\n        (s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeLateDecoderFactored.") &&\n        (s.splitOn ".").any (fun c => c.startsWith "match_")\n      if names.isEmpty then break\n      let ids := names.map Lean.mkIdent\n      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))\n  dsimp only\n  all_goals with_reducible rfl\n\n#print axioms decode_source\nend AspisS6NativeLateDecoderFactored\n'
q=S/'S6NativeLateDecoderFactoredV1.lean';m=E/'s6-native-late-decoder-factoring-v1.json';meta=dict(schema='focused-extractor-proof-packet-v1',original_native_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_fragment_sha256=hashlib.sha256(original.encode()).hexdigest(),candidate_sha256=hashlib.sha256(out.encode()).hexdigest(),packed_array_sequences=4,textual_reexpansion_equal=True,qualification='Full original native carriers and all source callees retained; kernel full Result equality required. No Rust/SDK/release closure claim.')
if '--check' in sys.argv:assert q.read_text()==out and json.loads(m.read_text())==meta
else:q.write_text(out);m.write_text(json.dumps(meta,indent=2)+'\n')
