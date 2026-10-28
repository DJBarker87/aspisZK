from pathlib import Path
import re
p=Path('lean');s=Path('evidence/replay-dry8-20261026/RPz7_S6NativeAfterstateDecoderFactoredV1.lean').read_text()
(p/'NBN_AfterDecodeTypes.lean').write_text('''import S6NativeAfterstateDecoderFactoredV1
set_option autoImplicit false
noncomputable section
namespace NBN_AfterDecodeTypes
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Digest := Array U32 8#usize
abbrev Decode := Array U8 32#usize → Result (core.result.Result Digest atomic_statement.AtomicStatementError)
def NBN_Dep_DigestDecode (decode : Decode) : Prop :=
  ∀ bytes, decode bytes = atomic_statement.decode_digest_canonical bytes
end NBN_AfterDecodeTypes
''')
matcher='''  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        (s.startsWith "NBN_AfterDecode" || s.startsWith "AspisS6NativeAfterstateDecoderFactored.") &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl
'''
for k in [16,12,8,4,0]:
 name=f'NBN_AfterDecode{k:02}'
 start=s.index(f'def part_{k} ');end=s.index('\ndef ',start+5)
 text=s[start:end].strip();header=text[:text.index(' := do')];vs=list(dict.fromkeys(re.findall(r'\bval\d+\b',header)))
 # Original native/model split continuation is reused, never expanded to all20 calls.
 run=text.replace(f'def part_{k} ', 'def run (decode : Decode) ',1).replace('atomic_statement.decode_digest_canonical','decode')
 prev=None
 if k<16:
  prev=f'NBN_AfterDecode{k+4:02}'
  run=re.sub(r'(?<![\w.])part_'+str(k+4)+r'\b',prev+'.run decode',run)
 imports='import NBN_AfterDecodeTypes\n'+(f'import {prev}\n' if prev else '')
 params=header[len(f'def part_{k} '):header.index(' : Result')]
 args='bytes '+ ' '.join(vs)
 proof='  have same : decode = atomic_statement.decode_digest_canonical := funext lower\n  unfold run\n'
 if prev:proof+=f'  simp only [{prev}.source decode lower]\n'
 proof+='  rw [same]\n'+f'  unfold AspisS6NativeAfterstateDecoderFactored.part_{k}\n'+matcher
 out=imports+f'''set_option autoImplicit false
noncomputable section
namespace {name}
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NBN_AfterDecodeTypes

'''+run+f'''\n\ntheorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode)
    {params} :
    run decode {args} = AspisS6NativeAfterstateDecoderFactored.part_{k} {args} := by
'''+proof+f'''\n#print axioms source
end {name}
'''
 (p/(name+'.lean')).write_text(out)
start=s.index('def decode (');end=s.index('\n\n/-- Full Result',start);text=s[start:end].strip()
run=text.replace('def decode (','def run (child : Decode) (',1).replace('atomic_statement.decode_digest_canonical','child').replace('part_0 bytes val1','NBN_AfterDecode00.run child bytes val1')
name='NBN_AfterDecodeParent'
out=f'''import NBN_AfterDecode00
set_option autoImplicit false
noncomputable section
namespace {name}
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1TerminalDecoder pool_v1.pair_terminal NBN_AfterDecodeTypes

'''+run+'''

theorem source (child : Decode) (lower : NBN_Dep_DigestDecode child) (bytes : Slice U8) :
    run child bytes = decode_pool_v1_pair_verified_afterstate_v1 bytes := by
  have factored : run child bytes = AspisS6NativeAfterstateDecoderFactored.decode bytes := by
    have same : child = atomic_statement.decode_digest_canonical := funext lower
    unfold run
    simp only [NBN_AfterDecode00.source child lower]
    rw [same]
    unfold AspisS6NativeAfterstateDecoderFactored.decode
'''+''.join('  '+l+'\n' for l in matcher.rstrip().splitlines())+'''  exact factored.trans (AspisS6NativeAfterstateDecoderFactored.decode_source bytes)

#print axioms source
end NBN_AfterDecodeParent
'''
(p/(name+'.lean')).write_text(out)
(p/'NBN_AfterstateDecoderDependency.lean').write_text('''import NBN_AfterDecodeParent
set_option autoImplicit false
noncomputable section
namespace NBN_AfterstateDecoderDependency
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Decode := NBN_AfterDecodeTypes.Decode
abbrev NBN_Dep_DigestDecode := NBN_AfterDecodeTypes.NBN_Dep_DigestDecode
abbrev run := NBN_AfterDecodeParent.run

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode) (bytes : Slice U8) :
    run decode bytes = pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes :=
  NBN_AfterDecodeParent.source decode lower bytes

#print axioms source
end NBN_AfterstateDecoderDependency
''')
