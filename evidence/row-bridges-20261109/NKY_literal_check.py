from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
x=json.loads((E/'NKY_LITERAL_INPUT.json').read_text());raw=subprocess.check_output(['git','show','HEAD:'+x['path']]);assert hashlib.sha256(raw).hexdigest()==x['sha256'];assert x['excerpt']in raw.decode()
s=x['excerpt'];a=s.index('def\n  pool_');b=s.index('/-- [aspis_statement::',a)
body=s[a:b].replace('pool_v1.pair_forest_semantic_terminal.append_levels_packed_selector_tensor_loop.body','body').replace('pool_v1.pair_forest_semantic_terminal.append_level_packed_selector_tensor','child').replace('aspis_core.field.QM31','FIq_Native.field.QM31').replace('aspis_core.field.M31','U32')
body=body.replace('def\n  body','def body (child : U64 → Usize → NJX_DigestCohort.D → NJX_DigestCohort.O → FIv_NativeArithmetic.NQ → Result NKY_LevelCarrier.Pair)')
assert body in (E/'NKY_LevelsLiteral.lean').read_text()
p='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';rust=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
a=rust.index('fn append_levels_packed_selector_tensor(');b=rust.index('\n}\n',a)+2;fn=rust[a:b]
assert fn.endswith('    (local0, local12)\n}');assert 'return 'not in fn and '?'not in fn
out=dict(passed=True,retained_emission=x['path'],retained_sha256=x['sha256'],body_port='exact retained body under explicit child slot and coherent field/type namespace transport',original_combinator='Result/ControlFlow loop; current partial_fixpoint port proved equal to LevelsFrame by finite induction',bc=dict(frozen_function_sha256=hashlib.sha256(fn.encode()).hexdigest(),post_loop='tuple tail expression; no explicit return or question-mark exit',affected=False),coherent_environment='NKY_L001 found no declaration with the original append_levels/append_level suffix; NKY supplies a literal port, not an existing-FIq alias proof')
(E/'NKY_LITERAL_CHECK.json').write_text(json.dumps(out,indent=1)+'\n');print('literal-body and post-loop checks PASS')
