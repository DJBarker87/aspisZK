from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=E/'NFW_prepared_native_prepare.py';s=p.read_text();assert 'fn return_block_source(' not in s
s=s.replace('fn check(facet:usize){','fn check(facet:usize){if cfg!(NFW_RETURN_BLOCK){return_block_check();return;}')
code=(E/'NFW_return_block.rs.txt').read_text();pos=s.index('# A new child module');s=s[:pos]+'code+='+repr(code)+'\n'+s[pos:];p.write_text(s)
p=E/'NFW_run.py';s=p.read_text();needle="if os.environ.get('NFW_CAPTURE_ALL'):env['RUSTFLAGS']+=' --cfg NFW_CAPTURE_ALL'";s=s.replace(needle,needle+"\n if os.environ.get('NFW_RETURN_BLOCK'):env['RUSTFLAGS']+=' --cfg NFW_RETURN_BLOCK'");p.write_text(s)
(E/'NFW_K064_REVIEW.json').write_text(json.dumps(dict(attempt='NFW_K064',disposition='TIMEOUT; no field-output credit',replacement='Same original prepared_facet5 name. Isolate only the exact final frozen record/Box return expression on an arbitrary valid pre-return state; all 11 field classes, full raw-QM31 sem fields and all variants are quantified. This removes the unrelated opening prefix and its Vec/scratch effects. NFW_PreparedFields.source is the paired adopted constructor theorem. Linking this native return-block prestate to the earlier call log remains a separate explicit obligation; no independent complete output is assumed.'),indent=1)+'\n')
