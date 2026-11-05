from pathlib import Path
import json,re,lzma,hashlib
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
def read(n):return json.loads((E/n).read_text())
# Freeze prior successful stage, preserving its checks rather than relabeling.
for src,dst in [('NGX_CLOSED.json','NGX_CLOSED_STAGE2.json'),('NGX_COMBINED_IMPORT.lean','NGX_STAGE2_IMPORT.lean.txt')]:
 if not(E/dst).exists():(E/dst).write_bytes((E/src).read_bytes())
p=E/'NGX_SCAN_STAGE2.jsonl.xz'
if not p.exists():
 raw=(E/'NGX_LOADED_scan.jsonl').read_bytes();p.write_bytes(lzma.compress(raw,preset=6));(E/'NGX_SCAN_STAGE2.jsonl.sha256').write_text(sha(raw)+'\n')
s=(E/'NGX_stage2_validate.py').read_text()
s=s.replace("(E/'NGX_LOADED_scan.jsonl').read_text().splitlines()","lzma.decompress((E/'NGX_SCAN_STAGE2.jsonl.xz').read_bytes()).decode().splitlines()")
s=s.replace("sha((E/(module+'.lean')).read_bytes())==r['source_hashes']['NGX_generated/'+module+'.lean']","sha((E/('NGX_STAGE2_IMPORT.lean.txt' if module=='NGX_COMBINED_IMPORT' else module+'.lean')).read_bytes())==r['source_hashes']['NGX_generated/'+module+'.lean']")
s=s.replace("closed=read('NGX_CLOSED.json')","closed=read('NGX_CLOSED_STAGE2.json')")
(E/'NGX_stage2_validate.py').write_text(s)
selected=read('NGX_STAGE2_TARGETS.json')|{'NGX_PrefixGeometry':'NGX_L047','NGX_PrefixSource':'NGX_L048','NGX_PrefixCarrier':'NGX_L054','NGX_SamplerJoin':'NGX_L051','NGX_RunBind':'NGX_L057','NGX_Validated':'NGX_L059','NGX_SamplerStages':'NGX_L060','NGX_ValidatedTrace':'NGX_L062','NGX_BeginDomains':'NGX_L063'}
roots={'AspisR1.RPx_Deployed.deployed'}
for module,attempt in selected.items():
 r=read(attempt+'/receipt.json');assert r['exit_status']==0
 assert sha((E/(module+'.lean')).read_bytes())==r['source_hashes']['NGX_generated/'+module+'.lean']
 roots.update(line.split("'")[1]for line in r['print_axioms'])
imports=['NGK_COMBINED_IMPORT','NGT_COMBINED_IMPORT']+list(selected)
(E/'NGX_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n'for m in imports)+''.join('#print axioms '+n+'\n'for n in sorted(roots)))
base={r['module']:r['imports']for r in map(json.loads,(E/'NGX_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for r in map(json.loads,(E.parent/'transcript-scalars-20261105/NGT_EXPECTED_IMPORTS.jsonl').read_text().splitlines()):
 if r['module']in base:assert base[r['module']]==r['imports'],r['module']
 else:base[r['module']]=r['imports']
for module in selected|{'NGX_COMBINED_IMPORT':None}:base[module]=['Init']+re.findall(r'^import ([\w.]+)',(E/(module+'.lean')).read_text(),re.M)
(E/'NGX_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=i))+'\n'for n,i in sorted(base.items())))
groups=read('NGX_AUDIT_ROOTS.json')['groups'][:2];groups.append(sorted(roots));(E/'NGX_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups),indent=1))
(E/'NGX_STAGE3_TARGETS.json').write_text(json.dumps(selected,indent=1));print('roots',len(roots))
closed=read('NGX_CLOSED_STAGE2.json');common=dict(status='CLOSED',form='ruling (y) hybrid; bottom-up same-value producer/leaf association',inner_hypotheses_remaining=[],trust='P6/D188 option-A semantic transport RECLASSIFICATION; retained ABI/compiler/library/Aeneas/source-to-ELF. Digest value remains P1/RuntimeSyscall. No trust added.',KMX_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
wire='crates/aspis-r1-cost-probe/src/r1_wire.rs::';sampler='crates/aspis-r1-cost-probe/src/sampler.rs::'
closed['functions'].append(common|dict(function=wire+"Prefix<'a>::parse",rows=['TX1:138'],domain='Every live immutable bytes borrow length<=57607. Every actual record child check, all11 arbitrary WireError payloads and failures retained; successful SAME root/windows at exact offsets. No accepted input premise.',native_positive=['NGX_K023'],matched_control=['NGX_K025'],lean_root='AspisR1.NGX_PrefixSource.source',domain_roots=['AspisR1.NGX_PrefixGeometry.next','AspisR1.NGX_PrefixGeometry.terminal','AspisR1.NGX_PrefixCarrier.producer_domain'],carrier_roots=['AspisR1.NGX_PrefixCarrier.fields','AspisR1.NGX_PrefixCarrier.full_result'],internal_edges=['TX1:152'],modifies='none; no digest/protocol events',association='NGX_PREFIX_PACKET.md'))
for row,name,root,positive,negative,edges in [
 ('TX1:162','qm31_div_pass','pass_emitted',[21,29,31,33,37],[22,30,32,34,38],[]),
 ('TX1:161','qm31_digits','digits_emitted',[15,17,39],[16,18,40],['TX1:162']),
 ('TX1:163','qm31_sample','sample',[19],[20],['TX1:161','TX1:010'])]:
 closed['functions'].append(common|dict(function=sampler+name,rows=[row],domain='Every same borrowed block32; arbitrary u32 words. Native reverse index/remainder and four-pass/packing domains are derived from initialization, previous cell and callback control. No selected sampler Result or whole-function success is a premise.',native_positive=[f'NGT_K{i:03}'for i in positive],matched_control=[f'NGT_K{i:03}'for i in negative],native_provider='evidence/transcript-scalars-20261105; immutable committed source revalidated by NGX_NGT_REVALIDATION.json',lean_root='AspisR1.NGX_SamplerStages.'+root,domain_roots=['AspisR1.NGX_SamplerStages.pass_induction','AspisR1.NGX_SamplerStages.digits_induction','AspisR1.NGX_SamplerJoin.total'],internal_edges=edges,modifies='pure values; no runtime digest/protocol event',association='NGX_SAMPLER_PACKET.md'))
closed['functions'].append(common|dict(function=wire+'SemanticTranscript<H>::semantic_validated',rows=['TX1:145'],domain='SAME valid token/transcript borrow with frame length5..3717; arbitrary rowu8, state32, hash, cursor and frame bytes. Row>24 rejects before child. Valid row reaches sample with <=24; arbitrary block32 is in sampler domain. All exact Result/state/error/effect branches.',native_positive=['NGX_K027'],matched_control=['NGX_K028'],lean_root='AspisR1.NGX_Validated.source',domain_roots=['AspisR1.NGX_Validated.sample_domain','AspisR1.NGX_SamplerJoin.total'],ordered_effect_roots=['AspisR1.NGX_ValidatedTrace.rejected','AspisR1.NGX_ValidatedTrace.wrong_order','AspisR1.NGX_ValidatedTrace.returned'],internal_edges=['TX1:144','TX1:148','TX1:149','TX1:163'],modifies='exact sample state/cursor and same hash; same read block determines canonical sample; no extra event',association='NGX_BRIDGES.md'))
(E/'NGX_CLOSED.json').write_text(json.dumps(closed,indent=1))
