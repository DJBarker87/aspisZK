"""Validate focused receipts and freeze the packet manifest; does not rerun Lean."""
import hashlib, json, pathlib, re, subprocess
packet = pathlib.Path(__file__).resolve().parents[1]
root = pathlib.Path(__file__).resolve().parents[6]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
modules = ['ActualScaledDivisorMonic', 'ActualRawModCostBound', 'RawExtractorCostLedger', 'RawExtractorCostComposedV2']
entries = []
for module in modules:
    directory = packet/module
    r = json.loads((directory/'receipt.json').read_text())
    source = pathlib.Path(r['command'][-1])
    assert r['exit_status'] == 0
    assert sha(source) == r['source_sha256']
    assert r['peak_rss_bytes'] < 6*1024**3
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", r['axioms_result'], re.S)
    assert reports
    for theorem, axioms in reports:
        assert set(re.findall(r'[\w.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}, (theorem,axioms)
    imports = {}
    for imported in re.findall(r'^import (\S+)', source.read_text(), re.M):
        obj = next(pathlib.Path(x)/(imported.replace('.','/')+'.olean') for x in r['lean_path'].split(':') if (pathlib.Path(x)/(imported.replace('.','/')+'.olean')).exists())
        src = root/'docs/research/100bit-spend-path-20261013/lean'/(imported+'.lean')
        imports[imported] = dict(object_path=str(obj),object_sha256=sha(obj),source=str(src.relative_to(root)) if src.exists() else None,source_sha256=sha(src) if src.exists() else None)
    entry = {k:r[k] for k in ['module','source_revision','source_sha256','object_sha256','exit_status','wall_seconds','peak_rss_bytes','process_swap_count','swap_bytes','swap_note']}
    entry.update(source=str(source.relative_to(root)),receipt=f'{module}/receipt.json',receipt_sha256=sha(directory/'receipt.json'),axioms_result={t:re.findall(r'[\w.]+',a) for t,a in reports},direct_imports=imports)
    entries.append(entry)
manifest = dict(schema='focused-extractor-proof-packet-v1',status='checked_conditional_composition',source_state='Revision identifies the parent checkout; exact tested working-tree sources and imports are pinned by SHA-256 below.',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),modules=entries,failed_attempts=['RawExtractorCostLedger-missing-import/receipt.json','RawExtractorCostComposed-missing-import/receipt.json','RawExtractorCostComposed/receipt.json'],scope='Conditional cost/safety/failure composition for the exact no-model experiment. Implementation accounting hypotheses remain open; not a release or unconditional closure of M10.',rules_file='/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/local-lean.txt',object_directory='/tmp/cx-m10-extractor-cost-resume-20261020-objects',verification='Focused dependency-order compiles and one successful source axiom audit per target; no unchanged full regression.',historical_preflight='preflight.json and vm_stat.txt belong to the superseded blocked draft; current commands use the revised mkdir/process gate.')
(packet/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Validated',len(entries),'successful targets; only standard axioms')
