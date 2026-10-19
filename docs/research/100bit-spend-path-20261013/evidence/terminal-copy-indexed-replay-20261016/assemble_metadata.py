#!/usr/bin/env python3
import hashlib, json, re
from pathlib import Path
E=Path(__file__).resolve().parent
X=E/'evidence-export'
sha=lambda b:hashlib.sha256(b).hexdigest()
case_rows=[]
for line in (X/'p3-results.tsv').read_text().splitlines()[1:]:
    name, proof_sha, public_sha, index, variant, exit_code=line.split('\t')
    d=X/f'p3-{name}'; out=d/'r18-output'
    cmp=json.loads((out/'comparison.json').read_text())
    inp=json.loads((out/'input-manifest.json').read_text())
    t=(d/'time.log').read_text()
    def timeval(rx, cast=float):
        m=re.search(rx,t,re.M)
        if not m: raise ValueError(rx)
        return cast(m.group(1))
    receipt={
      'record_type':'derived-per-case-run-record from exact output manifest/comparison/time log',
      'exit':int(exit_code), 'source_revision':inp['after_source_revision'],
      'harness_source_sha256':inp['harness_source_sha256'],
      'harness_binary_sha256':inp['harness_binary_sha256'],
      'baseline_elf_sha256':inp['before_elf_sha256'], 'candidate_elf_sha256':inp['after_elf_sha256'],
      'proof_sha256':inp['proof_sha256'], 'public_sha256':inp['public_sha256'],
      'expected_next_pair_index':inp['expected_next_pair_index'], 'expected_variant':inp['expected_variant'],
      'wall_seconds':timeval(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([0-9:.]+)',str),
      'max_rss_kib':timeval(r'Maximum resident set size \(kbytes\):\s*(\d+)',int),
      'swap_count':timeval(r'Swaps:\s*(\d+)',int),
      'comparison':cmp,
      'included_output_file_sha256':{p.name:sha(p.read_bytes()) for p in sorted(out.iterdir()) if p.is_file()},
      'keys_included':False,
    }
    (d/'derived-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    case_rows.append({'case':name,'pair_index':int(index),'variant':variant,'exit':int(exit_code),
       'stage1_before':cmp['before']['stage1'],'stage1_candidate':cmp['after']['stage1'],
       'stage1_delta':cmp['delta']['stage1'],'stage2_before':cmp['before']['stage2'],
       'stage2_candidate':cmp['after']['stage2'],'stage2_delta':cmp['delta']['stage2'],
       'checkpoint_equal':cmp['checkpoint_equal'],'asr8_equal':cmp['asr8_equal'],'initial_images_equal':cmp['initial_images_equal'],
       'proof_sha256':proof_sha,'public_sha256':public_sha,'max_rss_kib':receipt['max_rss_kib'],'wall_seconds':receipt['wall_seconds']})
summary={
 'scope':'isolated R18 verifier-only paired replay; no Pool CPI/settlement',
 'baseline_elf_sha256':'2c031d0040a3bf739b58591b2a20dc68f04722550fd49b79d4fd7eb8e5dfee9f',
 'candidate_elf_sha256':'d346de4aa5a122f7ad0d2dde819ec416d2e479065490e5a84f970c534ea4220d',
 'harness_binary_sha256':'8068af36cb9b0e38456457db7004c94f3d2a0ea1212b0c97746f790a26f60615',
 'candidate_source_revision':'a8930e677bc745854b9f693b5628c8a8bd2ac848',
 'cases':case_rows,
 'all_accepted':all(c['exit']==0 for c in case_rows),
 'all_equal_checkpoint_asr8_initial_images':all(c['checkpoint_equal'] and c['asr8_equal'] and c['initial_images_equal'] for c in case_rows),
 'settlement_exercised':False,
 'private_keys_copied':False,
}
(E/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
