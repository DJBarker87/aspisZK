"""Primary reference hash/symbol receipts only. No GPL source written."""
import json
import urllib.request
from ResourceHierarchy_objects import Objects, sha

def main():
    objects=Objects()
    try:
        refs=objects.json('evidence/resource-stat-20261024/primary-source-hashes.json')[:3]
        refs += [dict(url='https://raw.githubusercontent.com/torvalds/linux/v6.8/mm/memcontrol.c'),
                 dict(url='https://docs.kernel.org/6.8/admin-guide/cgroup-v2.html')]
        results=[]
        for expected in refs:
            with urllib.request.urlopen(expected['url'],timeout=30) as response:
                raw=response.read(2_000_000);assert not response.read(1)
                pin=dict(sha256=sha(raw),size=len(raw))
                if 'sha256' in expected:
                    assert all(pin[k]==expected[k] for k in pin)
                text=raw.decode();lines=text.splitlines()
                symbols={s:[i+1 for i,line in enumerate(lines) if s in line] for s in
                    ('void mem_cgroup_flush_stats(', 'static void memcg_stat_format(',
                     'static void mem_cgroup_css_rstat_flush(', 'static void cgroup_rstat_flush_locked(',
                     'void page_counter_charge(')}
                results.append(dict(url=expected['url'],response_url=response.url,status=response.status,
                    **pin,symbol_lines=symbols,existing_hash_revalidated='sha256' in expected))
        print(json.dumps(dict(status='PASS',references=results,input_hashes=objects.pins,
            source_saved=False,new_running_kernel_identity_gate=False,
            assessment='Primary source reference refresh only; no host access',print_axioms='N/A'),indent=2))
    finally:objects.close()
if __name__=='__main__':main()
