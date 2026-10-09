#!/usr/bin/env python3
"""Audit the final linked call graph, including conservative indirect edges."""
import hashlib, json, re, subprocess, sys
from pathlib import Path
log, linked, stripped, out = map(Path, sys.argv[1:])
llvm = Path('/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin')
syms = subprocess.check_output([str(llvm/'llvm-readelf'), '-s', str(linked)], text=True)
dis = subprocess.check_output([str(llvm/'llvm-objdump'), '-d', '--no-show-raw-insn', str(linked)], text=True)
out.mkdir(parents=True, exist_ok=True)
(out/'symbols.txt').write_text(syms)
(out/'disassembly.txt').write_text(dis)
functions = {}
for line in syms.splitlines():
    m = re.match(r'\s*\d+: ([0-9a-f]+)\s+(\d+) FUNC\s+\S+\s+\S+\s+(\d+) (\S+)', line)
    if m: functions[m[4]] = {'address': int(m[1],16), 'size': int(m[2])}
addresses = {v['address']: k for k,v in functions.items()}
root = next(k for k in functions if 'process_r0_cu_probe_instruction17h' in k)
edges = {k:set() for k in functions}; indirect=[]; external=[]; current=None
for line in dis.splitlines():
    m=re.match(r'[0-9a-f]+ <([^>]+)>:',line)
    if m: current=m[1]
    if current not in edges: continue
    m=re.match(r'\s*([0-9a-f]+):\s+call (0x[0-9a-f]+|-0x[0-9a-f]+)',line)
    if m:
        imm=int(m[2],16)
        if imm>=2**31: imm-=2**32
        target=int(m[1],16)+8+8*imm
        if target in addresses: edges[current].add(addresses[target])
        else: external.append({'caller':current,'instruction':line.strip()})
    if re.search(r'\bcallx\b',line):
        indirect.append({'caller':current,'instruction':line.strip()})
        # Sound overapproximation: a retained function pointer may reach any
        # linked function. This includes hash callbacks, observers, formatting
        # vtables, allocation/error paths and their transitive descendants.
        edges[current].update(functions)
seen=set(); todo=[root]
while todo:
    n=todo.pop()
    if n in seen: continue
    seen.add(n);todo.extend(edges[n]-seen)
lines=[l for l in log.read_text().splitlines() if l.startswith('Error:')]
diags={}
for line in lines:
    m=re.search(r'(?:Function |function call in method )(\S+)',line)
    assert m, line
    diags.setdefault(m[1],[]).append(line)
records=[]
for name, messages in sorted(diags.items()):
    present=name in functions
    reachable=name in seen
    records.append({'symbol':name,'diagnostics':messages,'present_in_linked_elf':present,
        'reachable':reachable,'reason':('not in root call-graph closure' if present else
        'absent from complete unstripped linked symbol table and function bodies; linker removed it, so no direct or indirect edge from the entrypoint can reach it')})
# Strip only debug/symbol metadata: show the executable text is identical.
for tag,p in [('linked',linked),('measured',stripped)]:
    subprocess.run([str(llvm/'llvm-objcopy'),'--dump-section',f'.text={out/(tag+".text")}',str(p)],check=True)
text_hashes={tag:hashlib.sha256((out/(tag+'.text')).read_bytes()).hexdigest() for tag in ['linked','measured']}
assert len(set(text_hashes.values()))==1
record={'root':root,'root_address':functions[root]['address'],'method':'direct SBF relative calls plus every linked function as a conservative target of each callx',
    'linked_sha256':hashlib.sha256(linked.read_bytes()).hexdigest(),'measured_elf_sha256':hashlib.sha256(stripped.read_bytes()).hexdigest(),
    'text_sha256':text_hashes,'linked_function_count':len(functions),'reachable_function_count':len(seen),
    'reachable_functions':sorted(seen),'direct_and_conservative_edges':{k:sorted(v) for k,v in edges.items()},
    'indirect_calls':indirect,'external_calls':external,'diagnostic_lines':len(lines),'diagnostic_functions':len(records),
    'reachable_diagnostics':[r for r in records if r['reachable']],'unreachable_diagnostics':[r for r in records if not r['reachable']],
    'all_diagnostic_functions_absent_from_linked_elf':all(not r['present_in_linked_elf'] for r in records)}
(out/'stack-audit.json').write_text(json.dumps(record,indent=2)+'\n')
assert not record['reachable_diagnostics']
assert record['all_diagnostic_functions_absent_from_linked_elf']
print(json.dumps({k:record[k] for k in ['root','linked_function_count','reachable_function_count','diagnostic_lines','diagnostic_functions','reachable_diagnostics','all_diagnostic_functions_absent_from_linked_elf']}))
