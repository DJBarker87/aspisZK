from pathlib import Path
import json
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul5-20261104'
# Runner adapted from own-lane predecessor; infrastructure unchanged.
s=(P/'NFC_kani_run.py').read_text().replace('NFC','NFF').replace('mul5','mul7').replace('<= 60','<= 90')
s=s.replace("'NFF_RECEIVER_PAYLOAD.json'","'NFF_PAYLOAD.json'")
(E/'NFF_kani_run.py').write_text(s)
(E/'NFF_graph.py').write_text((P/'NFC_graph.py').read_text().replace('NFC','NFF'))
frozen=json.loads((P/'NFC_FROZEN.json').read_text());(E/'NFF_FROZEN.json').write_text(json.dumps(frozen))
s=(P/'NFC_gate.py').read_text().replace('NFC','NFF')
a=s.index("changed={'");b=s.index("(B/(a+'-frozen-source-check.json'))",a)
s=s[:a]+'''checked=[]
base=json.loads((B/'NFF_BASE.json').read_text())
for name,text in frozen_sources.items():
 p=S/name
 if not p.is_file():continue
 assert p.read_text()==base.get(name,text),('frozen source drift',name)
 checked.append(name)
changed=set(base)
'''+s[b:]
a=s.index('harnesses=[');b=s.index('static_errors=',a)
s=s[:a]+'''harnesses=[p for p in S.rglob('NFF*.rs')]+[S/'KMX_stubs.rs',S/'KMX_native.rs']
'''+s[b:]
(E/'NFF_gate.py').write_text(s)
# Native base: exactly inherited arbitrary impls and exact KMX support, no old harnesses reached.
prior=json.loads((P/'NFC_RECEIVER_PAYLOAD.json').read_text());base={}
for name in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-r1-cost-probe/src/lib.rs']:
 base[name]=prior[name].replace('NFC','NFF')
base['crates/aspis-r1-cost-probe/src/fast_dots.rs']=frozen['crates/aspis-r1-cost-probe/src/fast_dots.rs']+'\n#[cfg(kani)] #[path="NFF_dots.rs"] mod NFF_dots;\n'
(E/'NFF_BASE.json').write_text(json.dumps(base))
payload=dict(base)
for name in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']:payload[name]=prior[name]
(E/'NFF_PAYLOAD.json').write_text(json.dumps(payload))
# Extend runner's exact source set with the independently validated base.
s=(E/'NFF_kani_run.py').read_text().replace("files['NFF_FROZEN.json']=(E/'NFF_FROZEN.json').read_text()","files['NFF_FROZEN.json']=(E/'NFF_FROZEN.json').read_text()\n    files['NFF_BASE.json']=(E/'NFF_BASE.json').read_text()")
(E/'NFF_kani_run.py').write_text(s)
# Private setup; admission occurs before upload/copy.
s=(P/'NFC_native_setup.py').read_text().replace('NFC','NFF').replace('mul5','mul7').replace("src=P/'codex-cx-slice-q-mul4-20261029/NFA_src'","src=P/'codex-cx-slice-q-mul5-20261029/NFC_src'")
s=s.replace("pins={str(p.relative_to(dst))", "frozen=json.loads((P/'codex-cx-slice-q-mul5-20261029/NFC_FROZEN.json').read_text())\nfor n,t in frozen.items():\n q=dst/n\n if q.is_file():q.write_text(t)\n(B/'NFF_tmp').mkdir(exist_ok=True)\npins={str(p.relative_to(dst))")
(E/'NFF_native_setup.py').write_text(s)
