#!/usr/bin/env python3
"""Writes PCQF_FAILURES.json, PCQF_TOOLS.json, PCQF_CONFIG_BY_MODULE.json, adds p1e_config to each PINS, and writes PCQF_RECEIPT_SUMMARY.json."""
import json,re,lzma,hashlib,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;EV=E.parent;ZK=str(EV.parent)
def J(p):return json.loads(Path(p).read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
runs=[]
for f in sorted(E.glob('PCQF_E[0-9][0-9][0-9]_spec.json')):
    s=J(f);run=s['run'];rc=E/run/'receipt.json'
    if not rc.exists():continue
    r=J(rc);runs.append((s,r))
def err(run):
    t=lzma.decompress((E/run/'stdout.log.xz').read_bytes()).decode('utf8','replace') if (E/run/'stdout.log.xz').exists() else (E/run/'stdout.log').read_text()
    if 'ERROR Code failed to compile' in t:return 'Charon: "ERROR Code failed to compile" (charon-driver exit 101, no diagnostic text); a --start-from root does not exist in the build configuration (cfg-compiled-out)'
    m=re.search(r'Uncaught exception:\s*\n(.*?)\n\nRaised',t,re.S) or re.search(r'Uncaught exception:\s*\n(.*?)(?:\nRaised|\nCalled)',t,re.S)
    body=re.sub(r'\s+',' ',m.group(1)).strip()[:420] if m else 'see stdout.log.xz'
    loc=re.findall(r"Source: '([^']+)', lines ([0-9:\-]+)",body)
    ml=re.search(r'Raised at ([^\n]+)',t);cs=re.search(r'Called from Aeneas__(Interp\w+)\.\w+ in file "[^"]*", line[s]? ([0-9]+)',t)
    return 'Aeneas: '+body+((' | raised '+ml.group(1)[:80]) if ml else '')
fails=[]
for s,r in runs:
    if r['exit_status']!=0:
        c=s['configuration']
        fails.append(dict(run=s['run'],spec=s['spec_id'],label=s['label'],start_from=c['start_from'],include=c['include'],opaque=c['opaque'],features=c['features'] if len(c['features'])<40 else 'audit feature set FS (see spec)',exit=r['exit_status'],wall_seconds=round(r['wall_seconds'],1),peak_rss_kib=r['peak_rss_kib'],error=err(s['run'])))
(E/'PCQF_FAILURES.json').write_text(json.dumps(dict(schema=1,target_established=False,note='Exact tool errors. No failed shape was rerun unchanged; a second shape (split roots or opaque failing callee) is a separate spec id. A shape that failed twice is retired.',failures=fails),indent=1)+'\n')
# tools
tools={}
for k in ['charon','aeneas-b59d5188-extended','charon-driver']:
    p=Path('/nonexistent')
pins=J(E/'PCQF_E001_emitted/PCQF_E001_PINS.json')
tl=dict(note='Controller copies from P1c (PCQC_) with PCQC_ -> PCQF_; stager unchanged (evidence/extract-stage-20261106/NHR_stage.py); per-run extra_env overflow checks ON (ruling 2026-11-09). Tool: aeneas-b59d5188-extended with Charon of the same pin as P1c.',
  tools=pins['tools'],stager_sha256=pins['stager_sha256'],controller_sha256=pins['controller_sha256'],toolchain=pins['environment'],files={})
for n,orig in (('PCQF_extract.py','prov-p1c-20261109/PCQC_extract.py'),('PCQF_run.py','prov-p1c-20261109/PCQC_run.py'),('PCQF_run_host.py','prov-p1c-20261109/PCQC_run_host.py'),('PCQF_STAGER_PIN.json','prov-p1c-20261109/PCQC_STAGER_PIN.json')):
    tl['files'][n]=dict(original=orig,original_sha256=sha((EV/orig).read_bytes()),sha256=sha((E/n).read_bytes()),changes='PCQC_ -> PCQF_ (prefix, attempt-id regex, file names, env PCQF_HOST_BASE); codex-pc-prov-p1c-20261109 -> codex-pc-prov-p1e-20261109; no logic change')
tl['files']['PCQF_render_spec.py']=dict(original='prov-p1a-20261109/PCQ_render_spec.py',sha256=sha((E/'PCQF_render_spec.py').read_bytes()),changes='overflow checks always on; reads PCQF_extract_specs.json; include list rendered after start-from as in the original')
tl['files']['PCQF_chain.sh']=dict(original='prov-p1c-20261109/PCQC_chain.sh',sha256=sha((E/'PCQF_chain.sh').read_bytes()),changes='renders spec from PCQF_extract_specs.json instead of copying an earlier spec; strictly sequential')
tl['transparency_option']='Charon --include aspis_core::field::P (made aspis_core::field::P a def in aspis-statement and cost-probe selections; see PCQF_SUPERSEDES.json)'
(E/'PCQF_TOOLS.json').write_text(json.dumps(tl,indent=1)+'\n')
# per-module configuration from gate text
g={}
for m,v in J(EV/'prov-p2b-20261109/inputs/gate_sources.json').items():
    if v['paths']:g[m]=v['paths'][0]
for m,x in J(EV/'prov-p2c-20261109/PCUC_EQ_STATUS.json')['modules'].items():
    if x['passes']:g[m]=x['passes'][0]['gate_path']
cfg={}
for m,p in g.items():
    t=subprocess.run(['git','-C',ZK,'show','HEAD:'+p],capture_output=True,text=True).stdout
    chk=len(re.findall(r'←\s*[^\n]*?\s[+\-*]\s',t));wr=len(re.findall(r'wrapping_|Wrapping|\.wrap',t))
    cfg[m]=dict(gate_file=p,checked_arithmetic_bindings=chk,wrapping_markers=wr,
      overflow_checks='ON' if (chk>0 or wr==0) else 'OFF',
      basis=('gate text binds +,-,* results with <- (checked arithmetic); no wrapping_ markers' if chk>0 and wr==0 else 'gate text has no +,-,* arithmetic bindings and no wrapping markers: configuration has no effect on this module; ON kept (P1c ruling)' if wr==0 else 'wrapping markers: OFF'))
(E/'PCQF_CONFIG_BY_MODULE.json').write_text(json.dumps(dict(schema=1,ruling='2026-11-09 per-gate-module configuration (Stream A lead): checked ops => ON, wrapping_* on plain operators => OFF',method='regex over the gate file text: count of `<- a op b` (op in + - *) bindings and of wrapping_/Wrapping markers',modules=cfg),indent=1)+'\n')
# annotate PINS
for s,r in runs:
    pf=E/(s['run']+'_emitted')/(s['run']+'_PINS.json')
    if not pf.exists():continue
    d=J(pf);mods=(s.get('covers') or {}).get('modules',[])
    d['p1e_config']=dict(overflow_checks='ON',cargo_profile_release_overflow_checks='true',rustflags_appended='-C overflow-checks=yes',per_gate_module={m:cfg.get(m,{}).get('overflow_checks','n/a (not a P2b/P2c gate module)') for m in mods},
        note='added after the run by PCQF_records.py from PCQF_CONFIG_BY_MODULE.json; the run itself was made with the extra_env recorded in extra_env_appended_to_stager_env')
    pf.write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
rs=[dict(run=s['run'],spec=s['spec_id'],exit=r['exit_status'],wall_seconds=round(r['wall_seconds'],1),peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],cgroup_peak=r.get('cgroup_memory_peak_bytes'),source_revision=r['source_revision']) for s,r in runs]
(E/'PCQF_RECEIPT_SUMMARY.json').write_text(json.dumps(rs,indent=1)+'\n')
print(len(runs),'runs',len(fails),'failures')
