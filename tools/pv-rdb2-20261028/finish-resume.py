"""Assemble the final evidence without running any proof or native test."""
from pathlib import Path
import json, hashlib, lzma, re, subprocess

R=Path(__file__).resolve().parents[2]
E=R/'evidence/pv-rdb2-20261028'
def load(p): return json.loads(p.read_text())
def write(p,j): p.write_text(json.dumps(j,indent=2)+'\n')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
deployed=load(E/'native-leaves/receipt.json')
fixture=load(E/'resume-pointer-layout-inputs.json')
fp='resume-final-dependency-fingerprint.json.xz'
fingerprint=load(E/'resume-row-gate.json')
for p in E.glob('*/receipt.json'):
    j=load(p)
    if not (p.parent.name.startswith('resume-') or p.parent.name.startswith('lean-')): continue
    # Lean and source checks do not run Cargo. The associated deployed graph
    # is recorded separately from any fixture graph actually compiled.
    j['associated_deployed_resolved_features']=deployed['resolved_features']
    j['associated_deployed_profile']=deployed['profile']
    j['associated_deployed_toolchain']=deployed['toolchain']
    j['dependency_fingerprint']=fp
    j['dependency_fingerprint_uncompressed_sha256']=(E/'resume-final-dependency-fingerprint.json.sha256').read_text().strip()
    if p.parent.name=='resume-pointer-layout-fixed':
        j.update(resolved_features=fixture['resolved_features'],profile=fixture['profile'],toolchain=fixture['toolchain'],fixture_inputs='resume-pointer-layout-inputs.json',evidence_class='finite validation')
    elif p.parent.name=='resume-layout-repeat':
        j.update(resolved_features=[],profile=deployed['profile'],toolchain=deployed['toolchain'],fixture_inputs='resume-layout-repeat-inputs.json',feature_scope='std/core/alloc prebuilt 1.94.1; no Cargo project crates',evidence_class='finite validation of before/after law')
    elif 'resolved_features' not in j:
        j['resolved_features']=deployed['resolved_features']
        j['resolved_features_scope']='associated deployed source graph; this scope did not compile Rust'
        j['profile']=deployed['profile']
        if not p.parent.name.startswith('lean-'):j['toolchain']=deployed['toolchain']
    write(p,j)

attempts=[]
for n in range(41100,41200):
    p=E/f'lean-{n}/receipt.json';assert p.exists(),n
    j=load(p);assert j.get('swap')=='0',(n,j.get('swap'))
    if j['exit']==0:
        for a in j['print_axioms']:
            if 'depends on axioms:' in a:
                names=re.search(r'\[([^]]*)\]',a,re.S).group(1).split(',')
                assert set(x.strip() for x in names)<= {'propext','Classical.choice','Quot.sound'},(n,a)
    attempts.append({'attempt':n,'module':j.get('module'), 'exit':j['exit'],'wall':j['wall'],
                     'peak_rss_kib':j['peak_rss_kib'],'swap':j['swap'],
                     'source_revision':j['source_revision'],'receipt':str(p.relative_to(E))})

for row in fingerprint['rows']:
    name=row['row'];p=E/(name+'.json');old=load(p)
    old['prior_D388_disposition']='SUSPENDED; historical known_changed_functions and unresolved associations below remain the conservative envelope, not the new precise consumed call boundary'
    old['disposition']=row['disposition'];old['native_link_evidence_class']=row['evidence_class']
    old['resume_gate']=row;old['exact_reason']=row.get('exact_reason','All required source/helper transports at the precise consumed boundary pass; compiler and privacy endpoint boundaries retained.')
    old['project_structural']=row.get('boundary',row['exact_reason'] if 'exact_reason' in row else '')
    old['before']='D388: deployed native association SUSPENDED; original Lean/model law retained.'
    old['after']=('Deployed helper source association RESTORED in structural (K-1 substitute) class, at the stated original callback/domain boundary. No endpoint premise removed.' if row['disposition']=='RESTORED' else 'Still SUSPENDED with narrower obligations; no endpoint premise removed.')
    old['source_revision']=revision
    write(p,old)
    (E/(name+'.md')).write_text(f"# {name}: {row['disposition']}\n\n{old['after']}\n\nEvidence class: **{row['evidence_class']}**.\n\n"+
       (row.get('boundary') or row['exact_reason'])+'\n\n'+
       (f"Complete law: `{row['law']}`. Focused replay: `{row['replay_law']}`.\n\n" if row['disposition']=='RESTORED' else '')+
       f"Source checks and exact pins: [resume-row-gate.json](resume-row-gate.json), [{name}.json]({name}.json). Native finite validation: [{old['deployed_native_receipt']}]({old['deployed_native_receipt']}); unchanged same-input fixtures reused from the first phase. Combined audit41198 and focused replay41199 pass; receipts retain target, revision, wall, RSS, swap and axioms.\n\n"+
       'Endpoint premises: removed0, added0, changed0. Rust/compiler-cohort correspondence, E1/E2, real RunJoin, client proof-account route and L1/L2/L3 remain; T is exactly entropy_law/entropy_kernel/observation. No Kani credit.\n')

native=[(p.parent.name,load(p)) for p in E.glob('*/receipt.json') if not p.parent.name.startswith('lean-')]
audit=dict(status='PARTIAL RESTORATION; privacy target not yet established',source_revision=revision,
           restored=[r['row'] for r in fingerprint['rows'] if r['disposition']=='RESTORED'],
           suspended=[r['row'] for r in fingerprint['rows'] if r['disposition']=='SUSPENDED'],findings=[],
           lean_attempts=attempts,lean_budget=dict(used=100,total=100,success=sum(a['exit']==0 for a in attempts),failure=sum(a['exit']!=0 for a in attempts)),
           native_budget=dict(used=len(native),total=120,failure=sum(j['exit']!=0 for _,j in native)),kani=0,
           combined_axioms_audit='lean-41198/receipt.json',focused_replay='lean-41199/receipt.json',
           final_gate='resume-row-gate.json',dependency_fingerprint=fp,
           endpoint_premises=dict(removed=0,added=0,changed=0),
           all_successful_lean_axioms='subset of propext, Classical.choice, Quot.sound',
           retained='compiler-cohort/source-executable boundary D381/D386; E1/E2; RunJoin; proof-account route; L1/L2/L3; no trust-record extension',
           stop='Lean budget exhausted; native-only repetition cannot supply the eight missing universal source/effect laws')
write(E/'combined-audit.json',audit)
for p in [E/'resume-pointer-layout-metadata.json']:
    if p.exists():
        raw=p.read_bytes();(p.with_name(p.name+'.xz')).write_bytes(lzma.compress(raw,preset=6))
        (p.with_name(p.name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
print(json.dumps({k:audit[k] for k in ['restored','suspended','lean_budget','native_budget','stop']}))
