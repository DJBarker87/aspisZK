#!/usr/bin/env python3
"""PCUA_jobs.py: the job table (module, fresh emission, gate sources) and the generator driver. `python3 PCUA_jobs.py gen ID` runs
the first (probe) generation of one job; `... gen2 ID LOG BUNDLE_OFFSETS` ingests a Lean log and regenerates."""
import subprocess,sys,json
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;EV=H.parent
E13=str(EV/'emission-repro-20261110/NMH_E013_emitted/raw/NMH_field_decode')
Q415=str(EV/'prov-p1b-20261109/PCQ_E415_emitted/raw/PCQ_aspis_r1_cost_probe_candidate')
JOBS={
 'DotDecode':dict(M='RPz7_FIp_DotDecode',fresh=E13,ns='NMH_field_decode',gate='RPz7_FIp_DotDecode.lean',types='RPz7_FIp_DotDecode.lean'),
 'NativeDots':dict(M='RPz7_FIp_NativeDots',fresh=Q415,ns='PCQ_aspis_r1_cost_probe_candidate',gate='RPz7_FIp_NativeDots.lean',types='RPz7_FIo_NativeTypes.lean',open=['FIo_Native']),
 'NativeFunsQ415':dict(M='RPz7_FIo_NativeFuns',fresh=Q415,ns='PCQ_aspis_r1_cost_probe_candidate',gate='RPz7_FIo_NativeFuns.lean',types='RPz7_FIo_NativeTypes.lean'),
 'NativeTypesQ415':dict(M='RPz7_FIo_NativeTypes',fresh=Q415,ns='PCQ_aspis_r1_cost_probe_candidate',gate='RPz7_FIo_NativeTypes.lean'),
 'Stage2Q415':dict(M='Stage2ContinuationTypes',fresh=Q415,ns='PCQ_aspis_r1_cost_probe_candidate',gate='Stage2ContinuationTypes.lean'),
 'CWFuns':dict(M='AspisR1CurrentWide.Funs',fresh=str(EV/'emission-repro-20261110/NMH_E008_emitted/raw/NFG_InverseRef'),ns='NFG_InverseRef',gate='CW_Funs_sources.lean',types='CW_Types_sources.lean'),
 'CWTypes':dict(M='AspisR1CurrentWide.Types',fresh=str(EV/'emission-repro-20261110/NMH_E014_emitted/raw/NMH_wide_decode'),ns='NMH_wide_decode',gate='CW_Types_sources.lean'),
 'S1M31':dict(M='S1M31EmbeddingSourceV1',fresh=Q415,ns='PCQ_aspis_r1_cost_probe_candidate',gate='S1M31EmbeddingSourceV1.lean',kind='types'),
}
JOBS.update({
 'NativeFunsE410':dict(M='RPz7_FIo_NativeFuns',fresh=str(EV/'prov-p1b-20261109/PCQ_E410_emitted/raw/PCQ_aspis_r1_cost_probe_transport'),ns='PCQ_aspis_r1_cost_probe_transport',gate='RPz7_FIo_NativeFuns.lean',types='RPz7_FIo_NativeTypes.lean'),
 'NativeFunsE008':dict(M='RPz7_FIo_NativeFuns',fresh=str(EV/'emission-repro-20261110/NMH_E008_emitted/raw/NFG_InverseRef'),ns='NFG_InverseRef',gate='RPz7_FIo_NativeFuns.lean',types='RPz7_FIo_NativeTypes.lean'),
 'NativeTypesE416':dict(M='RPz7_FIo_NativeTypes',fresh=str(EV/'prov-p1b-20261109/PCQ_E416_emitted/raw/PCQ_aspis_r1_cost_probe_weights'),ns='PCQ_aspis_r1_cost_probe_weights',gate='RPz7_FIo_NativeTypes.lean'),
 'NativeTypesE003':dict(M='RPz7_FIo_NativeTypes',fresh=str(EV/'emission-repro-20261110/NMH_E003_emitted/raw/NHR_tx2_common'),ns='NHR_tx2_common',gate='RPz7_FIo_NativeTypes.lean'),
 'Stage2E003':dict(M='Stage2ContinuationTypes',fresh=str(EV/'emission-repro-20261110/NMH_E003_emitted/raw/NHR_tx2_common'),ns='NHR_tx2_common',gate='Stage2ContinuationTypes.lean'),
 'Stage2E010':dict(M='Stage2ContinuationTypes',fresh=str(EV/'emission-repro-20261110/NMH_E010_emitted/raw/NJS_Extract'),ns='NJS_Extract',gate='Stage2ContinuationTypes.lean'),
})
JOBS['CtlCWFuns']=dict(M='AspisR1CurrentWide.Funs',fresh=str(H/'control_cw'),ns='AspisR1CurrentWide',gate='CW_Funs_sources.lean',types='CW_Types_sources.lean')
def args(j,out):
    a=['python3',str(H/'PCUA_gen_equalities.py'),'--partition',str(H/'PCUA_PARTITION.json'),'--module',j['M'],'--fresh-dir',j['fresh'],'--fresh-ns',j['ns'],'--gate-source',str(H/'gate_src'/j['gate'])]
    if 'types' in j:a+=['--gate-types-source',str(H/'gate_src'/j['types'])]
    if 'kind' in j:a+=['--kind',j['kind']]
    for o in j.get('open',[]):a+=['--open-extra',o]
    return a
def bundle(name,ids):
    subprocess.run(['python3',str(H/'PCUA_bundle.py'),str(H/('PRVEq_bundle_'+name+'.lean')),str(H/('PRVEq_bundle_'+name+'.offsets.raw.json'))]+[str(H/('PRVEq_'+i+'.lean')) for i in ids],check=True)
    raw=json.loads((H/('PRVEq_bundle_'+name+'.offsets.raw.json')).read_text());out={}
    for i in ids:out['PRVEq_'+JOBS[i]['M'].replace('.','_')]=raw['PRVEq_'+i]   # generator keys offsets by module
    (H/('PRVEq_bundle_'+name+'.offsets.json')).write_text(json.dumps(out))
    # error-limit only (no resource cap): without this the 100-message limit of Lean stops elaboration after the first noisy module
    p=H/('PRVEq_bundle_'+name+'.lean');L=p.read_text().split('\n');k=max(i for i,l in enumerate(L) if l.startswith('import '))
    L.insert(k+1,'set_option maxErrors 100000');p.write_text('\n'.join(L))
    raw=json.loads((H/('PRVEq_bundle_'+name+'.offsets.raw.json')).read_text())
    for i in ids:  # line map shifts by one line after the inserted option
        key='PRVEq_'+JOBS[i]['M'].replace('.','_');out[key]['line_map']=[[a,b+1] for a,b in raw['PRVEq_'+i]['line_map']]
    (H/('PRVEq_bundle_'+name+'.offsets.json')).write_text(json.dumps(out))
if __name__=='__main__':
    if sys.argv[1]=='bundle':bundle(sys.argv[2],sys.argv[3:]);sys.exit(0)
    cmd,jid=sys.argv[1:3];j=JOBS[jid];stem='PRVEq_'+jid
    base=args(j,stem)+['--out',str(H/(stem+'.lean')),'--report',str(H/(stem+'.report.json'))]
    if cmd=='gen':base+=['--state-out',str(H/(stem+'.state1.json'))]
    else:
        log,offs=sys.argv[3:5];base+=['--state',str(H/(stem+'.state1.json')),'--state-out',str(H/(stem+'.state2.json')),'--lean-log',log]
        if offs!='-':base+=['--bundle-offsets',offs]
    r=subprocess.run(base,capture_output=True,text=True)
    print(r.stdout[-600:]);print(r.stderr[-400:]);sys.exit(r.returncode)
