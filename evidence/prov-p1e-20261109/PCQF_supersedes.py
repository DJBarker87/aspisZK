#!/usr/bin/env python3
"""Writes PCQF_SUPERSEDES.json: each P2c-used emission (PCQC_E002/E003/E004/E011, PCQ_E039/E040) vs its P-transparent re-run."""
import json,re,difflib,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;EV=E.parent
def J(p):return json.loads(Path(p).read_text())
pairs=[('PCQC_E002','prov-p1c-20261109','PCQF_E001','S005a'),('PCQC_E003','prov-p1c-20261109','PCQF_E002','S009'),('PCQC_E004','prov-p1c-20261109','PCQF_E003','S014'),
       ('PCQC_E011','prov-p1c-20261109','PCQF_E006','S015'),('PCQ_E039','prov-p1a-20261109','PCQF_E004','S013'),('PCQ_E040','prov-p1a-20261109','PCQF_E005','S011')]
norm=lambda t:re.sub(r'PC(?:QF|QC|Q|O)_','NS_',t)
out=dict(schema=1,target_established=False,
 note='Each entry: an earlier overflow-checks-on emission that P2c used, the P1e re-run of the identical start_from/opaque with --include aspis_core::field::P added (S015 also adds M31/QM31 ZERO, ONE, mul, reduce_u64 items), and the text difference modulo the PCQ_/PCQC_/PCQF_ prefix. The earlier emission is superseded for the P3 transport of aspis_core.field.P only; every other declaration is unchanged unless listed under changed_declarations.',
 option='Charon: --include aspis_core::field::P (cross-crate constant is opaque by default in aspis-statement / aspis-r1-cost-probe selections; a local selection of aspis-core defines it).',supersedes=[])
for old,od,new,sid in pairs:
    rcn=E/new/'receipt.json'
    e=dict(superseded=old,superseded_dir='%s/%s_emitted/raw'%(od,old),replacement=new,replacement_dir='prov-p1e-20261109/%s_emitted/raw'%new,spec=sid,
           replacement_exit=J(rcn)['exit_status'] if rcn.exists() else None,files={})
    od_=EV/od/(old+'_emitted/raw');nd=E/(new+'_emitted/raw')
    for nf in sorted(nd.glob('*/*.lean')):
        c=list(od_.glob('*/'+nf.name))
        if not c:e['files'][nf.name]='no old file';continue
        a=norm(c[0].read_text()).splitlines();b=norm(nf.read_text()).splitlines()
        if a==b:e['files'][nf.name]='identical_modulo_prefix';continue
        d=[l for l in difflib.unified_diff(a,b,lineterm='',n=0) if not l.startswith(('---','+++','@@'))]
        e['files'][nf.name]=dict(status='DIFFERS',removed=sum(l.startswith('-') for l in d),added=sum(l.startswith('+') for l in d),sample=d[:14])
    out['supersedes'].append(e)
(E/'PCQF_SUPERSEDES.json').write_text(json.dumps(out,indent=1)+'\n');print('ok')
