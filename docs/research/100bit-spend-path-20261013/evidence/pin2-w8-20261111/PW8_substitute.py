#!/usr/bin/env python3
"""PW8: replay of the recorded fe80 substitution on the fresh PIN2 emission of verify_observed (PW8_E003), by script.
Steps, in order, all recorded in PW8_SUBSTITUTION.json:
 1. blocks r1_semantic.mark and r1_semantic.verify_observed from PW8_E003_emitted/raw/PW8_vo/Funs.lean (doc comment dropped);
 2. PCXU xform (PW8_lib.xform) and the tool-version name map (PW8_toolmap.TOOL_MAP; tool-option adaptation, Stream C class);
 3. the RECORDED fe80 identifier_map and binder addition, read from the committed binding-audit.json
    (docs/research/100bit-spend-path-20261013/lean/bridge-verify-prefix-fe80-20261017/binding-audit.json on research),
    applied with the same regex as fe80 verify.py (longest name first, no identifier character or '.' after the name);
 4. the RPz7 Phase swap, as recorded by the diff ExtractedVerifyPrefixModel.lean -> RPz7_S1SemanticPrefixModelV1.lean:
    verifier.Phase -> RPz7_PhaseIso.Phase.
Also derives VerifyPrefix.Finish from the fresh external signature of r1_semantic.verify_finish (FunsExternal_Template) by
the same maps (axiom signature -> Pi type), for comparison with the frozen abbreviation.
Comparison (b): every produced declaration against the frozen RPz7_S1SemanticPrefixModelV1.lean (L187 source, read-only copy
fetched by sha) with xform + TOOL_MAP applied to the frozen side; equality is on PW8_lib.norm tokens.
usage: python3 PW8_substitute.py <frozen RPz7 file> <frozen fe80 ExtractedVerifyPrefixModel.lean>"""
import sys,re,json,subprocess
sys.dont_write_bytecode=True
from PW8_lib import *
from PW8_toolmap import TOOL_MAP,apply_tool_map
RPZ7,FE80MODEL=sys.argv[1:3]
raw=open('PW8_E003_emitted/raw/PW8_vo/Funs.lean').read();ext=open('PW8_E003_emitted/raw/PW8_vo/FunsExternal_Template.lean').read()
audit_raw=subprocess.check_output(['git','show','research:docs/research/100bit-spend-path-20261013/lean/bridge-verify-prefix-fe80-20261017/binding-audit.json'])
audit=json.loads(audit_raw);mapping=audit['identifier_map']
pattern=re.compile('|'.join(re.escape(n)+r'(?![A-Za-z0-9_.])' for n in sorted(mapping,key=len,reverse=True)))
PHASE=[(r'(?<![\w.])verifier\.Phase(?![\w])','RPz7_PhaseIso.Phase')]
used=set()
def prep(b):
    b=re.sub(r'(?s)^/--.*?-/\n','',b);b=xform(b);return apply_tool_map(b,used)
fresh={key(b):b for b in blocks(inner(raw,'PW8_vo'))}
out={};steps={}
for name in ['r1_semantic.mark','r1_semantic.verify_observed']:
    src=prep(fresh[name]);body=pattern.sub(lambda z:mapping[z[0]],src)
    item=[x for x in audit['exact_body_audits'] if x['declaration']==name][0]
    if item['binder_addition']:
        hdr='def '+mapping[name]+'\n';assert hdr in body,(name,body[:200]);body=body.replace(hdr,'def '+mapping[name]+item['binder_addition']+'\n',1)
    for p,r in PHASE:body=re.sub(p,r,body)
    out[mapping[name]]=body;steps[name]=dict(fresh_raw_block_sha256=sha(fresh[name]),after_xform_toolmap_sha256=sha(src),output_sha256=sha(body),binder_addition=item['binder_addition'])
# VerifyPrefix.Finish from the verify_finish external signature
eb={key(b):b for b in blocks(ext.split('open PW8_vo',1)[1])}['r1_semantic.verify_finish']
sig=prep(eb);m=re.search(r'(?s)axiom r1_semantic\.verify_finish\s*\n\s*\{H : Type _?\} \((\w+) : ([^)]*)\) :\s*(.*)$',sig);assert m,sig
fin='abbrev VerifyPrefix.Finish := {H : Type _} → '+m.group(2)+' →\n  '+' '.join(m.group(3).split())
for p,r in PHASE:fin=re.sub(p,r,fin)
out['VerifyPrefix.Finish']=fin
# comparison (b) against frozen RPz7 (and the fe80 model, which RPz7 differs from only by the Phase swap)
def frozen_decls(path):
    t=open(path).read();body=inner(t,'AspisR1PublicPreparation')
    parts=re.split(r'(?m)^(?=(?:abbrev|def) )',body);d={}
    for p in parts:
        mm=re.match(r'(?:abbrev|def) (\S+)',p)
        if mm:d[mm.group(1)]=re.sub(r'(?m)^#print.*$','',p).strip()
    return t,d
rt,rz=frozen_decls(RPZ7);ft,fz=frozen_decls(FE80MODEL)
cmp=[]
for k,v in out.items():
    g=apply_tool_map(xform(rz[k]))
    a,b=norm(g),norm(v)
    # universe spelling of the abbreviation binder is the only Type/Type _ case the map does not cover
    cmp.append(dict(declaration=k,equal_after_maps=(a==b),frozen_tokens_sha256=sha(a),pin2_tokens_sha256=sha(b),diff=None if a==b else [l for l in __import__('difflib').unified_diff(a.split(),b.split(),lineterm='',n=1) if not l.startswith(('---','+++'))]))
res=dict(schema='PW8_SUBSTITUTION/1',input=dict(emission='PW8_E003 Funs.lean',sha256=sha(raw),external_template_sha256=sha(ext)),
 recorded_identifier_map=mapping,recorded_binding_audit_sha256=sha(audit_raw),phase_swap=dict(PHASE),
 tool_map_entries_used=[dict(pattern=TOOL_MAP[i][0],replacement=TOOL_MAP[i][1],reason=TOOL_MAP[i][2]) for i in sorted(used)],
 steps=steps,frozen_rpz7_sha256=sha(rt),frozen_fe80_model_sha256=sha(ft),comparison_b=cmp,
 output_text={k:v for k,v in out.items()},output_sha256=sha('\n\n'.join(out[k] for k in sorted(out))))
json.dump(res,open('PW8_SUBSTITUTION.json','w'),indent=1,ensure_ascii=False)
for c in cmp:print(c['declaration'],'EQUAL' if c['equal_after_maps'] else 'DIFF',c['diff'] or '')
