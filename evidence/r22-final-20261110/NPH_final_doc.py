#!/usr/bin/env python3
"""NPH_: rebuild NPH_R22_FINAL_COUNTS.md from NPH_R22_CONE.json plus the narrative file NPH_final_narrative.md
(sections 2, 4 and 5 are narrative; sections 1, 3 and 6 are generated). Read-only on the cone."""
import json,collections,subprocess,re
c=json.load(open('NPH_R22_CONE.json'))
J=lambda e:(e.get('nph_judgment') or '').split(' ')[0].rstrip(':')
cc=[e for e in c['definitions'] if e['body_class'] in ('CHECKED','MIXED')]
cnt=collections.Counter(J(e) for e in cc)
ex=[e for e in cc if J(e)!='NOT_EXECUTED'];touched=set();bad=set()
for e in ex:
  touched|=set(e['rows'])
  if J(e) in ('OPEN','DOMAIN_LEMMA_PROVED'):bad|=set(e['rows'])
start=dict(TOTAL_PROVED=72,DIRECT=42,PRECONDITION_B=54,DOMAIN_LEMMA_PROVED=0,OPEN=29,NOT_EXECUTED=28)
nar=open('NPH_final_narrative.md').read()
sec=dict(re.findall(r'<<(\w+)>>\n(.*?)(?=\n<<|\Z)',nar,re.S))
def row(name,key):
  d=cnt[key]-start[key];return f"| {name} | {cnt[key]} | {start[key]} | {'+' if d>0 else ''}{d} |"
out=[]
out.append("# NPH_ R22 final counts (CheckedVsWrapping), 2026-11-10 continuation\n")
out.append("Job NPH_, branch codex/cx-r22-20261110, frozen target 4bb3b3f (deployed ELFs f8c0ec72…, 63ad3e9c…, built with overflow checks OFF). Sections 1, 3 and 6 are generated from NPH_R22_CONE.json by NPH_final_doc.py. **Target not yet established.**\n")
out.append("## 1. Counts\n")
out.append("| Judgment | Definitions | Start of this run | Change |\n|---|---:|---:|---:|")
for n,k in [('TOTAL (a)','TOTAL_PROVED'),('DIRECT (c)','DIRECT'),('precondition proved from the callers (b)','PRECONDITION_B'),('domain lemma proved, caller join open','DOMAIN_LEMMA_PROVED'),('open','OPEN'),('NOT_EXECUTED (excluded, ruling 1)','NOT_EXECUTED')]:out.append(row(n,k))
exn=len(ex);out.append(f"| **executed (the obligation)** | **{exn}** | 197 | {exn-197:+d} |")
out.append(f"| all checked or mixed | {len(cc)} | 225 | {len(cc)-225:+d} |\n")
out.append(f"Rows. The executed checked or mixed definitions touch **{len(touched)}** CLOSED rows. **{len(bad)}** of them still depend on at least one open definition (153 at the start of this run). {len(touched)-len(bad)} are served only by TOTAL, DIRECT or (b) definitions.\n")
out.append(sec['resources'].strip()+"\n")
out.append("## 2. What moved in this run\n");out.append(sec['moved'].strip()+"\n")
n_open=cnt['OPEN']+cnt['DOMAIN_LEMMA_PROVED']
out.append(f"## 3. Definitions still open ({n_open}), largest row fan-out first\n")
out.append('"Only blocker" counts the rows for which this definition is the single remaining open dependency.\n')
out.append(subprocess.check_output(['python3','NPH_open_tables.py','table'],text=True).strip()+"\n")
out.append("## 4. Every textual-screen reliance (one place)\n");out.append(sec['reliances'].strip()+"\n")
out.append("## 5. Proposed wording for the claim document (section 4.3, CheckedVsWrapping row)\n");out.append(sec['wording'].strip()+"\n")
out.append("## 6. Appendix: row IDs of the open definitions\n")
out.append(subprocess.check_output(['python3','NPH_open_tables.py','rows'],text=True).strip()+"\n")
out.append("Target not yet established.\n")
open('NPH_R22_FINAL_COUNTS.md','w').write('\n'.join(out))
print(dict(cnt),len(touched),len(bad))
