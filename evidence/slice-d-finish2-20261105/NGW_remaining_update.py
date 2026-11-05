from pathlib import Path
import json
E=Path(__file__).resolve().parent;graph=json.loads((E.parent/'slice-d-finish-20261105/NGM_TAIL_GRAPH.json').read_text());closed={'TX2:047','TX2:048'}
updates={
'TX2:119':'E001 extraction, L036 coefficient-add association and L038 natural Horner induction pass; intended missing reverse corruption K034 fails. Complete byte-window/read and native-to-adopted carrier ports plus seven-step source/cohort association still OPEN. Needs Lean; uncovered observations may require native checks.',
'TX2:128':'Statement-point child CLOSED. Split row, product/double argument, count/order and window/frame observations K036..K078 complete with controls, except original K035/K048 timeouts excluded and replaced. Full factor-loop/source/reference and boxed-record composition still OPEN. NFW SAME semantic alpha/z producers remain boundary obligations. Needs Lean and native Box packet.',
'TX2:127':'Need source/value/ownership/allocation/frame certificate under (aa), including corrupt-value and different-allocation controls. No allocation-availability premise.',
'TX2:116':'K098/K099 inherited full Result pair retained. Need same scale/polynomial call/order/frame captures; E001 round reference extracted. Complete polynomial packet still OPEN. Needs native captures and Lean carrier/domain composition.',
'TX2:114':'NGM fourteen one-iteration native pairs retained. E003 dot pack/unpack/result reference now extracted. Still need nine-word/count ABI association, canonical field-window/index and CLOSED Q new/finish packet use, byte-loop/error-prefix/cohort association. Needs Lean; additional native observations only where ABI/frame coverage is missing.',
'TX2:115':'Blocked by OPEN polynomial/round/dot/new/pair packets and NFW Prepared/view producers. K083/K086/K087 excluded timeouts unchanged. Staged cuts only once real callees close; no successful child premise.'}
s='# NGW remaining obligations (live)\n\nTarget not established. New CLOSED rows TX2:047/048; inherited NGM double/guard remain CLOSED. All acceptance-tail roots remain OPEN.\n\n'
for r in graph:
 if r.get('ngm_status',r['status'])=='OPEN' and r['row']not in closed:
  s+=f"## {r['row']} {r['function'].split('::')[-1]} — OPEN\n\n"+updates.get(r['row'],'Needs complete source-ordered native local-record/cell packet with controls, exact reference/emitted/cohort association, canonical caller-domain and frame/error propagation, then combined replay/scan/ax2. Its actual callees in NGM_TAIL_GRAPH.json remain required. Existing fragmentary receipts do not establish source/model closure.')+'\n\n'
(E/'NGW_REMAINING.md').write_text(s)
