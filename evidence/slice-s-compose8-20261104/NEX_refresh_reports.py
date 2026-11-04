"""Report only validator-admitted closure; preserve all conservative edges."""
from pathlib import Path
import json,subprocess,sys
import NEX_validate as v
E=v.E;R=v.R;P=E.parent/'slice-s-compose7-20261103'
summary=v.read(E/'NEX_VALIDATION.json');packet=v.read(E/'NEX_LEDGER_DELTA.json');base=v.read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');closed=set(summary['slice_closed'])
rows={}
for r in base['rows']:rows.setdefault(r['function'],[]).append(r['row'])
edges=v.read(P/'NEU_EDGES.json')
for e in edges['edges']:
 caller,callee=e['edge'].split(' -> ',1);e['caller_composed']=all(r in closed for r in rows[caller]);e['callee_composed']=all(r in closed for r in rows[callee])
 if e['edge'] in packet.get('edges',{}) and packet['edges'][e['edge']].get('id','').startswith('NEX_'):e['certificate']=packet['edges'][e['edge']]
edges['provenance']='NEU edge set retained, NEX validator-admitted closure only; no alternative target pruned';(E/'NEX_EDGES.json').write_text(json.dumps(edges,indent=1)+'\n')
roots=v.read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S']['roots']
text='''# Slice S composition\n\nCurrent validated checkpoint: **%s/97 rows, 2/7 roots CLOSED**. Target not yet established. Native roots use the NEM ruling-(y) hybrid form: a kernel MODEL theorem plus checked frozen-native caller/child/domain certificates, under the root-owned PacketDomain and PhysicalInterpretation, P6/D188 option-A reclassification, the approved runtime trust rows and RuntimePersistence. No single kernel theorem from Rust source is claimed.\n\nAuthority: NEX_VALIDATION.json, NEX_validate.py, immutable NEU baseline and all unchanged predecessor gates. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Headline AspisR1.RPx_Deployed.deployed; frozen3; L154 parameter; D188 narrowed.\n\nRuntimeReturnData under ruling (ab), 2026-11-04, is ADDED runtime trust. No newly closed root uses (ab) at this checkpoint. NEX_ReturnData's model event/order/bound facts are supporting laws, not a proof of platform readback or an op53 Unit erasure. No shipped source changed; no ELF rebuild trigger.\n\n'''%summary['closed_row_count']
old=v.read(P/'NEU_STOP_AUDIT.json');obstacles={p['function']:p['exact_remaining_obligation'] for p in old['root_results']}
for f in roots:
 status='CLOSED' if all(r in closed for r in rows[f]) else 'OPEN'
 text+='## '+f+'\n\nStatus: '+status+'.\n\n'
 if status=='CLOSED':
  c=packet['roots'][f];text+='Inherited certificate: `'+c['id']+'`. Exact model statement(s), retained unchanged:\n\n'
  for t in c['theorems']:
   if 'result_state_effects' in t['name']:
    text+='```lean\n'+t['statement']+'\n```\n\n';text+='Axioms: standard subset of `[propext, Classical.choice, Quot.sound]`, pinned in `'+t['receipt']['path']+'`.\n\n'
  text+='Native/domain receipts and all explicit root qualifications remain in the pinned inherited certificate. No inner bridge was re-proved or removed. (ab) uses: none.\n\n'
 else:
  text+='No composed native theorem established. Exact outstanding obligations from the accepted handoff:\n\n'+obstacles[f]+'\n\n'
  if f.endswith('emit_result'):text+='Ruling (ab) now resolves the policy/effect-interface question by adding RuntimeReturnData. Exact model bytes, trace position and no later write still require native proof; BindingBridge and EncoderBridge remain explicit, not discharged. (ab) uses: supporting model only; no closed native certificate.\n\n'
text+='## Newly admitted exact helper\n\n`NEX_Exact.result_state_effects` (L015) reuses NBH_Exact.source. Full statement:\n\n```lean\n'+packet['members']['crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact']['domain_theorems'][0]['statement']+'\n```\n\nAxioms `[propext, Quot.sound]`. Native coverage is widths8/32, slice length≤33, all input bytes and every return/error, readonly state and empty runtime effects. Actual slice callers must establish these domains at their own call sites. K052..055 execute the frozen helper under KMX and deployed statement features, with matched failing output controls; frozen graph and post-run lock checks pass. The two slice rows TX1:279/TX2:173 are newly CLOSED. No root closure is inferred.\n'
(E/'NEX_COMPOSED.md').write_text(text)
print(json.dumps(dict(closed=summary['closed_row_count'],edges=len(edges['edges']))))
