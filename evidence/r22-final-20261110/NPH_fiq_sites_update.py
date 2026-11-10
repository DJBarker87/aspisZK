#!/usr/bin/env python3
"""NPH_ (R22, FIq): annotate the 238 FIq sites of NPH_SITES.json from NPH_FIQ_REFS.json (backward referrer screen)."""
import json,collections
s=json.load(open('NPH_SITES.json'));r={x['site']:x for x in json.load(open('NPH_FIQ_REFS.json'))['sites']}
T='NPH_R22FIqTerminal.terminal_total + NPH_R22JoinFIq.stage1_guardedT/term_site'
for e in s['FIq']:
  x=r[e['site']];c=x['cls']
  if c=='COVERED_BY_TERMINAL':
    e['status']='TERMINAL_TOTAL';e['lemma_or_reason']=('every execution lies inside terminal_qm31 (backward screen: upward definition referrers meet only the composed terminal, every other top theorem-only without tie candidate); '
      'the terminal is ok on its input domain and the deployed 345 entry runs it only there: '+T)
  elif c=='STOP_NODE':
    e['status']='TERMINAL_TOTAL';e['lemma_or_reason']='the composed terminal itself: '+T
  elif c=='PROOF_ONLY':
    e['status']='NOT_EXECUTING';e['lemma_or_reason']=('FLAGGED textual screen (NPH_fiq_refs_host.py, widened tie words): no definition path upward reaches a deployed root or the terminal; every top is referenced from theorems only, none naming a deployed record')
  elif c=='TIE_CANDIDATE':
    e['status']='W_LEMMA';e['lemma_or_reason']={'LIB_VTerminal.native':'NPH_R22FIqSites.lib_native_ok/lib_model_site: its only definition referrer LIB_VTerminal.model runs it only under LIB_VTerminal.Domain, where it is ok (library carriers canonical by type)',
      'AspisR1.NNG_ModelTerminal.native':'NPH_R22FIqSites.nng_native_ok: at the lowered LIB arguments it equals LIB_VTerminal.native (NNG_LIBTerminal.native), ok under Domain; its NNG 136 model callers (NNG_ConcreteCalls136.calls c7) are model-layer records tied to the headline by theorems only, flagged'}[e['site']]
  else: raise SystemExit(('unexpected',e['site'],c))
  e['screen_20261110_fiq']=dict(cls=c,meets_stop=x.get('meets_stop'),upward_defs=x.get('upward_defs'))
s['_summary']['FIq']['status_20261110_fiq']=dict(collections.Counter(e['status'] for e in s['FIq']))
s['_contexts_closed_20261110_fiq']=('FIq: terminal totality on the input domain (NPH_R22FIqTerminal, L078) composed to the deployed 345 entry (NPH_R22JoinFIq, L080); '
  'model wrappers NPH_R22FIqSites (L081); backward referrer screen NPH_FIQ_REFS.json (textual, flagged; positive controls NBO_FieldSemantics add/product/power, NBF_BasisInstall.install, NJJ_QueryOps.concrete, FIp_SemanticArithmetic.mask, NFS_QueryOps.installed, AspisR72Sampler secure_ood_circle_point_from_parameter all non-proof-only)')
json.dump(s,open('NPH_SITES.json','w'),indent=1,ensure_ascii=False)
print(s['_summary']['FIq']['status_20261110_fiq'])
