#!/usr/bin/env python3
import pathlib,json,re,collections
O=pathlib.Path(__file__).resolve().parent;R=O.parents[1]
rows=json.load(open(O/'NBI2_selected.json'));I=json.load(open(O/'NBI2_cohort_index.json'))
# Checked kernel dependencies, not merely import membership.
C=set(json.load(open(R/'evidence/replay-deployed2-20261027/RPx_reachable-constants.json')))
SPECIAL={
 'resume':['AspisR1Stage2.verifier.resumeWithOps','AspisR1.Port4A_NativeReader.resume'],
 'read_checkpoint_weights':['AspisR1.CheckpointBytes4Ops.readWeights'],
 'read_checkpoint_semantic_alpha':['AspisR1.CheckpointBytes4Ops.readSemanticAlpha'],
 'validate_checkpoint_queries':['AspisR1.CheckpointBytes4Ops.validate'],
 'checkpoint_size':['AspisR1.CheckpointBytes4Ops.checkpointSize','AspisR1.S2W_D189Entry.checkpoint_size'],
 "Reader<'a>::raw":['AspisR1Stage2.verifier.Reader.rawWithUnwrap','AspisR1.CheckpointBytes3Reader.raw'],
 "Reader<'a>::e":['AspisR1.CheckpointBytes3Reader.readE'],
 "Reader<'a>::k":['AspisR1.CheckpointBytes3Reader.readK'],
 'Weights::new':['FIn_WeightsExtract.weights_new','AspisR1.FIn_WeightsInstall.newWeights'],
 'stage2':['AspisR1.S2W_D189Wrappers.second'],
 'snapshot':['AspisR1.S2W_D189Entry.Entry.snapshot'],
 'SolanaDigest::digest':['AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32'],
}
# Names differ across the installed cohort's local refactoring.
for v in rows:
 name=v['name'];norm=re.sub(r'<.*?>','',name).replace('::','.')
 hits=[n for n in I if n.endswith('.'+norm)]
 # Restrict unrelated same-name field/codec cohorts by suffix containing source module.
 if '::' not in name:
  stem=pathlib.Path(v['file']).stem
  preferred=[n for n in hits if '.'+stem+'.' in n]
  if preferred:hits=preferred
 if '/r1_pool_adapter_owned.rs' in v['file']:hits=[n for n in hits if '.owned.' in n]
 if '/r1_pool_adapter.rs' in v['file']:hits=[n for n in hits if '.r1_pool_adapter.' in n and '.owned.' not in n]
 hits=sorted(set(hits+[n for n in SPECIAL.get(name,[]) if n in C]))
 sources=[]
 for n in hits:
  locs=I.get(n,[])
  # Prefix replay source is preferred, but retain original declaration when not renamed.
  ranked=sorted(locs,key=lambda x:(not x['file'].startswith('evidence/replay-deployed2'),not x['file'].startswith('evidence/replay-tops3'),not x['file'].startswith('evidence/replay-'),x['file']))
  if ranked:
   loc=ranked[0];sources.append(dict(name=n,**loc))
  else:sources.append({'name':n,'file':None,'note':'reachable constant; locator needs manual source resolution'})
 v['cohort_definitions']=sources
 v['cohort_status']='named reachable cohort definition; correspondence is a bridge obligation' if sources else 'no cohort counterpart'
 # Machine parser exposes raw field-like calls, including Vec::push. Name-based tags are review aids.
 v.pop('_body',None)
(O/'NBI2_mapped.json').write_text(json.dumps(rows,indent=2)+'\n')
print('rows',len(rows),'unmapped',sum(not v['cohort_definitions'] for v in rows))
for v in rows:
 if not v['cohort_definitions']:print(v['file'].split('/')[-1]+'::'+v['name'])
