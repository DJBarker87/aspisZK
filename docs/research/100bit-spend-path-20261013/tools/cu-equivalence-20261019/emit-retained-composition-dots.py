#!/usr/bin/env python3
"""Unify adjacent source kernels through explicit opaque dot API parameterization."""
from pathlib import Path
import argparse,re,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];lean=area/'lean';sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
def blocks(s,ns):
 head,*parts=re.split(r'(?m)(?=^/--)',s);out={}
 for part in parts:
  part=part.removesuffix('end '+ns+'\n').rstrip()
  m=re.search(r'\b(?:def\s+|def\s*\n\s*|structure\s+|inductive\s+)([\w.]+)',part);assert m,part[:100]
  out[m[1]]=part+'\n\n'
 return head,out
def code(block):return re.sub(r'/--.*?-/', '',block,flags=re.S).strip()
source=(lean/'AspisR1DelayedDots/Funs.lean').read_text();assert '.sums'not in source and '.count'not in source
# All dot values occur at new/push/finish or as forwarded arguments/state; no dot projection.
assert len(re.findall(r'self\.c[01]',source))==8
_,db=blocks(source,'AspisR1DelayedDots');_,pb=blocks((lean/'AspisR1CuDots/Funs.lean').read_text(),'AspisR1CuDots')
shared_middle=[]
for name,raw in db.items():
 if name.startswith('new_dots.'):
  other=name.replace('new_dots.','old_dots.',1);assert code(raw).replace('new_dots.','old_dots.')==code(pb[other]),name;shared_middle.append(name)
assert len(shared_middle)==19
head,dt=blocks((lean/'AspisR1DelayedDots/Types.lean').read_text(),'AspisR1DelayedDots');_,pt=blocks((lean/'AspisR1CuDots/Types.lean').read_text(),'AspisR1CuDots')
shared_types=['field.M31','field.CM31','field.QM31','field.wide_exact.WideExact'];opaque=['fast_pairing.canonical.Dot','fast_pairing.EbyKDot']
for name in shared_types:assert code(dt[name])==code(pt[name]),name
for name in shared_types+opaque:dt[name]='abbrev '+name+' := AspisR1CuDots.'+name+'\n\n'
head=head.replace('import Aeneas','import AspisR1CuDots.Types').replace('namespace AspisR1DelayedDots','namespace AspisR1RetainedDots')
types=head+''.join(dt.values())+'end AspisR1RetainedDots\n'
outputs={lean/'CuSavingsRetainedCompositionDotsTypes.lean':types}
external=(lean/'AspisR1DelayedDots/FunsExternal.lean').read_text().replace('AspisR1DelayedDots.Types','CuSavingsRetainedCompositionDotsTypes').replace('AspisR1DelayedDots','AspisR1RetainedDots')
outputs[lean/'CuSavingsRetainedCompositionDotsExternal.lean']=external
funs=source.replace('AspisR1DelayedDots.Types','CuSavingsRetainedCompositionDotsTypes').replace('AspisR1DelayedDots.FunsExternal','CuSavingsRetainedCompositionDotsExternal').replace('AspisR1DelayedDots','AspisR1RetainedDots')
outputs[lean/'CuSavingsRetainedCompositionDotsSource.lean']=funs
# Prefix-new exact declarations; its old nineteen declarations are the shared middle above.
_,prefix_types=blocks((lean/'AspisR1CuDots/Types.lean').read_text(),'AspisR1CuDots')
prefix_head='import CuSavingsRetainedCompositionDotsSource\nimport CuSavingsPrefix\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnamespace AspisR1RetainedDots\nvariable [Shared]\n'
prefix_body=''.join(v.replace('new_dots.','prefix_new_dots.') for k,v in prefix_types.items()if k.startswith('new_dots.'))
prefix_body+=''.join(v.replace('new_dots.','prefix_new_dots.')for k,v in pb.items()if k.startswith('new_dots.'))
outputs[lean/'CuSavingsRetainedCompositionDotsPrefixSource.lean']=prefix_head+prefix_body+'end AspisR1RetainedDots\n'
delayed=['Scalar','Arrays','Common','LimbLoop','Materialize','Batches','Kernel','Candidate4']
prefix=['Slot','BaseStep','BaseProgress','Base','Batches','Tail','SlotPost','SlotPrefix','SameBytes','PrefixKernel']
mapping={('CuSavingsDelayed'+n):('CuSavingsRetainedCompositionDelayed'+n)for n in delayed}
mapping.update({('CuSavingsDots'+n):('CuSavingsRetainedCompositionPrefix'+n)for n in prefix})
for old,new in mapping.items():
 s=(lean/(old+'.lean')).read_text()
 # Namespace/import substitutions only; existing symbolic proof bodies retained.
 for x,y in mapping.items():s=re.sub(r'\b'+re.escape(x)+r'\b',y,s)
 s=s.replace('AspisR1DelayedDots.Funs','CuSavingsRetainedCompositionDotsSource').replace('AspisR1DelayedDots','AspisR1RetainedDots')
 s=s.replace('AspisR1CuDots.Funs','CuSavingsRetainedCompositionDotsPrefixSource').replace('AspisR1CuDots','AspisR1RetainedDots')
 if old.startswith('CuSavingsDots'):
  s=s.replace('[Arithmetic]','[Shared]');s=s.replace('new_dots.','prefix_new_dots.').replace('old_dots.','new_dots.')
 outputs[lean/(new+'.lean')]=s
meta=dict(middle_declarations_source_identical=shared_middle,shared_nominal_field_declarations=shared_types,opaque_dot_carriers=opaque,opaque_dot_parameterization='Dot representation is not claimed byte-identical: candidate5 removed private counters. Source4 numerical kernel only calls Shared new/push/finish and forwards dot values; zero dot projections/constructors in all source/proof bodies. This local source-parametric ADT abstraction shares current source Dot carrier, holding actual interface computations fixed per replacement. Existing proofs are rechecked on this carrier. No propositional ADT or candidate-equivalence law added.',field_state_observation_audit=dict(source_dot_count_projections=0,source_dot_sums_projections=0,all_self_coordinate_projections_are_wide_limb_extraction=8),proof_mapping=mapping,outputs={str(p.relative_to(area)):sha(s)for p,s in outputs.items()})
for p,s in outputs.items():
 if a.check:assert p.read_text()==s,p
 else:p.write_text(s)
p=tool/'retained-composition-dots-emission.json';s=json.dumps(meta,indent=2)+'\n'
if a.check:assert p.read_text()==s
else:p.write_text(s)
print(json.dumps(dict(check=a.check,middle_declarations_identical=len(shared_middle),targets=len(outputs),opaque_dot_no_field_inspection=True)))
