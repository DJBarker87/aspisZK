#!/usr/bin/env python3
"""NPH_: set the judgment of named cone definitions in NPH_R22_CONE.json (any target class: the first
word of the judgment text), keeping the previous judgment under nph_judgment_before_<tag>, recording
an optional R22 pattern class (field nph_pattern_class), then recount counts and rows exposed.
Usage: NPH_move.py <tag> <judgment-text-file|-> <theorems,comma> <pattern-class|-> <def1> [<def2> ...]
With '-' as judgment file only the pattern class is recorded (judgment unchanged)."""
import json,sys,collections
tag,jf,ths,pc=sys.argv[1:5];defs=sys.argv[5:]
text=None if jf=='-' else open(jf).read().strip();ths=[t for t in ths.split(',') if t]
p='NPH_R22_CONE.json';c=json.load(open(p))
J=lambda e:(e.get('nph_judgment') or '').split(' ')[0].rstrip(':')
hit=0
for e in c['definitions']:
    if e['definition'] in defs:
        assert e['body_class'] in ('CHECKED','MIXED'),e['definition']
        if text is not None:
            assert J(e) in ('DOMAIN_LEMMA_PROVED','OPEN'),(e['definition'],J(e))
            e['nph_judgment_before_'+tag]=e['nph_judgment'];e['nph_judgment']=text
        if ths:e['nph_theorems']=list(dict.fromkeys(e.get('nph_theorems',[])+ths))
        if pc!='-':e['nph_pattern_class']=pc
        hit+=1
assert hit==len(defs),(hit,defs)
cnt=collections.Counter();bycls=collections.Counter();touched=set();bad=set()
for e in c['definitions']:
    if e['body_class'] not in ('CHECKED','MIXED'):continue
    j=J(e);cnt[j]+=1;bycls[e['body_class']+'/'+j]+=1
    if j=='NOT_EXECUTED':continue
    touched|=set(e['rows'])
    if j in ('OPEN','DOMAIN_LEMMA_PROVED'):bad|=set(e['rows'])
for k in ['TOTAL_PROVED','DIRECT','DOMAIN_LEMMA_PROVED','PRECONDITION_B','OPEN','NOT_EXECUTED']:c['counts_checked_and_mixed'][k]=cnt[k]
c['counts_by_class']=dict(sorted(bycls.items()))
c['rows']['touched_by_executed_checked_or_mixed']=len(touched);c['rows']['with_at_least_one_open_or_domain_only_definition']=len(bad)
c['rows']['served_only_by_TOTAL_or_DIRECT_definitions']=len(touched-bad)
s=f"{cnt['TOTAL_PROVED']}/{cnt['DIRECT']}/{cnt['DOMAIN_LEMMA_PROVED']}/{cnt['PRECONDITION_B']}/{cnt['OPEN']} of {sum(cnt.values())-cnt['NOT_EXECUTED']}; rows exposed {len(bad)} of {len(touched)}"
what=(text.split(' ')[0].rstrip(':') if text else 'pattern class only')
c['revision_note']=f"updated {tag}: {', '.join(defs)} -> {what}; counts {s}. Previous: "+c['revision_note']
json.dump(c,open(p,'w'),indent=1,ensure_ascii=False);print(s)
