#!/usr/bin/env python3
"""NPH_: recount judgments and rows exposed from NPH_R22_CONE.json (read-only).
Rows exposed = rows touched by an executed checked/mixed definition that depend on at least one
OPEN or DOMAIN_LEMMA_PROVED definition. NOT_EXECUTED definitions are excluded."""
import json,collections,sys
c=json.load(open(sys.argv[1] if len(sys.argv)>1 else 'NPH_R22_CONE.json'))
def J(e):
    j=(e.get('nph_judgment') or '').split(' ')[0].rstrip(':')
    return j
cnt=collections.Counter();touched=set();bad=set()
for e in c['definitions']:
    if e['body_class'] not in ('CHECKED','MIXED'):continue
    j=J(e);cnt[j]+=1
    if j=='NOT_EXECUTED':continue
    touched|=set(e['rows'])
    if j in ('OPEN','DOMAIN_LEMMA_PROVED'):bad|=set(e['rows'])
print(json.dumps(dict(counts=cnt,touched=len(touched),exposed=len(bad),served=len(touched-bad)),default=dict))
