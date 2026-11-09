import json,collections,sys
sys.dont_write_bytecode=True
EV='..'
idx=json.load(open('PCUF_EMISSION_INDEX.json'))
SUP={"PCQC_E002","PCQC_E003","PCQC_E004","PCQC_E011","PCQ_E039","PCQ_E040"}
def variants(rel):
    return [rel, rel[len('aspis_core.'):] if rel.startswith('aspis_core.') else 'aspis_core.'+rel]
def match(rel):
    out=[]
    for e,ent in idx.items():
        if not ent['eligible']: continue
        for k in('Types','Funs'):
            for v in variants(rel):
                nm=ent.get(k,{})
                if v in nm and nm[v] not in('axiom','opaque'): out.append((ent['run'],k,v))
    return out
sel=collections.defaultdict(lambda:collections.defaultdict(list))
origin={}
allmods={}
for f,tool in [("prov-p2r-20261109/PCUE_EQ_STATUS.json","P2r"),("prov-p2b-20261109/PCUB_EQ_STATUS.json","P2b"),("prov-p2c-20261109/PCUC_EQ_STATUS.json","P2c")]:
    d=json.load(open(f"{EV}/{f}"))["modules"]
    for m,v in d.items():
        origin[m]=tool; allmods[m]=list(v["reached"])
        for n,r in v["reached"].items():
            s=r["status"]; js=json.dumps(r); used={x for x in SUP if x+"_emitted" in js or ('"fresh_run": "%s"'%x) in js}
            rel=n.split('.',1)[1] if '.' in n else n
            mt=match(rel)
            if s in("NO_FRESH_EMISSION","FRESH_EXTERNAL_AXIOM_ONLY","NO_COMMON_LEAN_NAME") and mt: sel[m]['target_new'].append(n)
            elif s=="FAILED" and used: sel[m]['target_failed_superseded'].append(n)
            elif s.startswith("PROVED") and used: sel[m]['recheck_superseded'].append(n)
json.dump({m:{k:v for k,v in d.items()} for m,d in sel.items()},open('selected_modules.json','w'),indent=1)
json.dump(origin,open('module_origin.json','w'),indent=1)
json.dump(allmods,open('module_reached.json','w'),indent=1)
for m,d in sel.items(): print(origin[m],m,{k:len(v) for k,v in d.items()})
print(len(sel))
