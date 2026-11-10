#!/usr/bin/env python3
"""PCUI_emissions.py: label every committed fresh emission directory with its overflow configuration
(ON when its PINS/spec record -C overflow-checks=yes or CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true; OFF_DEFAULT when
the stager ran with no overflow flag, release profile default). Output PCUI_EMISSION_CONFIG.json."""
import json,glob,os,re,sys
sys.dont_write_bytecode=True
EV=os.path.abspath(os.path.join(os.path.dirname(__file__),'..'))
out={}
on=False
for d in sorted(glob.glob(EV+'/*/*_emitted')):
    rel=os.path.relpath(d,EV)
    texts=''
    for f in glob.glob(d+'/*PINS.json')+glob.glob(d+'/../*_spec.json')+glob.glob(d.replace('_emitted','_spec.json')):
        try: texts+=open(f).read()
        except Exception: pass
    on=False; off_explicit=False; has_pins=bool(glob.glob(d+'/*PINS.json'))
    def walk(o):
        global on
        if isinstance(o,dict):
            for k,v in o.items():
                if k=='CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS' and str(v).lower()=='true': on=True
                if k in('RUSTFLAGS',) and isinstance(v,str) and 'overflow-checks=yes' in v: on=True
                walk(v)
        elif isinstance(o,list):
            for v in o: walk(v)
    for f in glob.glob(d+'/*PINS.json')+glob.glob(d.replace('_emitted','_spec.json')):
        try: j=json.load(open(f))
        except Exception: continue
        walk(j)
    cfg='ON' if on else ('OFF_EXPLICIT' if off_explicit else ('OFF_DEFAULT' if has_pins else 'UNRECORDED'))
    mods=[os.path.basename(p) for p in glob.glob(d+'/raw/*') if os.path.isdir(p)]
    out[rel]=dict(config=cfg,modules=mods,pins=has_pins)
json.dump(out,open(os.path.join(os.path.dirname(__file__),'PCUI_EMISSION_CONFIG.json'),'w'),indent=1)
import collections
print(collections.Counter(v['config'] for v in out.values()))
