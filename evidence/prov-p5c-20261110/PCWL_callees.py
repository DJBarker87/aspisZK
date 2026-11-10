import json,sys
d=json.load(open('../prov-p6r-20261110/PCXD_PROVENANCE.json'))['modules']
keys=sys.argv[1:]
for mod,v in d.items():
  for n,x in v['definitions'].items():
    if any(k in n for k in keys):
      print(mod,'|',n,'|',x.get('status') or x.get('class'),'|',x.get('configuration'),'|',x.get('theorem'),'|',x.get('proving_file'))
