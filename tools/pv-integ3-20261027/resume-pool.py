from gates import call,E
import json
labels={'default':'build-default-executable-wrapper','devnet':'build-devnet-executable-wrapper'}
labels['pool']=call('build.py',['candidate','pool','{label}'],'build-pool-affinity4')
(E/'elf-labels.json').write_text(json.dumps(labels,indent=2)+'\n')
