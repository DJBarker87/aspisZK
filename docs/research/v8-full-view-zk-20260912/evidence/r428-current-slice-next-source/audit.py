import pathlib,json,hashlib,re,ast
H=pathlib.Path(__file__).resolve().parent; S=H/'saved-output'; checks=[]
def check(name,v):
 checks.append({'name':name,'pass':bool(v)})
 if not v: raise AssertionError(name)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((S/'result.json').read_text()); a=json.loads((S/'host-reservation-before.json').read_text()); b=json.loads((S/'host-reservation-after.json').read_text()); d=json.loads((S/'R428SliceNextSource.llbc').read_text())
check('child and GNU time status',r['charon_exit_status']==r['gnu_time_exit_status']==0)
check('no extraction errors',r['has_errors'] is False and d['has_errors'] is False)
check('all output checksums',r['llbc_sha256']==sha(S/'R428SliceNextSource.llbc') and r['charon_stdout_sha256']==sha(S/'charon.stdout.log') and r['charon_stderr_sha256']==sha(S/'charon.stderr.log'))
check('source pins stable',a['source_hashes_before']==b['source_hashes_after']==r['source_hashes_before_after']['before']==r['source_hashes_before_after']['after'])
check('Std source pins stable',a['stdlib_hashes_before']==b['stdlib_hashes_after'])
check('baseline stable',a['baseline_sha_before']==b['baseline_sha_after']==r['baseline_sha256_before_after'][0]==r['baseline_sha256_before_after'][1])
check('actual cgroup caps',all((x['memory.high'],x['memory.max'],x['memory.swap.max'],x['pids.max'])==('5368709120','7516192768','0','128') for x in [a['effective_cgroup_before'],b['effective_cgroup_after']]))
check('no cgroup swap or OOM',b['effective_cgroup_after']['memory.swap.current']=='0' and b['effective_cgroup_after']['memory.swap.peak']=='0' and all(int(v)==0 for k,v in (x.split() for x in b['effective_cgroup_after']['memory.events'].splitlines()) if k.startswith('oom')))
check('own group same',a['effective_cgroup_before']['path']==b['effective_cgroup_after']['path'] and 'aspis-r428-slice-next-source.service' in a['effective_cgroup_before']['path'])
base=H.parent/'base-r327/extract-command.json'; check('base plan checksum',sha(base)=='021c55ed604170e5982365f714d4abd46edf4b14ad0d626b1c59d25f8b6da1ad')
o=json.loads(base.read_text());c=json.loads((S/'extract-command.json').read_text());cmd=c['command'].copy();i=cmd.index('core::slice::iter::_::next');del cmd[i-1:i+1];cmd[cmd.index('--dest-file')+1]=o['command'][o['command'].index('--dest-file')+1];check('exact argv scope and destination delta',cmd==o['command'])
check('flags unchanged',a['rustflags']==o['rustflags'] and c['monomorphize'] is True)
f=d['translated']['fun_decls'][10];check('next now transparent structured',f['item_meta']['opacity']=='Transparent' and 'Structured' in f['body'])
check('actual instantiated B(u32)',d['translated']['type_decls'][0]['item_meta']['source_text']=='struct B(u32);')
g=(S/'gnu-time.txt').read_text();check('GNU metrics agree',r['wall_time']=='0:14.65' and r['peak_rss_kib']==628696 and r['swap_count']==0 and 'Maximum resident set size (kbytes): 628696' in g)
report={'status':'PASS','checks':checks,'target':c['start_from'],'LLBC_sha256':r['llbc_sha256'],'result':r,'effective_cgroup_after':b['effective_cgroup_after'],'boundary':'Source capture of Iter<B>, not source execution proof or actual QM31 freeze binding.','first_remaining_proposition':'Establish source-faithful mutable receiver and pointer/cursor execution for actual freeze specialization, preserving stopping/errors and original slice reference lifetime.','axioms':'N/A no Lean proof compiled'}
(H/'lead-audit.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS',len(checks),'checks')
