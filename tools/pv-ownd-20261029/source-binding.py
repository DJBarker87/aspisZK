"""Pin initial schedule source spans and check their ordered statements.
This partial binding never labels an unproved native stack counter as closed.
"""
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownd-20261029'
base='1e44071977';tree='crates/aspis-statement/src/pool_v1/pair_tree_hiding.rs';profile='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'
rows=[]
def span(path,start,end,ordered,laws,difference):
 b=subprocess.check_output(['git','show','HEAD:'+path]);original=subprocess.check_output(['git','show',base+':'+path]);assert b==original,path
 text='\n'.join(b.decode().splitlines()[start-1:end])+'\n';pos=0
 for s in ordered:
  i=text.find(s,pos);assert i>=0,(path,start,s);pos=i+len(s)
 rows.append(dict(path=path,start_line=start,end_line=end,source_sha256=hashlib.sha256(b).hexdigest(),span_sha256=hashlib.sha256(text.encode()).hexdigest(),text=text,ordered_statements=ordered,model_laws=laws,differences=difference))
span(tree,86,97,['kind,','producer_row: producer_row as u16','consumer_row: consumer_row as u16'],['PV_OWND_LegacySource.link','PV_OWND_SourceBounds.word_room'],['Rust integer casts represented by UInt16.ofNat; bounded arithmetic; selected Link layout inherited from ownb; V370 retained'])
span(tree,105,131,['Vec::with_capacity(POOL_V1_PAIR_COPY_ROW_LINKS_V1)','for (from, to) in [','links.push(link(','SpongeCarry','OwnerOutput','NullifierKey','InputSaltHead','InputSaltTail'],['PV_OWND_FixedPhases.sponge_source','PV_OWND_AllocationBuffer.valid'],['Seven ordered pushes use a list map plus typed store fold; list-fold composition is separate checked law'])
span(tree,133,153,['for level in 0..POOL_V1_PAIR_PRIVATE_DIRECTIONS','pool_v1_pair_path_base_row_v1(level).ok_or','PrivatePathCurrent','PrivatePathLeft','PrivatePathRight'],['PV_OWND_PrivatePhase.source','PV_OWND_SourceBounds.helper_success'],['21 bounded source iterations; named per-level complete Link cells retain payloads; error helper branch unreachable on range'])
span(tree,155,222,['[(0u8, 44usize, 960usize), (1, 460, 962), (2, 508, 964)]','ValueSource','ConservationInput','ConservationRecipient','ConservationChange','ConservationPartial','InputSecondCommitment','InputSelectedSide','OutputSecondCommitment','OutputPairFirst,','OutputPairFirstWithdrawal','OutputPairSecond,'],['PV_OWND_FixedPhases.value_source','PV_OWND_LegacySource.conservation','PV_OWND_LegacySource.occupancy'],['Scalar source link constructors retain all kind fields; aux(0)=865 is a named level cell'])
span(tree,224,248,['for level in 0..20usize','AppendCurrentLeft','AppendCurrentRight','if links.len() !=','return Err(','endpoint_counts(&links)?','Ok(links)'],['PV_OWND_AppendPhase.source','PV_OWND_LegacyCount.count','PV_OWND_SourceShape.no_shape_error','PV_OWND_InitialCheck.checks'],['Shape branch has length proof; endpoint stack-array initialization/access/world binding remains open; checks is a scalar interpretation, not a native law'])
span(tree,246,263,['let mut producers = [0u8; 1024]','let mut consumers = [0u8; 1024]','for link in links','usize::from(link.producer_row)','usize::from(link.consumer_row)','if row >= POOL_V1_PAIR_TRACE_ROWS || counts[row] >= 2','return Err(','counts[row] += 1','Ok((producers, consumers))'],['PV_OWND_EndpointCounter.check','PV_OWND_CounterOrder.success','PV_OWND_CounterBounds.byte_room'],['OPEN: two concrete stack byte arrays, mutable counts handles and their backwards restoration/store instance; no extraction credit claimed'])
span(profile,351,361,['if level >= POOL_V1_PAIR_PRIVATE_DIRECTIONS','return None','POOL_V1_PAIR_PATH_AUX_ROW_START','level / POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK','2 * (level % POOL_V1_PAIR_DIRECTIONS_PER_AUX_BLOCK)'],['PV_OWND_SourceBounds.private_aux','PV_OWND_SourceBounds.helper_success','PV_OWND_SourceBounds.helper_failure'],['Nat arithmetic bounded before usize/u16 transport; deployed constants 21,4,864,16,1'])
obj=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),base=base,evidence_class='partial source structural coverage preflight; not a complete structural (K-1 substitute) gate',complete=False,compiler_boundary='V370 at D381/D386 retained',trust='Rust/compiler semantic agreement is reclassification within existing tool trust; runtime primitives rdea-1 retained; T unchanged',rows=rows)
(E/'initial-source-binding.json').write_text(json.dumps(obj,indent=2)+'\n');print(len(rows),'source spans checked; complete=false')
