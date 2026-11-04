"""Account for every std/scalar/constructor inventory boundary explicitly."""
def law(call):
 text=call.get('expression',call.get('syntax'))
 if text=='queries.len':return ['Array length22 and exact range guard','NFB_K015/016','NFB_RangeTrace.selected']
 if text in ['Err','Ok']:return ['Exact Result constructor, all variants retained','NFB_K015/016;NFB_K017..026;NFB_K101..106','NFB_GeometryComposed.result_state_effects']
 if text=='Vec::with_capacity':
  return ['Fresh uniquely owned successful allocation; approved Allocator/abort trust retained','NEW_K081..086;NFB_K047..054','NFB_ReturnedBuffers.initial_frame;NFB_TerminalAssociation.complete']
 if '.map_err' in text:return ['Same checked domain/error tag and ordering','NFB_K029..032','NFB_RowG.complete;NFB_RowIndex.indexPort']
 if text=='values.iter().any':return ['Same fixed5 slice, one iterator/callback step, finite early-stop induction and pinned std Iter::any','NFB_K002..009','NFB_ZeroScan.zero_loop;NFB_ZeroFinite.complete']
 if text=='values.iter':return ['Same fixed5 slice/cursor','NFB_K002..007','NFB_ZeroFinite.next_active']
 if text=='flat.extend_from_slice':return ['Reserve once, initialize new fixed5 window, preserve every arbitrary old live offset and allocation','NEW_K041..044;NEW_K071..074','NFB_GatherFrame.payloads;NFB_RootGather.complete']
 if text=='line_z_values.push':return ['Same Vec append and old windows, no capacity growth at k<N','NEW_K048..053','NFB_GatherFrame.payloads;NFB_TraceBounds.terminal_bound']
 if text=='flat.is_empty':return ['Metadata comparison; empty success unreachable in deployed nonempty successful range','NFB_K096/097;NEW_K081..086','NFB_AcceptedGather.complete;NFB_ReturnedBuffers.complete']
 if text=='Vec::new':return ['Empty constructor in branch unreachable for deployed successful nonempty range','NFB_K096/097','NFB_AcceptedGather.complete']
 if text=='flat.len' or text=='line_z_values.len':return ['SAME mutable payload length, derived count10/12 and size50/60','NEW_K048..053;NFB_K033..040;NFB_K080..085','NFB_TerminalAssociation.complete;NFB_GeometryComposed.accepted_physical']
 if text=='flat_inverse.resize':return ['One actual std append at arbitrary live pre-state, uninitialized spare and SetLenOnDrop, finite induction','NFB_K033..046','NFB_ResizeAssociation.complete;NFB_ResizeAssociation.payload']
 if text=='(0..flat.len()).rev':return ['Actual reverse iterator, two ordered opaque products and SAME inverse write/frame','NEW_K045..047;NEW_K068..070','NFB_ReverseAssociation.complete;NFB_BackwardTransport.complete']
 if text.endswith('.collect'):
  return ['TrustedLen Map<Range<usize>> fixed5 array records, guard-local store then publication','NFB_K072..085;NFB_K098..100','NFB_CollectorTrace.meaning;NFB_TerminalAssociation.complete']
 if text=='(0..line_z_values.len()).map':return ['Exact map capture, immutable inverse, ordered row cursor; std TrustedLen dispatch pinned','NEW_K060..063;NFB_K086..093','NFB_CollectAssociation.complete;Port4C_CollectLoop.list_total']
 if text=='core::array::from_fn':return ['One exact Guard slot at arbitrary initialized prefix, all lanes, final initialized array transfer','NFB_K086..093;NFB_K098..100','NFB_CollectorTrace.meaning;NFB_CollectAssociation.array_complete']
 raise AssertionError(('unclassified external',text))
def check(row):
 out={}
 for o in row['caller_domain_obligations']:
  if 'callee' in o:continue
  out[o['id']]=dict(call=o['call'],law=law(o['call']),status='CLOSED')
 assert len(out)==26
 inventory=[]
 for o in row['inventory_domain_obligations']:
  assert (row['row'],o['unit']) in [('TX1:181','geometry'),('TX2:104','U08')]
  inventory.append(dict(unit=o['unit'],original_domain=o['domain'],status='CLOSED',
   discharge='Stronger all-raw full Result association NEW_L079 and NFB_GeometryComposed; NFB_AcceptedGather and TerminalAssociation bind SAME vectors and reciprocal grouping. Rejections retained; distinctness is not needed by this correspondence. Canonical nonzero and reciprocal mathematical conclusion is NEW_GeometryComplete.accepted, not an inner precondition.'))
 return out,inventory
