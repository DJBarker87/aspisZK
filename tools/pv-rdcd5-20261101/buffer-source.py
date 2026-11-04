"""Mechanical source-shape preparation. No native or theorem credit alone."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101'
P=R/'evidence/pv-rdcd4-20261029'
files=json.load(open(P/'buffer-dependency-sources.json'))
lex=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.S)
def tok(s):return [m[0] for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
def body(s,marker):
    a=s.index('{',s.index(marker));depth=0
    for m in lex.finditer(s,a):
        if m[0]=='{':depth+=1
        elif m[0]=='}':
            depth-=1
            if not depth:return s[a:m.end()]
    raise ValueError(marker)
def source(suffix):return next(x for x in files if x['path'].endswith(suffix))
b=source('block-buffer-0.10.4/src/lib.rs')
w=source('digest-0.10.7/src/core_api/wrapper.rs')
s=source('block-buffer-0.10.4/src/sealed.rs')
checks=[
 ('wrapper',w,w['text'][w['text'].index('impl<T> Update for'):],'fn update',
  '{let Self{core,buffer}=self;buffer.digest_blocks(input,|blocks|core.update_blocks(blocks));}',
  'PV_DL_UpdateSelected.selected_native; only original UpdateCore.update_blocks parameter retained'),
 ('buffer',b,b['text'],'pub fn digest_blocks',
  '''{let pos=self.get_pos();let rem=self.size()-pos;let n=input.len();
  if Kind::invariant(n,rem){self.buffer[pos..][..n].copy_from_slice(input);self.set_pos_unchecked(pos+n);return;}
  if pos!=0{let(left,right)=input.split_at(rem);input=right;self.buffer[pos..].copy_from_slice(left);compress(slice::from_ref(&self.buffer));}
  let(blocks,leftover)=Kind::split_blocks(input);if !blocks.is_empty(){compress(blocks);}
  let n=leftover.len();self.buffer[..n].copy_from_slice(leftover);self.set_pos_unchecked(n);}''',
  'PV_RDCD5_BufferSource.source_instance -> existing PV_DL_UpdatePlan.model; typed carrier association remains required'),
 ('get_pos',b,b['text'],'pub fn get_pos',
  '''{let pos=self.pos as usize;if !Kind::invariant(pos,BlockSize::USIZE){debug_assert!(false);unsafe{core::hint::unreachable_unchecked();}}pos}''',
  'Original Eager64 safe guard pos<64 excludes UB and formatting; U8 widening preserves val at V370'),
 ('size',b,b['text'],'pub fn size',
  '{BlockSize::USIZE}', 'PV_AL_SplitNativeShape.native_size; concrete U64 only'),
 ('set_pos',b,b['text'],'fn set_pos_unchecked',
  '{debug_assert!(Kind::invariant(pos,BlockSize::USIZE));self.pos=pos as u8;}',
  'PV_RDCD5_BufferSource.cursor_transport; all assigned values<64; debug assertions inactive in deployed release'),
 ('Eager.invariant',s,s['text'][s['text'].index('impl Sealed for super::Eager'):],'fn invariant',
  '{pos<block_size}', 'Original safe Eager domain; zero-sized/Unit Lazy marker is never used as evidence of Eager selection')]
rows=[]
for label,p,text,marker,expected,law in checks:
    actual=body(text,marker)
    assert tok(actual)==tok(expected),label
    rows.append(dict(step=label,path=p['path'],file_sha256=p['sha256'],
      body=actual,body_sha256=hashlib.sha256(actual.encode()).hexdigest(),
      tokens_sha256=hashlib.sha256('\0'.join(tok(actual)).encode()).hexdigest(),
      token_identity=True,expected=expected,law=law,status='source shape checked; Lean proof uncompiled'))
out=dict(row='V236',status='PREPARATION ONLY',evidence_class='structural (K-1 substitute), within existing compiler/tool trust; not premise removal',
 bindings=rows,existing_link='PV_DL_UpdatePlan.model; PV_DL_UpdateCarrier.value; PV_DL_UpdateSelected.selected_native',
 qualifiers=['original safe private Eager64 cursor<64','original native byte-slice word bound',
 'same complete Result-valued batched compression callback; no callback totality or singleton-fold premise',
 'V233 typed Eager split/carrier association still required','V370/D381/D386 source-to-codegen boundary retained',
 'D159 physical/formatting observer link remains a separate original obligation'],
 fmt_1='No Aeneas.Std core::fmt semantics is used. get_pos UB/debug diagnostic excluded by original safe guard; release debug_assert inactive. All checked buffer windows require symbolic bounds.',
 originals_reused='99328 native/reference finite pairs and recovered original checker retained unchanged; no unchanged suite rerun',
 before='Concrete source buffer branch/cursor/callback transport unbound at original link',
 after='Unchanged target, uncompiled drafts; row remains SUSPENDED',
 endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[],kani_runs=0)
(E/'v236-source-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('Six exact source shapes checked; source law and row restoration still pending.')
