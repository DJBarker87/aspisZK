"""cfg(kani)-only contracts; frozen function bodies stay unchanged."""
def overlay(raw):
 s=raw.decode()
 for name,ty in [('bits','u32'),('width','usize'),('levels','u32')]:
  needle='    pub const fn '+name+'(self) -> '+ty+' {'
  attrs=f'''    #[cfg_attr(all(kani, not(NJA_bad_{name})), kani::ensures(|result: &{ty}| *result == NJA_contracts::NJA_{name}_ref(self)))]
    #[cfg_attr(all(kani, NJA_bad_{name}), kani::ensures(|result: &{ty}| *result != NJA_contracts::NJA_{name}_ref(self)))]
'''
  assert s.count(needle)==1;s=s.replace(needle,attrs+needle)
 return s.encode()
