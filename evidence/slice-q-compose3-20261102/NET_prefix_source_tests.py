import unittest
from pathlib import Path
import NET_prefix_source as s
class Source(unittest.TestCase):
 def test_positive(self):self.assertEqual(len(s.check()['capacity_classes']),22)
 def deny(self,a,b):
  text=(s.E/'NET_prefix.rs.txt').read_text();self.assertIn(a,text)
  with self.assertRaises(AssertionError):s.check(text.replace(a,b))
 def test_append_operand(self):self.deny('prefixes.push(product);','prefixes.push(reply);')
 def test_field_argument(self):self.deny('NET_product(product,value,reply,log)','NET_product(value,product,reply,log)')
 def test_index(self):self.deny('let index=index+1;','let index=index+2;')
 def test_order(self):self.deny('prefixes.push(product);\n let product=NET_product(product,value,reply,log);','let product=NET_product(product,value,reply,log);\n prefixes.push(product);')
 def test_spare_assumption(self):self.deny('while initialized<i','while initialized<M')
 def test_capacity_coverage(self):self.deny('prefix!(NET_prefix_22,110);','')
 def test_argument_log(self):self.deny('a:a.0,b:b.0,reply:reply.0','a:b.0,b:a.0,reply:reply.0')
if __name__=='__main__':unittest.main()
