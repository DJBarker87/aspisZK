"""Material358 producer. Historical material357 producer and source are immutable inputs."""
import pathlib
T=pathlib.Path(__file__).resolve().parent
E=T.parents[1]/'evidence/port32consumer-20261025'
OLD='''  let d := Declaration.defnDecl { name := n, levelParams := [], type := ty,
    value := instances[0]!, hints := .abbrev, safety := .safe, all := [n] }'''
NEW='  let d := Declaration.defnDecl (mkDefinitionValEx n [] ty instances[0]! .abbrev .safe [n])'
def material():
 s=(E/'Port32CONSUMER_source-357.lean.txt').read_text()
 assert s.count(OLD)==1
 return s.replace(OLD,NEW)
if __name__=='__main__':
 (T/'Port32CONSUMER_Consumer358.lean').write_text(material())
