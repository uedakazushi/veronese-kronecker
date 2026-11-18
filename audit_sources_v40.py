#!/usr/bin/env python3
"""Audit recursive TeX inputs, labels and citations; freeze current source hashes."""
from pathlib import Path
import hashlib,json,re

ROOT=Path(__file__).resolve().parent
MAINS=['quantum_categories_ja_v40','quantum_primitive_spectra_ja_v40','vk_research_notes_ja_v40']

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def collect(p):
    seen=set();todo=[p]
    while todo:
        q=todo.pop().resolve()
        if q in seen:continue
        if not q.is_relative_to(ROOT) or not q.is_file():raise RuntimeError('Missing/nonlocal TeX input '+str(q))
        seen.add(q)
        t=re.sub(r'(?<!\\)%[^\n]*','',q.read_text())
        for name in re.findall(r'\\(?:input|include)\s*\{([^}]+)\}',t):
            child=q.parent/name;todo.append(child if child.suffix else child.with_suffix('.tex'))
    return sorted(seen)

def main():
    allpaths=set();docs=[]
    for stem in MAINS:
        paths=collect(ROOT/'papers'/(stem+'.tex'));allpaths.update(paths)
        t='\n'.join(p.read_text() for p in paths)
        labels=re.findall(r'\\label\{([^}]+)\}',t)
        refs=re.findall(r'\\(?:eqref|ref|pageref|autoref)\{([^}]+)\}',t)
        bib=re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}',t)
        cites=[v.strip() for z in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}',t) for v in z.split(',')]
        missing_refs=sorted(set(refs)-set(labels));missing_cites=sorted(set(cites)-set(bib))
        duplicates=sorted(x for x in set(labels) if labels.count(x)>1)
        if missing_refs or missing_cites or duplicates:raise RuntimeError((stem,missing_refs,missing_cites,duplicates))
        docs.append({'stem':stem,'inputs':[p.relative_to(ROOT).as_posix() for p in paths],
                     'labels':len(labels),'citations':len(set(cites)),
                     'missing_references':missing_refs,'missing_citations':missing_cites,'duplicate_labels':duplicates})
    result={'version':40,'status':'PASS','documents':docs,
            'source_sha256':{p.relative_to(ROOT).as_posix():digest(p) for p in sorted(allpaths)},
            'scope':'Recursive literal TeX inputs for three current documents; references, citations and unique labels. Mathematical proofs are audited separately.'}
    out=ROOT/'verification/manuscript_source_audit_v40.json'
    out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':'PASS','recursive_inputs':len(allpaths),'documents':len(docs)}))

if __name__=='__main__':main()
