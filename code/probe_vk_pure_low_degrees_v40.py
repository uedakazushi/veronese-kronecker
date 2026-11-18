#!/usr/bin/env python3
"""Optional exact low-degree probes; no all-m assertion is inferred."""
from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
from vk_all_weights_model_v40 import Corner
HERE=Path(__file__).resolve().parent

def compute():
    rows=[]
    for m in (3,4,5):
        for s in (0,1):
            a=Corner(0,m,s=s).ranks('N')
            a['HH_dimensions']=[1,a['cohomology'][0]-3,a['cohomology'][1],a['cohomology'][2]]
            rows.append(a)
    return {'version':40,'status':'PASS','scope':'Exact m=3,4,5 probes only; general pure hull and all-m HH comparison are not proved.','cases':rows}

if __name__=='__main__':
    actual=compute()
    expected=json.loads((HERE/'vk_pure_low_degrees_v40_probe.json').read_text())
    assert actual==expected,'probe mismatch'
    print(json.dumps(actual,indent=2,sort_keys=True))
