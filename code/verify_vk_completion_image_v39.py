#!/usr/bin/env python3
"""Read-only exact comparison of standard-completion and pure-curve tangents.

This is a compatibility check between two independently computed bar
certificates. The complete closed-embedding statement is proved formally in
the manuscript, using the established dual-number ambient hull.
"""
from pathlib import Path
from fractions import Fraction
import argparse,hashlib,json

HERE=Path(__file__).resolve().parent
CODE=HERE if (HERE/'vk_completion_symmetry_v38_certificate.json').exists() else HERE.parent/'output/vk_lo_deformations_v39/code'

def compute():
    paths=[CODE/'vk_completion_symmetry_v38_certificate.json',CODE/'vk_filtered_reduction_v39_certificate.json']
    completion,filtered=[json.loads(p.read_text()) for p in paths]
    case=filtered['cases'][1]
    vector=[Fraction(row[0]) for row in completion['HH2_coordinates']]
    matrix=[[Fraction(x) for x in row] for row in case['restriction_HH2_matrix']]
    assert len(vector)==35 and len(matrix)==3 and all(len(row)==35 for row in matrix)
    image=[sum((x*y for x,y in zip(row,vector)),Fraction(0)) for row in matrix]
    pure=[Fraction(row[0]) if isinstance(row,list) else Fraction(row) for row in case['pure_gamma_HH2_class']]
    assert image==pure==[Fraction(229,120),Fraction(117,20),Fraction(-1571,60)]
    assert completion['in_kernel'] and not completion['in_image']
    assert case['invariant_restriction_rank']==1
    assert filtered['cases'][0]['invariant_restriction_rank']==0
    return {
        'version':39,'status':'PASS','arithmetic':'exact rational Fraction arithmetic',
        'scope':'Compatibility of actual standard-six-term tangent with the pure gamma curve; the all-order image is a formal-algebra consequence in the manuscript.',
        'input_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'restriction_matrix_shape':[3,35],
        'completion_pure_image':[str(x) for x in image],
        'pure_gamma_HH2_class':[str(x) for x in pure],
        'exact_equality':True,'nonzero':True,
        'completion_in_ker_L':True,'completion_in_im_L':False,
        'invariant_restriction_ranks_j0_j1':[0,1],
        'manuscript_conclusion':'After coordinates over C[[gamma]], the standard six-term image in C[[u1,...,u5,gamma]]/(gamma^2) is u1=...=u5=0.'
    }

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    result=compute()
    if args.check:
        assert result==json.loads((HERE/'vk_completion_image_v39_certificate.json').read_text())
    print(json.dumps(result,ensure_ascii=False,indent=2,sort_keys=True))
