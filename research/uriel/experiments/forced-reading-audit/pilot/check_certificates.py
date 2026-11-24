"""Enumerate distinct ID sets for each verdict and test malformed duplicate witnesses separately."""
from itertools import combinations
import json
from analyze import evaluate
from run import RECORDS


def verify():
    sets=dups=0
    for row in json.loads(RECORDS.read_bytes()).values():
        required=set(row['survivors'])
        signs={row['states'][s]['answer'] for s in required}
        target='U' if len(signs)==2 else 'Y' if True in signs else 'N'
        for n in range(9):
            for subset in combinations(row['states'],n):
                for verdict in ('Y','N','U'):
                    reply=dict(status='ok',answer=dict(verdict=verdict,certificate=list(subset)))
                    s=evaluate(row,reply)
                    if (s['ids'],s['sign'],s['certified'])!=(set(subset)==required,verdict==target,set(subset)==required and verdict==target):
                        raise ValueError(reply)
                    sets+=1
        possible=list(required)
        for dup in possible:
            reply=dict(status='ok',answer=dict(verdict=target,certificate=possible+[dup]))
            if evaluate(row,reply)['certified']:raise ValueError('Duplicate accepted')
            dups+=1
    print(f'Checked {sets} verdict/subset combinations and {dups} duplicate certificates.')


if __name__=='__main__':
    verify()
