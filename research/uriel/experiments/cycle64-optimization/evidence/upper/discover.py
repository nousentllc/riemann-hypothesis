"""Optional replay of adverse-label discovery. The default upper check uses the saved word."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import random
import subprocess
from tempfile import TemporaryDirectory

from run import compile_program


def interlace(left, right):
    return sum(((word >> (s-1+c)) & 1) << (2*s-1+2*c+b)
               for b,word in enumerate([left,right]) for s in (1,2,4,8,16) for c in range(s))


def experiment(binary, workers):
    random_words = random.Random(648421923)
    words = [interlace(8421923,8421923)] + [random_words.getrandbits(63) for _ in range(120)]
    def measure(word, a, c):
        return list(map(int,subprocess.check_output([binary,str(word),str(a),str(c)],text=True).split()))
    with ThreadPoolExecutor(max_workers=workers) as pool:
        records=list(pool.map(lambda word:measure(word,13,100),words))
        inspected=sorted((round(line[4]/line[5],9),line[0]) for line in records)
        beam=[word for _,word in inspected[:4]]
        print("Initial candidate words",beam,flush=True)
        mutations=random.Random(2164497)
        cache={}
        for epoch in range(12):
            candidates=set()
            for word in beam:
                candidates.add(word)
                candidates.update(word^(1<<j) for j in range(63))
                candidates.update(word^sum(1<<j for j in mutations.sample(range(63),3))
                                  for _ in range(12))
            for line in pool.map(lambda w:measure(w,23,200),sorted(candidates-cache.keys())):
                cache[line[0]]=(line[3],line[0],line[4],line[5])
            beam=[]
            for row in sorted(cache[w] for w in candidates):
                if all((value^row[1]).bit_count()>=2 for value in beam):
                    beam.append(row[1])
                    if len(beam)==4:
                        break
            print(epoch,len(cache),[cache[w] for w in beam],flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers",type=int,default=2)
    args=parser.parse_args()
    with TemporaryDirectory() as temp:
        experiment(compile_program("bound",Path(temp)),args.workers)


if __name__=="__main__":
    main()
