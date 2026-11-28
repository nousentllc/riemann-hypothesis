"""Exact compressed computation on the cyclic source frame of order 2**64."""
from fractions import Fraction
from math import gcd, log
import json

from experiment import ELL, K, R, EPS


N = 2**64
X = 2**27
FIRST_END = ELL
SECOND_END = FIRST_END + 9510
BLOCKS, UNUSED = divmod(N - SECOND_END, 14)
TAIL_END = SECOND_END + 14*BLOCKS
DROP, ADD = 2, ELL
WIDTH = 3872
Q = 236789744721782169152365302750626042756803
D = 135688505402369557604164386969459867197719


def prime_certificate(p, multiplier, base):
    """Every prime divisor has order obstruction forcing it to exceed sqrt(p)."""
    F = 3**82
    assert p-1 == multiplier*F and F*F > p
    assert pow(base, p-1, p) == 1
    assert gcd(pow(base, (p-1)//3, p)-1, p) == 1
    return {"prime":str(p), "multiplier":multiplier, "base":base, "power_of_three":82}


def count_below(t, edited):
    """Number retained at indices i with 0 <= i < t <= N."""
    assert 0 <= t <= N
    head_length = min(t,FIRST_END)
    first = (head_length+1)//4  # i = 2 mod 4
    mid_length = max(0,min(t,SECOND_END)-FIRST_END)
    middle = mid_length//2 + int(t > FIRST_END+2)
    tail_length = max(0,min(t,TAIL_END)-SECOND_END)
    blocks, partial = divmod(tail_length,14)
    total = first + middle + 7*blocks + min(partial,7)
    return total + (int(t>ADD)-int(t>DROP) if edited else 0)


def window(start, edited):
    end = start+WIDTH
    if end<=N:
        return count_below(end,edited)-count_below(start,edited)
    return count_below(N,edited)-count_below(start,edited)+count_below(end-N,edited)


def all_window_extrema(edited):
    # Away from these cuts membership is periodic with periods 1, 2, 4 or 14.
    # If a window crosses a cut enumerate its start. In any remaining range
    # starts repeat within 28 steps. Include the first full period after each cut.
    cuts = {0, DROP, DROP+1, FIRST_END, FIRST_END+1, FIRST_END+2, FIRST_END+3,
            SECOND_END, TAIL_END, N}
    starts = {i % N for c in cuts for i in range(c-WIDTH,c+28)}
    observed = [(window(i,edited),i) for i in starts]
    low = min(x[0] for x in observed)
    high = max(x[0] for x in observed)
    return {"min":low,"max":high,"one_min_start":str(min(i for v,i in observed if v==low)),
            "one_max_start":str(min(i for v,i in observed if v==high)),
            "representative_starts":len(starts)}


def main():
    qd_bound = 4*(2*N+7)*(2*N+1)+1
    certificates = [prime_certificate(Q,178,2),prime_certificate(D,102,3)]
    assert min(Q,D)>qd_bound and Q%8==3 and D%16==7
    assert pow(-D,(Q-1)//2,Q)==1 and pow(3,(Q-1)//2,Q)==Q-1 and (-D)%3==2
    step=0
    for bit in range(64):
        modulus=2**(bit+3)
        if pow(5,step,modulus)!=(-3)%modulus:
            step+=2**bit
        assert pow(5,step,modulus)==(-3)%modulus
    assert step%2==1 and gcd(step,N)==1
    assert pow(3,N//2,4*N) not in (1,4*N-1) and pow(3,N,4*N)==1
    assert WIDTH%2==0 and 3**(WIDTH//2-1)<2**3068<3**(WIDTH//2)
    assert 2**27 < Fraction(6,5)**192 and Fraction(11,10)**192 < 2**27
    # The proof's o^64 constraint holds at equality. The raw generator is even.
    assert 2**64==N and 6*R+1>64
    tiles,remainder=divmod(N,ELL)
    assert FIRST_END+9510==SECOND_END and TAIL_END>=tiles*ELL
    assert UNUSED<14 and 2*ELL-SECOND_END>=14
    # Full tile 1 contains an entire periodic tail block; all later full tiles
    # have at least one full block (any interval of length >=27 suffices).
    assert 2*ELL-SECOND_END>=27 and ELL>=27
    evens=6339+1+4*BLOCKS
    odds=4755+3*BLOCKS
    total=evens+odds
    assert 3*evens==4*odds and count_below(N,False)==count_below(N,True)==total
    assert (2*total)**512 * 2**27 >= N**512 and total**512 * 2**27 <= (2*N)**512
    a,b=all_window_extrema(False),all_window_extrema(True)
    assert a["max"]<=K and b["max"]<=K
    # Every full tile after tile 0 contains a retained odd point in both
    # configurations, so none can be marked. M0 > N covers every tile start.
    assert count_below(DROP+1,False)-count_below(DROP,False)==1
    assert count_below(ADD+1,False)-count_below(ADD,False)==0
    assert 4*N < total*X**2  # delta < 1, strict failure at Cb=1.
    delta=2**(-27/512)
    return {"n":str(N),"frame":"cyclicFramePow 64 1","index":2,"eps":str(EPS),"x":X,
            "k":str(2*N),"rank_m":2,"rank_t":str(2*N+7),"qd_lower_bound":str(qd_bound),
            "prime_certificates":certificates,"raw_step":str(step),"eligible_primes":[3],
            "L2":WIDTH,"K":K,"tile_length":ELL,"full_tiles":str(tiles),"partial_tile":remainder,
            "tail_blocks":str(BLOCKS),"unused_tail_slots":UNUSED,
            "swap":[DROP,ADD],"exact_coset_counts":[str(evens),str(odds)],"size":str(total),
            "shares_discrepancy":0,"density_pass":True,"windows_before":a,"windows_after":b,
            "marked_tiles_before":[0],"marked_tiles_after":[],"marked_count":[1,0],
            "bad_counts":["0",str(total)],"pass_Cb1":[True,False],
            "budget_in_points_approx":round(4*N*delta/X**2,7),
            "critical_Cb_approx":float(format(total*X**2/(4*N*delta),'.10g')),
            "weighted_mass_after_approx":float(format(total*log(3)/3,'.10g'))}


if __name__ == "__main__":
    print(json.dumps(main(),indent=2,sort_keys=True))
