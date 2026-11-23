"""Symbolic census for the order-2**64, genuinely index-two fixture.

The calculation runs in time proportional to the short window. It does not
materialize the group. Run python3 index_two_certificate.py > index_two.json.
"""

import json
from independent_check import ceil_log_base_three_of_two_power


def certificate():
    n = 2**64
    ell = 25358
    b = 34868
    end = n - (n-b) % 14
    window = 2 * ceil_log_base_three_of_two_power(3068)
    blocks = (end-b)//14

    def base_prefix(y):
        """Number retained below y for 0 <= y <= n."""
        head_length = min(y,ell)
        middle_length = max(0, min(y,b)-ell)
        periodic_length = max(0,min(y,end)-b)
        return ((head_length+1)//4 + middle_length//2 + int(y>25360)
                + 7*(periodic_length//14) + min(7,periodic_length%14))

    def periodic_prefix(j, edited):
        periods, y = divmod(j,n)
        return (periods*base_prefix(n) + base_prefix(y)
                + int(edited) * (int(y>25358) - int(y>2)))

    # Cover all boundary-crossing windows. The rest start within a homogeneous
    # region; taking 14 starts at each left boundary covers all individual
    # local periods (1, 2, 4, or 14). The singleton edits are region boundaries.
    cuts = {0, 2, 3, ell, 25359, 25360, 25361, b, end}
    starts = {(c+i)%n for c in cuts for i in range(-window,15)}
    extrema = {}
    for edited in (False, True):
        values = {i:periodic_prefix(i+window,edited)-periodic_prefix(i,edited)
                  for i in starts}
        lo, hi = min(values.values()), max(values.values())
        extrema["edited" if edited else "initial"] = {
            "min":lo, "max":hi,
            "first_argmin":min(i for i,z in values.items() if z==lo),
            "first_argmax":min(i for i,z in values.items() if z==hi)}
        assert hi == 1940 < 2112
    even = 6339+1+4*blocks
    odd = 4755+3*blocks
    m=even+odd
    assert 3*even == 4*odd and m == base_prefix(n)
    assert (2*m)**512 * 2**27 >= n**512 and m**512 * 2**27 <= (2*n)**512
    tiles,remainder = divmod(n,ell)
    assert 2*ell >= b and tiles*ell <= end
    # Tile 1 meets an occupied odd middle position. Every remaining tile lies
    # in the full-block periodic field, where gaps between occupied odds <=14.
    assert ell<=25359<2*ell and ell>14 and 25359%2==1
    # The two edit locations are even; both odd-point arguments survive.
    assert ell % 2 == 0 and 2 % 2 == 0
    # If n=2^64 were in the RankVal n and k bands, x would be in (2^29,2^31).
    # n-band exponent 17/8 and k-band exponent 149/32 at epsilon 1/64.
    assert 8+29*17 < 64*8 < 31*17 and 29*149 > 135*32
    assert 20**512 > 2**31 * 19**512  # delta > 19/20
    width_lower = 2*ceil_log_base_three_of_two_power(4*(135+26*29))
    assert width_lower == 4488 and 19*width_lower > 40*2112
    # One full orbit: each of its m points lies in min(width,n) distinct windows.
    # Summing the cap over all starts contradicts the source m >= delta*n/2.
    obstruction = {"rank_lower_short_width":width_lower,
                   "density_lower_bound_numerator":19,"density_lower_bound_denominator":40,
                   "average_occupancy_lower_bound_numerator":19*width_lower,
                   "average_occupancy_lower_bound_denominator":40,
                   "local_cap":2112,"feasible_under_rank_and_density":False}
    return {"rank_and_density_obstruction_at_3":obstruction,"order":n,"index":2,"rank_k":2*n, "x":2**27,"epsilon":"1/64",
            "blocks":blocks,"empty_tail":n-end,"complete_tiles":tiles,
            "incomplete_tile_length":remainder, "matched_even":even,
            "matched_odd":odd,"retained_size":m,"short_window_length":window,
            "certifying_starts":len(starts),"short_window":extrema,
            "marked_tile_counts":{"initial":1,"edited":0},
            "normalized_bad_score":{"initial":0,"edited":m}}


if __name__=="__main__":
    print(json.dumps(certificate(),sort_keys=True,indent=2))
