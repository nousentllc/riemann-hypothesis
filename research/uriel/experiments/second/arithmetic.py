"""Integer witnesses for the scalar ranks and the normalized SizeWindows budget."""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import isqrt, log
import json
from pathlib import Path


def ceildiv(a,b):
    return -(-a//b)


def floor_root(a,p):
    """Exact floor of the pth root for a >= 0, by integer Newton iteration."""
    if a < 0 or p < 1:
        raise ValueError("Expected a nonnegative radicand and positive degree")
    if p == 1 or a < 2:
        return a
    if p == 2:
        return isqrt(a)
    x = 1 << ceildiv(a.bit_length(),p)
    while True:
        y = ((p-1)*x+a//x**(p-1))//p
        if y >= x:
            return x
        x = y


def ceil_root_ratio(num,den,p):
    if num < 0 or den <= 0:
        raise ValueError("Expected num >= 0 and den > 0")
    low = floor_root(num//den,p)
    return low + int(low**p*den < num)


def even_ceiling(num,p):
    return 2*ceil_root_ratio(num,2**p,p)


def scale(x,eps,J):
    return dict(x_gt_one=x>1, eps_positive=eps>0, eps_below_cutoff=eps<F(1,52), J_ge_one=J>=1)


def ranks(n,m,k,t):
    return dict(k_even=k%2==0,m_even=m%2==0,t_odd=t%2==1,two_le_m=2<=m,
                m_add_three_le_k=m+3<=k,rank_add_five_le=k+m-1+5<=t,three_m_lt_t=3*m<t,
                m_le_f=m<=2*n,f_le_k=2*n<=k,m_sq_le_N=m*m<=k+m*(t+1))


def fingerprint(x):
    data = x.to_bytes((x.bit_length()+7)//8,"big")
    return dict(bits=x.bit_length(),sha256=sha256(data).hexdigest())


def ratio_log(r):
    return log(r.numerator)-log(r.denominator)


def budget(x,L,n,nt,n2,m,k):
    dt, d2 = F(nt,n),F(n2,n)
    pieces = [2*x/(m*d2)*(1+F(m*m,k)),4*m*L/(dt*d2),2*k*L*L/(dt*n*n)]
    # Independent unnormalized bracket, set b=1 using homogeneity and aE/b=x.
    raw = nt*x*(1+F(m*m,k))+m*(2*n*m*L+F(n2*k*L*L,n*n))
    normalized = raw/(nt*m*d2/2)
    excess = L**5*sum(pieces)+4/(x*d2)
    target_rest = L**8-4*L
    holds = target_rest>=0 and excess**2 <= x*target_rest**2
    # This logarithm is a descriptive statistic of the positive part after subtracting
    # 4*sqrt(x)*L on both sides. The pass/fail decision above is exact.
    log_ratio = ratio_log(excess)-log(x)/2-log(target_rest) if target_rest>0 else None
    return dict(normalizations_equal=sum(pieces)==normalized, envelope_holds=holds,
                log_ratio_after_subtraction=round(log_ratio,8) if log_ratio is not None else None)


def row(q,base,j):
    x,L = base**(q*j),base**j
    norm_n = x*x*L**8
    e = norm_n.bit_length()
    n = 2**e
    m16 = x**8//L
    k2 = x**9*L**20
    m,k = even_ceiling(m16,16),even_ceiling(k2,2)
    f,r = 2*n,k+m-1
    T = x**377
    W8 = 8*ceildiv(10*r*(f*m+f*f*(k-1)**3*L*L),8*m)
    rhs = 8*f*r+4+T*W8
    t = rhs-r
    nt = ceil_root_ratio(n**8,2**8*L,8)
    n2 = ceildiv(n,L)

    def rankval(taken):
        return dict(n=norm_n<=n<=2*norm_n,m=m16<=m**16<=2**16*m16,
                    k=k2<=k*k<=4*k2, identity=r+taken==rhs)

    def memberships(xt,x2):
        return dict(TT_lower=(2*xt)**8*L>=n**8,TT_upper=xt**8*L<=(2*n)**8,
                    T2_lower=x2*L>=n,cardinalities=0<xt<=n and 0<x2<=n)

    host = memberships(nt,n2)
    baseline = budget(x,L,n,nt,n2,m,k)
    size = dict(x=x>=3,eps_positive=q>0,C_nonnegative=5>=0,n_positive=n>0,
                b_positive=True,aE_nonnegative=x>=0,aE_le= x<=2*x,
                TT_lower=host["TT_lower"],T2_lower=host["T2_lower"],T2_upper=n2<=n,
                m_lower=(m*L)**2>=x,m_upper=m*m<=x*L,
                k_lower=x*m<=k,k_upper=(k*L)**2<=n**4*x,
                err_le=baseline["normalizations_equal"],absorption=26**8<=L**3)
    # b=1 here denotes the common normalization, and Err is set to its largest allowed value.
    frac_T = (2*nt)**8*L != n**8
    frac_2 = n2*L != n
    result = dict(q=q,base=base,j=j,L=L,cyclic_exponent=e,threshold_16=x>=16,
                scale=scale(x,F(1,q),1),cyclic_exponent_ge_two=e>=2,ranks=ranks(n,m,k,t),
                rankval=rankval(t),host_cardinality=host,size_windows=size,
                fingerprints={key:fingerprint(v) for key,v in dict(n=n,m=m,k=k,t=t,TT=nt,T2=n2).items()},
                budget=baseline,t_plus_two_ranks=ranks(n,m,k,t+2),
                t_plus_two_rankval=rankval(t+2),
                rounded=dict(TT_fractional=frac_T,T2_fractional=frac_2,
                             TT_floor_pass=memberships(nt-int(frac_T),n2)["TT_lower"],
                             T2_floor_pass=memberships(nt,n2-int(frac_2))["T2_lower"]))
    if (q,base,j)==(64,2,16):
        # Post-registration sensitivity on a row satisfying both the rank and size gates.
        result["sensitivity"] = {}
        for label,a,b,c in (("thin_TT",nt//x,n2,k),("thin_T2",nt,n2//x,k),("high_k",nt,n2,k*x)):
            fields = memberships(a,b)
            fields["k_upper"] = (c*L)**2<=n**4*x
            result["sensitivity"][label] = dict(failed=[s for s,v in fields.items() if not v],
                                                 budget=budget(x,L,n,a,b,m,c))
        # ErrWindows uses (etaBar+4*sqrt(eBar))*x^cHH*b <= K*L*nT*a.
        # Hold eBar=0, K=1, cHH=10, a/b=x; all integers in this row are powers of two here.
        eta = F(L*nt*x,x**10)
        if eta.numerator!=1 or eta.denominator & (eta.denominator-1):
            raise ValueError("Expected a dyadic boundary")
        result["amplified_product"] = dict(cHH=10,K=1,eBar=0,eta_boundary_log2=1-eta.denominator.bit_length(),
            boundary_pass=eta*x**10==L*nt*x, twice_boundary_pass=2*eta*x**10<=L*nt*x,
            unit_component_pass=1<=1,unit_product_pass=x**10<=L*nt*x)
    return result


def round_one():
    original = Path(__file__).resolve().parent.parent/"initial/results/numerical.json"
    data = json.loads(original.read_bytes())["arithmetic"]
    rows = data["selected"]
    good_eps = lambda r: F(str(r["parameters"]["eps"])) < F(1,52)
    return dict(input_sha256=sha256(original.read_bytes()).hexdigest(),
                selected=len(rows),admissible=sum(r["admissible"] for r in rows),
                inadmissible_exceed=sum(not r["admissible"] and not r["bound_passes"] for r in rows),
                selected_in_both_domains=sum(r["admissible"] and good_eps(r) for r in rows),
                failures=[dict(eps=r["parameters"]["eps"],logx=r["parameters"]["logx"])
                          for r in rows if not r["admissible"] and not r["bound_passes"]],
                sampled=len(data["sampled"]),sampled_in_both_domains=sum(
                    r["admissible"] and good_eps(r) for r in data["sampled"]))


def run():
    invalid = [(F(1,52),1),(F(1,50),1),(F(0),1),(F(1,64),F(1,2))]
    return dict(grid=[row(q,b,j) for q,b,j in product((53,64,100),(2,3),(1,8,12,13,16,24))],
                scale_controls=[dict(epsilon=str(ep),J=str(J),fields=scale(16,ep,J)) for ep,J in invalid],
                round_one=round_one())
