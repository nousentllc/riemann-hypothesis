"""Exact linear-algebra example for the original Fourier-cell argument."""
import json
from pathlib import Path

from sympy import I, Matrix, Rational, diag, exp, eye, pi, zeros


def experiment():
    # All framed matrices have rational entries in the fixed field of the
    # conjugation on Q(i). J is the split skew-Hermitian Gram matrix.
    a, b, c, d = diag(0, 1), diag(1, 0), diag(-1, 0), diag(0, 1)
    gamma = a.row_join(b).col_join(c.row_join(d))
    j = zeros(2).row_join(eye(2)).col_join((-eye(2)).row_join(zeros(2)))
    t = Matrix([[2, 1], [1, 1]])
    u, y = Matrix([0, 1]), Matrix([1, 0])
    beta = u*y.T + y*u.T  # epsilon = -1
    assert gamma.T*j*gamma == j and c.rank() == 1
    assert c*u == zeros(2, 1) and (y.T*t*u)[0] == 1
    assert t.det() == 1 and (t*beta).trace() == 2
    assert c*beta*(-c.T) == zeros(2)
    assert a*beta*(-c.T) == Matrix([[0, 0], [1, 0]])
    # Extension trace of the rational 2 in Q(i) is 4. For the standard
    # additive character use the adele that is -1/8 at infinity, zero finite.
    ell = Rational(-1, 8)
    beta_infty = ell*beta
    unipotent = eye(2).row_join(beta_infty).col_join(zeros(2).row_join(eye(2)))
    conjugate = gamma*unipotent*gamma.inv()
    assert conjugate[2:,:2] == zeros(2) and conjugate[:2,:2].det() == 1
    exponent = -2*(t*beta_infty).trace()
    phase = exp(-2*pi*I*exponent)
    assert exponent == Rational(1, 2) and phase == -1
    if_t_zero = exp(-2*pi*I*(-2*(zeros(2)*beta_infty).trace()))
    assert if_t_zero == 1
    # Open Weyl element, epsilon = -1. The surviving parameter C^{-1}D
    # can be recovered in closed form independently of Fourier cancellation.
    translation = eye(2).row_join(t).col_join(zeros(2).row_join(eye(2)))
    open_frame = j*translation
    open_c, open_d = open_frame[2:, :2], open_frame[2:, 2:]
    assert open_frame.T*j*open_frame == j and open_c.inv()*open_d == t
    return dict(field='Q(i)/Q; framed matrices in Q',T=t.tolist(),beta1=beta.tolist(),
                kernel_u=list(u),dual_y=list(y),ell_arch=ell,ell_finite=0,
                singular_C_rank=c.rank(),conjugated_levi=conjugate[:2,:2].tolist(),
                conjugated_levi_det=conjugate[:2,:2].det(),trace_Tbeta=(t*beta).trace(),
                trace_character_input=exponent,phase_T_nondegenerate=phase,phase_T_zero=if_t_zero,
                recovered_open_cell_parameter=(open_c.inv()*open_d).tolist(),
                scope='exact algebra and phase; no adelic integral was evaluated')


if __name__ == '__main__':
    output=Path(__file__).with_name('cell_example.json')
    output.write_text(json.dumps(experiment(),default=str,indent=2)+'\n')
    print(output.read_text())
