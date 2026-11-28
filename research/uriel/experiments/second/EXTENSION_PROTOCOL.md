# Supplementary protocol for two finite experiments

The main signed-pole and integer-rank results had already been inspected when these two questions were specified. This supplement is registered before calculating the new prime-sum windows or lattice cases. The pinned formalization and parent protocol are unchanged.

## P. Finite prime-sum windows

Evaluate the actual singleton, unit-weight, conductor-one statistic `Deduction.G` of `CharFamily.lean` on the four closed windows with Y=4,16,64,256 and endpoints Y and Y^(3/2). Enumerate prime powers with their von Mangoldt weights. Between consecutive prime powers write G(y)=A y−B−y log(y) with B nonnegative. The sign of the derivative of G(y)/sqrt(y) is the sign of A−2−log(y)+B/y. It decreases strictly on each piece. Evaluate both endpoints and every interior zero, comparing the maximum with the two-endpoint estimate. Predict an interior maximum exceeds the two-endpoint estimate on at least one window. Report the inferred finite constants with their locations and an independent trial-division sum at each maximum. Test a deliberately missing prime-power contribution and a continuous bump between integer samples. Repeat at 60 and 90 decimal digits with a 1e−40 mixed tolerance. This finite assessment uses numerical logarithms and is independent of the universal late-window hypothesis.

## S. Rank fraction and the factor twelve

For the scalar `GlobalTheory.CutNum.numeric` inequality test the boundary dg=3, db=1, delta=1/12, mu=−1, m=lg=Q=1 with the cut at equality. Predict that reducing 12 to any smaller real constant fails on the same tuple. Try to check this new universal-in-the-coefficient statement in Lean. Separately test Euclidean hyperplane projections in dimensions 4 and 8 with normal v=(1,q,0,…) for q=1,2,10,100. Compute both intersection Gram determinants, the direct-sum index, and the matrix denominator, and test the rank constraint with delta=1/(3 dim). Predict that the covolume product equals the index and the cut needs the denominator even when the discarded rank is permitted. These lattice instances do not establish geometric sharpness for the source's number-field hypothesis.
