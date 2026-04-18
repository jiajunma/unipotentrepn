import CombUnipotent.CountingProof.CorrespondenceB

open CountingProof

-- dp = [2]: P = ⊥, Q = 1x1
-- countPBP_B [2] = (2, 3, 1)
#eval countPBP_B [2]

-- Check tripleSum
#eval tripleSum (countPBP_B [2])

-- Check tailCoeffs
#eval tailCoeffs 1
