"""
recursive.py - Recursive Counting of Unipotent Representations via Signature Polynomials

This module counts unipotent representations attached to purely even nilpotent orbits
of classical groups using recursive formulas with signature polynomials.

The counting is done in the polynomial ring Z[p,q] where:
    - r = p^2, s = q^2  (squares of the formal variables)
    - c = d = pq          (cross terms)

Each counting function returns a triple (DD, RC, SS) of polynomials in p, q:
    - DD: contributions ending with a 'd' pattern (discrete series type)
    - RC: contributions ending with an 'rc' pattern (principal series type)
    - SS: contributions ending with an 's' pattern (finite-dimensional type)

The total count at signature (1,1) gives the number of unipotent representations.

Root system types and their parity conditions:
    B : rows of the good parity partition are all even
    C : rows are all odd, total size is odd
    D : rows are all odd, total size is even
    M : rows are all even (metaplectic type)
    CS: rows are all odd, total size is odd (compact/split variant)
    DS: rows are all odd, total size is even (quaternionic variant)
"""
from sympy import Poly, expand, ZZ, ring, symbols

"""
Setup the polynomial ring Z[p,q] for signature polynomial computations.
"""
pp,qq = symbols('p q')
R, p, q = ring([pp,qq],ZZ)

r,s,c,d = p*p, q*q, p*q, p*q

def rs_n(r,s,n):
    """Compute r^n + r^(n-1)*s + ... + s^n = sum_{i=0}^{n} r^i * s^(n-i)."""
    a = R(0)
    for i in range(n+1):
        a += r**i * s**(n-i)
    return a

def tail_n(n):
    """Compute the tail polynomial: rs_n + rs_{n-1}*(c+d) + rs_{n-2}*cd."""
    a = rs_n(r,s,n) + rs_n(r,s,n-1)*c + rs_n(r,s,n-1)*d + rs_n(r,s,n-2)*c*d
    return a

def evalsignature(countres):
    """Sum the (DD, RC, SS) triple to get the total signature polynomial."""
    DD,RC,SS = countres
    a = DD+RC+SS
    res = a
    return res


def countD(ckO):
    """
    We will check ckO is a valid good parity partition of type D.
    Each row of ckO must be odd
    """
    assert sum(ckO)%2 ==0, "total size must be even"
    assert all(r %2 == 1 for r in ckO), "Each row must be odd length"

    if len(ckO) == 0:
        DD = R(1)
        RC = R(0)
        SS = R(0)
        return (DD,RC,SS)
    else:
        R1,R2,R3 = ckO[0],ckO[1], ckO[2] if len(ckO)>2 else -1
        n = (R1-R2)//2 + 1

        #tail ends with d, rc, s
        TDD = rs_n(r,s,n-1)*d + rs_n(r,s,n-2)*c*d
        TRC = rs_n(r,s,n-1)*c + r*rs_n(r,s,n-1)
        TSS = s**n

        if R2 > R3:
            """
            In this case (2,3) is a primitive pair
            """

            C2 = R2-1

            DDp,RCp,SSp = countD(ckO[2:])

            resp = (p**C2*q**C2)*(DDp+RCp+SSp)
            resp = resp
            DD = resp*TDD
            RC = resp*TRC
            SS = resp*TSS
            return (DD,RC,SS)
        else:
            scDD = rs_n(r,s,n-2)*c*d + s*rs_n(r,s,n-2)*d
            scRC = rs_n(r,s,n-1)*c + s*rs_n(r,s,n-2)*r
            scSS = s**n

            C2 = R2

            DDp, RCp, SSp = countD(ckO[2:])
            DD = DDp*TDD
            RC = DDp*TRC
            SS = DDp*TSS

            DD += RCp*scDD
            RC += RCp*scRC
            SS += RCp*scSS

            DD *= (p**(C2-1)*q**(C2-1))
            RC *= (p**(C2-1)*q**(C2-1))
            SS *= (p**(C2-1)*q**(C2-1))
            return (DD, RC, SS)

def countC(ckO):
    """
    We will check ckO is a valid good parity partition of type B.
    Each row of ckO must be odd
    """
    assert sum(ckO)%2 == 1, "total size must be odd"
    assert all(r %2 == 1 for r in ckO), "Each row must be odd length"
    res = 0
    if len(ckO) == 1:
        res = 1
    else:
        R1, R2 = ckO[0], ckO[1]
        DD, RC, SS = countD(ckO[1:])
        if R1 > R2:
            # Primitivie pair case
            a = DD+RC+SS
            res = 2*a(1,1)
        else:
            # balanced pair case
            a = DD+RC
            res = a(1,1)
    return res


def countB (ckO):
    """
    We will check ckO is a valid good parity partition of type B.
    """
    ckO = tuple(r for r in ckO if r!=0)
    assert all(r %2 == 0 for r in ckO), "Each row must be even length"
    if len(ckO) <= 1:
        #    DD = R(0)
        #    RC = R(p)
        #    SS = R(q)
        #    return (DD,RC,SS)
        #elif len(ckO) == 1:
        c1 = ckO[0]//2 if len(ckO)==1 else 0
        DD = d*(p+q)*rs_n(r,s,c1-1)
        RC = p*rs_n(r,s,c1) +q*r*rs_n(r,s,c1-1)
        SS = q*(s**c1)
        return (DD,RC,SS)
    else:
        R1,R2,R3 = ckO[0],ckO[1], ckO[2] if len(ckO)>2 else 0
        n = (R1-R2)//2 + 1

        #tail ends with d, rc, s
        TDD = rs_n(r,s,n-1)*d + rs_n(r,s,n-2)*c*d
        TRC = rs_n(r,s,n-1)*c + r*rs_n(r,s,n-1)
        TSS = s**n

        if R2 > R3:
            """
            In this case (2,3) is a primitive pair
            """

            C2 = R2-1

            DDp,RCp,SSp = countB(ckO[2:])

            resp = (p**C2*q**C2)*(DDp+RCp+SSp)
            resp = resp
            DD = resp*TDD
            RC = resp*TRC
            SS = resp*TSS
            return (DD,RC,SS)
        else:
            scDD = rs_n(r,s,n-2)*c*d + s*rs_n(r,s,n-2)*d
            scRC = rs_n(r,s,n-1)*c + s*rs_n(r,s,n-2)*r
            scSS = s**n

            C2 = R2

            DDp, RCp, SSp = countB(ckO[2:])
            DD = DDp*TDD
            RC = DDp*TRC
            SS = DDp*TSS

            DD += RCp*scDD
            RC += RCp*scRC
            SS += RCp*scSS

            DD *= (p**(C2-1)*q**(C2-1))
            RC *= (p**(C2-1)*q**(C2-1))
            SS *= (p**(C2-1)*q**(C2-1))
            return (DD, RC, SS)

def countM(ckO):
    """
    We will check ckO is a valid good parity partition of type B.
    Each row of ckO must be even
    """
    ckO = tuple(r for r in ckO if r!=0)
    assert all(r %2 == 0for r in ckO), "Each row must be even length"
    res = 0
    if len(ckO) == 0:
        res = 1
    else:
        R1, R2 = ckO[0], ckO[1] if len(ckO)>1 else 0
        DD, RC, SS = countB(ckO[1:])
        if R1 > R2:
            # Primitivie pair case
            a = DD+RC+SS
            res = 2*a(1,1)
        else:
            # balanced pair case
            a = DD+RC
            res = a(1,1)
    return res


def countDS(ckO):
    """
    We will check ckO is a valid good parity partition of type DS.
    Each row of ckO must be odd
    """
    assert all(r %2 == 1 for r in ckO), "Each row must be odd length"
    assert sum(ckO)%2 ==0, "total size must be even"

    a = countCS(ckO[1:])
    res = a(1,1)
    return res


def countCS(ckO):
    """
    We will check ckO is a valid good parity partition of type CS.
    Each row of ckO must be odd
    """
    assert all(r %2 == 1 for r in ckO), "Each row must be odd length"
    assert sum(ckO)%2 ==1, "total size must be odd"

    res = R(0)
    if len(ckO) == 1:
        c1 = (ckO[0]-1)//2
        res = rs_n(r,s,c1)
    else:
        R1,R2,R3 = ckO[0],ckO[1], ckO[2]
        n = (R1-R2)//2 - 1
        """
        In this case (1,2) is a primitive pair
        """
        #tail are filled with r,s
        if n >= 0:
            TAIL = rs_n(r,s,n)
            C2 = R2+1
            resp = countCS(ckO[2:])
            res = (p**C2*q**C2)*resp*TAIL
        else:
            res = R(0)
    return res


# Dispatch table mapping root system type to counting function.
# Types B and D return (DD,RC,SS) triples that need evalsignature() to get a scalar.
# Types C, M return scalars directly. CS, DS return polynomials.
COUNTFUN = {
    'B': lambda ckO: evalsignature(countB(ckO)),
    'C': countC,
    'D': lambda ckO: evalsignature(countD(ckO)),
    'M': countM,
    'CS': countCS,
    'DS': countDS,
}

def countunip(ckO, rtype):
    """
    Unified interface to count unipotent representations.

    Args:
        ckO: tuple of row lengths of the good parity partition (decreasing order)
        rtype: root system type ('B', 'C', 'D', 'M', 'CS', 'DS')

    Returns:
        The count of unipotent representations (integer for C/M, polynomial for others)
    """
    countfun = COUNTFUN.get(rtype, lambda ckO: "Wrong rtype")
    return countfun(ckO)
