from rich import print
from itertools import chain, zip_longest
from copy import copy, deepcopy
from multiset import FrozenMultiset as frozenset
from .tool import *
from .drc import *
from .LS import *

"""
Following lifting only realize the algorithm for the orbits
after the reduction. These orbits satisfies C_{2i} = C_{2i-1}.
So we only realize the algorithm 
for adding a column of lenght equal to the longest lenght column in type D
or the generalized descent case (C_{2i} = C_{2i-1} is odd).  
"""


def _combine_tab(drca, drcb):
    res = []
    for i, cb in enumerate(drcb):
        ca = getz(drca, i, '')
        cb = drcb[i]
        res.append(ca+cb[len(ca):])
    return tuple(res)


def _combine_tab(drca, drcb):
    res = tuple(ca+cb[len(ca):] for ca, cb in
                zip_longest(drca, drcb, fillvalue=''))
    return res


def lift_extdrc_B_M_trivial(drc, cL=None):
    drcL, drcR = drc
    exttype = drcR[0][-1]
    drcR = (drcR[0][:-1], *drcR[1:])
    if cL is None:
        # cL = len(getz(drcR, 0, ''))
        cL = len(drcR[0])
    cR = len(drcR[0])
    if cL < cR:
        return None
    else:
        tauL = [cL]+[c.count('*') for c in drcL]
        tauR = [c.count('*')+c.count('s') for c in drcR]
        sdrc = next(fill_rdot((tauL, tauR), sym='s'), None)
        if sdrc is None:
            return None
        if len(sdrc[0]) == 0:
            sdrc = (('',), ('',))
            #else:
        sdrcL, sdrcR = sdrc
        #r = max(len(drcL)+1, len(drcR))
        drcLL = (sdrcL[0], * _combine_tab(sdrcL[1:], drcL))
        drcRR = _combine_tab(sdrcR, drcR)
        if exttype == 'a':
            return (drcLL, drcRR)
        elif exttype == 'b':
            if drcLL[0][-1] == 's':
                drcLL = (drcLL[0][:-1]+'c', *drcLL[1:])
                return (drcLL, drcRR)
            else:
                return None
        else:
            return None


def lift_drc_B_M_det(drc, cL=None):
    drcL, drcR = drc
    if cL is None:
        cL = len(getz(drcR, 0, ''))+1
    cR = len(drcR[0])
    ndrc = lift_extdrc_B_M_trivial(drc, cL-1)
    if ndrc is None:
        return None
    else:
        ndrcL, ndrcR = ndrc
        ndrcL = (ndrcL[0]+'c', * ndrcL[1:])
        return (ndrcL, ndrcR)


NONSPEC_M_TWIST = {
    ('ss', 'd'): ('s', 'rd'),
    ('ss', 'r'): ('s', 'rr'),
    ('*s', '*'): ('*', '*r'),
    ('sc', 'r'): ('c', 'rr'),
    ('sc', 'd'): ('c', 'rd'),
    ('*c', '*'): ('*', '*d'),
    ('s', ''): ('', 'r'),
    ('c', ''): ('', 'd')
}


def lift_drc_D_C(drc, cR, printdrop=False):
    drcL, drcR = drc
    """
    if the lenght of '*'/'s' in the fisrt column > cR 
    then there is no lift. 
    Otherwise there is a lift. 
    """
    drcLL = [col.replace('s', '*') for col in drcL]
    drcR = ['*'*cR]+drcR
    drcRR = []
    for i in range(max(len(drcLL), len(drcR))):
        colL, colR = getz(drcLL, i, ''), getz(drcR, i, '')
        bL = colL.count('*')
        cR, cnR = len(colR), len(getz(drcR, i+1, ''))
        assert(bL >= cnR)
        if bL > cR:
            if printdrop:
                print('\n%s\n---------\n' % (str_dgms_C((drcL, drcR))))
            return None
        else:
            drcRR.append('*'*bL+'s'*(cR-bL))
    return (drcLL, drcRR)


def lift_drc_D_C_gd(drc):
    """
    Generalized descent case, attach c_2a = c_{2a-1}-1
    """
    drcL, drcR = drc
    """
    if the lenght of '*'/'s' in the fisrt column > cR
    then there is no lift.
    Otherwise there is a lift.
    """
    drcL, drcR = drc
    col0 = getz(drcL, 0, '')
    assert(len(col0) > 0)
    return lift_drc_D_C(drc, len(col0)-1)


def lift_drc_D_C_trivial(drc):
    """
    Lift the representation without determinant twist,
    attach c_2a = c_{2a-1}
    """
    drcL, drcR = drc
    """
    if the lenght of '*'/'s' in the fisrt column > cR
    then there is no lift.
    Otherwise there is a lift.
    """
    drcL, drcR = drc
    col0 = getz(drcL, 0, '')
    assert(len(col0) > 0)
    return lift_drc_D_C(drc, len(col0))


def lift_dgms_D_C_gd(dgms):
    S = []
    for drc in dgms:
        ldrc = lift_drc_D_C_gd(drc)
        if ldrc is not None:
            S.append(ldrc)
    return S


def lift_dgms_D_C(dgms, cR):
    S = []
    for drc in dgms:
        ldrc = lift_drc_D_C(drc, cR)
        if ldrc is not None:
            S.append(ldrc)
    return S


def lift_drc_D_C(drc, cR, printdrop=False):
    drcL, drcR = drc
    """
    if the lenght of '*'/'s' in the fisrt column > cR 
    then there is no lift. 
    Otherwise there is a lift. 
    """
    drcLL = [col.replace('s', '*') for col in drcL]
    drcR = ['*'*cR]+list(drcR)
    drcRR = []
    for i in range(max(len(drcLL), len(drcR))):
        colL, colR = getz(drcLL, i, ''), getz(drcR, i, '')
        bL = colL.count('*')
        cR, cnR = len(colR), len(getz(drcR, i+1, ''))
        assert(bL >= cnR)
        if bL > cR:
            if printdrop:
                print('\n%s\n---------\n' % (str_dgms_C((drcL, drcR))))
            return None
        else:
            drcRR.append('*'*bL+'s'*(cR-bL))
    return (tuple(drcLL), tuple(drcRR))


def lift_drc_D_C_gd(drc):
    drcL, drcR = drc
    """
    if the lenght of '*'/'s' in the fisrt column > cR 
    then there is no lift. 
    Otherwise there is a lift. 
    """
    drcL, drcR = drc
    col0 = getz(drcL, 0, '')
    assert(len(col0) > 0)
    return lift_drc_D_C(drc, len(col0)-1)


def lift_drc_D_C_trivial(drc):
    drcL, drcR = drc
    """
    if the lenght of '*'/'s' in the fisrt column > cR 
    then there is no lift. 
    Otherwise there is a lift. 
    the results are special diagrams.
    """
    drcL, drcR = drc
    col0 = getz(drcL, 0, '')
    assert(len(col0) > 0)
    return lift_drc_D_C(drc, len(col0))


def lift_dgms_D_C_gd(dgms):
    S = []
    for drc in dgms:
        ldrc = lift_drc_D_C_gd(drc)
        if ldrc is not None:
            S.append(ldrc)
    return S

"""
Consider the special to non-specail map in typ D

tau:

* *  , *           * * , *
* *    *   <-->    * *
*                  * *
*                  *

. s , .
. s   .
*
*

"""

def twist_C_nonspecial(drc):
    """
    send a the special diagram to non-special diagram
    special diagram means the longest column length of 
    the left and right diagram are the same
    """
    drcL, drcR = drc
    # first, second column of drcL and first column of drcR
    fL, sL, fR = getz(drcL, 0, ''), getz(drcL, 1, ''), getz(drcR, 0, '')
    assert(len(fR) == len(fL) and len(fR) > 0)
    fRR = fR[:-1]
    if fR[-1] == 's':
        if len(fL) == 1 or fL[-2] != 'c':
            fLL = fL[:-1]+'r'+fL[-1:]
        else:
            fLL = fL[:-2]+'r'+fL[-2:]
        nspdrc = ((fLL, *drcL[1:]), (fRR, *drcR[1:]))
    elif (fL[-1], getz(sL, len(fL)-1, '')) == ('*', 'r'):
        fLL = fL[:-1]+'rd'
        sLL = sL[:-1]+'c'
        nspdrc = ((fLL, sLL, *drcL[2:]), (fRR, *drcR[1:]))
    else:
        fLL = fL[:-1]+'cd'
        nspdrc = ((fLL, *drcL[1:]), (fRR, *drcR[1:]))
    if not verify_drc(nspdrc, 'C'):
        print('Invalid nonspecial drc\n original: \n%s\n new:\n%s\n'
              % (str_dgms_C(drc), str_dgms_C(nspdrc)))
        return None
    return nspdrc


def twist_M_nonspecial(drc):
    """
    send a the special diagram to non-special diagram
    special diagram means `switch' the left diagram longest column 
    to right diagram
    We only implement fL = fR+1 case
    """
    drcL, drcR = drc
    # first column of drcL and first, second column of drcR
    fL, fR, sR = getz(drcL, 0, ''), getz(drcR, 0, ''), getz(drcR, 1, '')
    assert(len(fL) == len(fR)+1 and len(fL) > 0)
    fLL = fL[:-1]
    if fL[-1] == 's':
        if len(fR) > 0 and fR[-1] == 'd':
            fRR = fR[:-1]+'rd'
        else:
            fRR = fR + 'r'
    elif fL[-1] == 'c':
        if len(fL) >= 2 and fL[-2] == 's':
            fLL = fL[:-2]+'c'
            fRR = fR[:-1]+'r'+fR[-1]
        else:
            fLL = fL[:-1]
            fRR = fR+'d'
    else:
        print('Invalid original drc: %s' % (str_dgms(drc)))
        return None
    nspdrc = ((fLL, *drcL[1:]), (fRR, *drcR[1:]))
    return nspdrc

## New version
def twist_M_nonspecial(drc):
    """
    send a the special diagram to non-special diagram
    special diagram means `switch' the left diagram longest column
    to right diagram
    We only implement fL = fR+1 case
    """
    drcL, drcR = drc
    # first column of drcL and first, second column of drcR
    fL, fR, sR = getz(drcL, 0, ''), getz(drcR, 0, ''), getz(drcR, 1, '')
    assert(len(fL) == len(fR)+1 and len(fL) > 0)
    if fL[-1] == 's':
        if len(fR) > 0 and fR[-1] == 'd':
            fLL = fL[:-2] +'c'
            fRR = fR[:-1]+'rr'
        else:
            fLL = fL[:-1]
            fRR = fR + 'r'
    elif fL[-1] == 'c':
        if len(fR) > 0 and fR[-1] == 'd':
            fLL = fL[:-2]+'c'
            fRR = fR[:-1]+'rd'
        else:
            fLL = fL[:-1]
            fRR = fR+'d'
    else:
        print('Invalid original drc: %s' % (str_dgms(drc)))
        return None
    nspdrc = ((fLL, *drcL[1:]), (fRR, *drcR[1:]))
    #print('abc')
    return nspdrc


def lift_drc_D_C_det(drc):
    spdrc = lift_drc_D_C_trivial(drc)
    nspdrc = twist_C_nonspecial(spdrc)
    return nspdrc


def _add_bullet_D(drcL, drcR):
    fL, fR = drcL[0], getz(drcR, 0, '')
    nfL, nfR = len(fL), len(fR)
    assert(nfL == nfR)
    rr = max(len(drcL), len(drcR))
    Rlen = [len(getz(drcR, i, '')) for i in range(rr)]
    bRlen = [getz(drcR, i, '').count('*') for i in range(rr)]
    ndrcR = tuple('*'*cl for cl in Rlen)
    ndrcL = ['*'*nfL]
    for i in range(rr):
        col = getz(drcL, i, '')
        nlR, nnlR = getz(bRlen, i, 0), getz(Rlen, i+1, 0)
        ncol = '*'*nnlR+'s'*(nlR-nnlR)+col[nlR:]
        ndrcL.append(ncol)
    return (tuple(ndrcL), ndrcR)

def gen_drc_D_two(fL, sL, n):
    RES = []
    assert(len(sL)<=1)
    if fL == '':
        RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(0,n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(n-1)])
    elif fL == 'd':
        # don't attach a column full of 's' or 'r' to d.
        RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(0,n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(n-1)])
    elif fL == 'c':
        RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1, n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(1, n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(1, n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(1, n-1)])
        if n >= 1:
            RES.extend([('r'*(n-1)+'c', 'c', sL, (1,-1) ), ])
        if n >= 2:
            RES.extend([('r'*(n-2)+'cd', 'c', sL, (1,1))])
    elif fL == 'r':
        RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1, n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(1, n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(1, n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(1, n-1)])
        RES.append(('r'*n, 'c', sL, (1,-1)))
        #print(RES)
        if n >= 2:
            RES.extend([('r'*(n-1)+'d', 'c', sL, (1,1))])
        # if n>2:
        #    RES.extend([('r'*(n-2)+'cd','c')])
    elif fL == 'rr':
        assert(n >= 2)
        RES.extend([('s'*i+'r'*(n-i), 'rr', sL, (1,-1)) for i in range(2, n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c', 'rr', sL,  (1,-1)) for i in range(2, n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d', 'rr', sL,  (1,1)) for i in range(2, n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd', 'rr', sL,  (1,1)) for i in range(2, n-1)])
        RES.extend([('r'*n, 'cd', sL,  (1,-1)),
                    ('r'*(n-1)+'c', 'cd', sL,  (1,-1)),
                    ('r'*(n-1)+'d', 'cd', sL,  (1,1))])
        if n >= 3:
            RES.extend([('r'*(n-2)+'cd', 'cd', sL, (1,1))])
        # if n>2:
        #    RES.extend([('s'*i+'r'*(n-i-1)+'d',fL) for i in range(2,n)])
        # else:
        #    RES.extend([('cd','cd')])
        # if n==2:
        #    RES = [('rr','cd'),('rc','cd'),('rd','cd'),('ss','rr')]
    elif fL == 'rc':
        assert(n >= 2)
        RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1, n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(1, n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(1, n-1)])
        if n > 2:
            RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(1, n)])
        else:
            RES.extend([('cd', 'cd', sL,  (1,1))])
    elif fL == 'rd':
        assert(n >= 2)
        RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1, n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(1, n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(1, n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(1, n-1)])
    elif fL == 'cd':
        assert(n >= 2)
        RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1, n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(1, n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(1, n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(1, n-1)])
    return RES

# def gen_drc_D_two_new(fL, sL, n):
#     RES = []
#     if fL == '':
#         RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(0,n+1)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(n)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(n)])
#         RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(n-1)])
#     elif fL == 'd':
#         # don't attach a column full of 's' or 'r' to d.
#         RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1,n)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(n)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(n)])
#         RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(n-1)])
#     elif fL == 'c':
#         RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1, n+1)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(1, n)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(1, n)])
#         RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(1, n-1)])
#         #if sL != 'c':
#         #    RES.append(('s'*n, 'c', sL, (1,1)))
#         if sL != 'c':
#             RES.append(('s'*n, 'd', sL, (1,1)))
#         else:
#             RES.append(('s'*n, 'c', 'd', (1,1)))
#         if n >= 1:
#             RES.extend([('r'*(n-1)+'c', 'c', sL, (1,-1) ), ])
#         if n >= 2:
#             RES.extend([('r'*(n-2)+'cd', 'c', sL, (1,1))])
#     elif fL == 'r':
#         RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1, n+1)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(1, n)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(1, n)])
#         RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(1, n-1)])
#         RES.append(('r'*n, 'c', sL, (1,-1)))
#         if sL == 'c':
#             RES.append(('r'*n, 'c', 'd', (1,1)))
#         else:
#             RES.append(('r'*n, 'd', sL, (1,1)))
#         if n >= 2:
#             RES.extend([('r'*(n-1)+'d', 'c', sL, (1,1))])
#         # if n>2:
#         #    RES.extend([('r'*(n-2)+'cd','c')])
#     elif fL == 'rr':
#         assert(n >= 2)
#         RES.extend([('s'*i+'r'*(n-i), 'rr', sL, (1,-1)) for i in range(2, n+1)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'c', 'rr', sL,  (1,-1)) for i in range(2, n)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'d', 'rr', sL,  (1,1)) for i in range(2, n)])
#         RES.extend([('s'*i+'r'*(n-i-2)+'cd', 'rr', sL,  (1,1)) for i in range(2, n-1)])
#         RES.extend([('r'*n, 'cd', sL,  (1,-1)),
#                     ('r'*(n-1)+'c', 'cd', sL,  (1,1)),
#                     ('r'*(n-1)+'d', 'cd', sL,  (1,-1))])
#         if n >= 3:
#             RES.extend([('r'*(n-2)+'cd', 'cd', sL, (1,-1))])
#         # if n>2:
#         #    RES.extend([('s'*i+'r'*(n-i-1)+'d',fL) for i in range(2,n)])
#         # else:
#         #    RES.extend([('cd','cd')])
#         # if n==2:
#         #    RES = [('rr','cd'),('rc','cd'),('rd','cd'),('ss','rr')]
#     elif fL == 'rc':
#         assert(n >= 2)
#         RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1, n+1)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(1, n)])
#         RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(1, n-1)])
#         if n > 2:
#             RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(1, n)])
#         else:
#             RES.extend([('cd', 'cd', sL,  (1,1))])
#         # if n==2:
#         #    RES = [('sr','rc'), ('ss','rc'),('sc','rc'), ('cd','cd')]
#     elif fL == 'rd':
#         assert(n >= 2)
#         RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1, n+1)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(1, n)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(1, n)])
#         RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(1, n-1)])
#         # if n==2:
#         #    RES =  [('sr',fL), ('ss',fL),('sc',fL),('sd',fL)]
#     elif fL == 'cd':
#         assert(n >= 2)
#         RES.extend([('s'*i+'r'*(n-i), fL, sL,  (1,-1)) for i in range(1, n+1)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'c', fL, sL,  (1,-1)) for i in range(1, n)])
#         RES.extend([('s'*i+'r'*(n-i-1)+'d', fL, sL,  (1,1)) for i in range(1, n)])
#         RES.extend([('s'*i+'r'*(n-i-2)+'cd', fL, sL,  (1,1)) for i in range(1, n-1)])
#         # if n==2:
#         #    RES =  [('sr',fL), ('ss',fL),('sc',fL),('sd',fL)]
#     return RES


def lift_drc_C_D(drc, a):
    drcL, drcR = drc
    fL, sL, fR = getz(drcL, 0, ''), getz(drcL, 1,''), getz(drcR, 0, '')
    nL, nR = len(fL), len(fR)
    assert(nL-nR <= 2)
    assert(nL <= a)
    bdrcL, bdrcR = _add_bullet_D([fL[:nR]]+list(drcL[1:]), drcR)
    # print(fL)
    ldrcD2 = gen_drc_D_two(fL[nR:], sL[nR:], a-nR)
    RES = []
    for ffL, fL, sL,  twist in ldrcD2:
        drcLL = (bdrcL[0]+ffL, bdrcL[1]+fL, getz(bdrcL,2,'')[:nR]+sL, *bdrcL[3:])
        ndrc = (tuple(drcLL), tuple(bdrcR))
        if not verify_drc(ndrc, 'D'):
            print('Invalid drc')
            print(concat_strblocks('original: ', str_dgms(drc),
                                   '  a = %d'%a, '  --> new:', str_dgms(ndrc)))
        RES.append((ndrc, twist))
    assert(len(RES) == len(set(ndrc for ndrc, twist in RES)))
    # print(drc)
    # print(RES)
    return RES


def gp_form_B_ext(drc):
    cplx, cpt1, cpt2, real1, real2 = countdrcform(drc)
    dp, dq = cplx+real1+real2+cpt1*2, cplx+real1+real2+cpt2*2
    if drc[1][0][-1] == 'a':
        return(dp+1, dq)
    elif drc[1][0][-1] == 'b':
        return (dp, dq+1)
    else:
        print('Wrong extended drc', drc)


def gp_form_B_c(drc):
    cplx, cpt1, cpt2, real1, real2 = countdrcform(drc)
    dp, dq = cplx+real1+real2+cpt1*2, cplx+real1+real2+cpt2*2
    return (dp, dq+1)


def gen_drc_B_two(fL, sL, fR,  n):
    """
    returns the tail of  
    first column of L, second column of L, first column of R, second column of R
    """
    #print('fL, fR, n: %s, %s, %d'%(fL,fR,n))
   #RES = []
    ERES = []
    if sL == '':
        if len(fL) == 0 and len(fR) == 0:
            ERES.extend([('', 's'*i+'r'*(n-i)+'a', '', (1, -1)) for i in range(0, n+1)])
            ERES.extend([('', 's'*i+'r'*(n-i-1)+'d'+'a', '', (1, 1)) for i in range(0, n)])
            ERES.extend([('', 's'*i+'r'*(n-i)+'b', '', (1, -1)) for i in range(0, n+1)])
            ERES.extend([('', 's'*i+'r'*(n-i-1)+'d'+'b', '', (1, 1)) for i in range(0, n)])
        elif (fL, fR) == ('s', ''):
            ERES.extend([('c', 'r'*n+'a', '', (1, -1))])
            #ERES.extend([('c', 'r'*n+'a', '', (1, 1))])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-1)+'a', '', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-2)+'d'+'a', '', (1, 1)) for i in range(0, n-1)])
            ERES.extend([('c', 'r'*n+'b', '', (1, 1))])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-1)+'b', '', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-2)+'d'+'b', '', (1, 1)) for i in range(0, n-1)])
        elif (fL, fR) == ('c', ''):
            ERES.extend([('c', 's'*i+'r'*(n-i)+'a', '', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('c', 'r'*(n-1)+'d'+'a', '', (1, -1))])
            #ERES.extend([('c', 'r'*(n-1)+'d'+'a', '', (1, 1))])
            ERES.extend([('c', 's'*i+'r'*(n-i-1)+'d'+'a', '', (1, 1)) for i in range(1, n)])
            ERES.extend([('c', 's'*i+'r'*(n-i)+'b', '', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('c', 's'*i+'r'*(n-i-1)+'d'+'b', '', (1, 1)) for i in range(0, n)])
        elif (fL, fR) == ('', 'r'):
            ERES.extend([('', 'r'*n+'a', 'd', (1, -1))])
            #ERES.extend([('', 'r'*n+'a', 'd', (1, 1))])
            ERES.extend([('', 's'*i+'r'*(n-i)+'a', 'r', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('', 's'*i+'r'*(n-i-1)+'d'+'a', 'r', (1, 1)) for i in range(1, n)])
            ERES.extend([('', 'r'*n+'b', 'd', (1, 1))])
            ERES.extend([('', 's'*i+'r'*(n-i)+'b', 'r', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('', 's'*i+'r'*(n-i-1)+'d'+'b', 'r', (1, 1)) for i in range(1, n)])
        elif (fL, fR) == ('', 'd'):
            ERES.extend([('', 's'*i+'r'*(n-i)+'a', 'd', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('', 'r'*(n-1)+'d'+'a', 'd', (1, -1))])
            #ERES.extend([('', 'r'*(n-1)+'d'+'a', 'd', (1, 1))])
            ERES.extend([('', 's'*i+'r'*(n-i-1)+'d'+'a', 'd', (1, 1)) for i in range(1, n)])
            ERES.extend([('', 's'*i+'r'*(n-i)+'b', 'd', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('', 's'*i+'r'*(n-i-1)+'d'+'b', 'd', (1, 1)) for i in range(0, n)])
        elif (fL, fR) == ('*', '*'):
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-1)+'a',     's', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-2)+'d'+'a', 's', (1, 1)) for i in range(0, n-1)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-1)+'b',     's', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-2)+'d'+'b', 's', (1, 1)) for i in range(0, n-1)])
        elif (fL, fR) == ('s', 'r'):
            ## New test
            if n>1:
                ERES.extend([('c', 'r'*n+'a', 'd', (1, -1))])
            #ERES.extend([('c', 'r'*n+'a', 'd', (1, -1))])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-1)+'a',     'r', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-2)+'d'+'a', 'r', (1, 1)) for i in range(0, n-1)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-1)+'b',     'r', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-2)+'d'+'b', 'r', (1, 1)) for i in range(0, n-1)])
        elif (fL, fR) == ('s', 'd'):
            ## New test
            ##print('[red]sd[/red]')
            ##ERES.extend([('c', 'r'*n+'a', 'd', (1, -1))])
            if n>1:
                ERES.extend([('c', 'r'*(n-1)+'d'+'a', 'd', (1, -1))])
            #ERES.extend([('c', 'r'*(n-1)+'d'+'a', 'd', (1, -1))])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-1)+'a',     'd', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-2)+'d'+'a', 'd', (1, 1)) for i in range(0, n-1)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-1)+'b',     'd', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', '*'+'s'*i+'r'*(n-i-2)+'d'+'b', 'd', (1, 1)) for i in range(0, n-1)])
        elif (fL, fR) == ('c', 'r'):
            if n==1:
                ERES.extend([('c', 'r'+'a', 'd', (1, -1))])
            ERES.extend([('c', 'r'*n+'b', 'd', (1, 1))])
            ERES.extend([('c', 's'*i+'r'*(n-i)+'a',       'r', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('c', 's'*i+'r'*(n-i-1)+'d'+'a', 'r', (1, 1)) for i in range(1, n)])
            ERES.extend([('c', 's'*i+'r'*(n-i)+'b',       'r', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('c', 's'*i+'r'*(n-i-1)+'d'+'b', 'r', (1, 1)) for i in range(1, n)])
        elif (fL, fR) == ('c', 'd'):
            if n==1:
                ERES.extend([('c', 'd'+'a', 'd', (1, -1))])
            ERES.extend([('c', 's'*i+'r'*(n-i)+'a',       'd', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('c', 's'*i+'r'*(n-i-1)+'d'+'a', 'd', (1, 1)) for i in range(1, n)])
            ERES.extend([('c', 's'*i+'r'*(n-i)+'b',       'd', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('c', 's'*i+'r'*(n-i-1)+'d'+'b', 'd', (1, 1)) for i in range(0, n)])
        # Return extend the parameter directly
        #if len(fL)+len(fR) == 2:
        EERES  = [(fL, '', fR, sR, twist) for fL, fR, sR, twist in ERES]
        return EERES
        # else extend RES to ERES and return
        # else:
        #     for fL, fR, sR, twist in RES:
        #         ERES.append((fL, '', fR+'a', sR, twist))
        #         ERES.append((fL, '', fR+'b', sR, twist))
        #     return ERES
    else:
        if (fL, sL, fR) == ('*', 's', '*'):
            ERES.extend([('*', '*', '*'+'s'*i+'r'*(n-i-1)+'a',      '*', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', '*', '*'+'s'*i+'r'*(n-i-2)+'d'+'a',  '*', (1, 1)) for i in range(0, n-1)])
            ERES.extend([('*', '*', '*'+'s'*i+'r'*(n-i-1)+'b',      '*', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', '*', '*'+'s'*i+'r'*(n-i-2)+'d'+'b',  '*', (1, 1)) for i in range(0, n-1)])
        elif (fL, sL, fR) == ('*', 'c', '*'):
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-1)+'a',     's', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-2)+'d'+'a', 's', (1, 1)) for i in range(0, n-1)])
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-1)+'b',     's', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-2)+'d'+'b', 's', (1, 1)) for i in range(0, n-1)])
        elif (fL, sL, fR) == ('s', 'c', 'r'):
            if n>1:
                ERES.extend([('c', 'c', 'r'*n+'a', 'd', (1, 1))])
            #ERES.extend([('c', 'c', 'r'*n+'b', 'd', (1, 1))])
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-1)+'a',     'r', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-2)+'d'+'a', 'r', (1, 1)) for i in range(0, n-1)])
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-1)+'b',     'r', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-2)+'d'+'b', 'r', (1, 1)) for i in range(0, n-1)])
        elif (fL, sL, fR) == ('s', 'c', 'd'):
            #if n ==1:
            #    ERES.extend([('c', 'c', 'r'*n+'a', 'd', (1, -1))])
            #ERES.extend([('c', 'c', 'r'*n+'a', 'd', (1, -1))])
            if n-1 >0:
                ERES.extend([('c', 'c', 'r'*(n-1)+'d'+'a', 'd', (1, 1))])
            ERES.extend([('*', 'c',  '*'+'s'*i+'r'*(n-i-1)+'a',     'd', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-2)+'d'+'a', 'd', (1, 1)) for i in range(0, n-1)])
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-1)+'b',     'd', (1, -1)) for i in range(0, n)])
            ERES.extend([('*', 'c', '*'+'s'*i+'r'*(n-i-2)+'d'+'b', 'd', (1, 1)) for i in range(0, n-1)])
        elif (fL, sL, fR) == ('c', 'c', 'r'):
            if n==1:
                ERES.extend([('c','c', 'r'*n+'a', 'd', (1, -1))])
            ERES.extend([('c', 'c', 'r'*n+'b', 'd', (1, 1))])
            ERES.extend([('c', 'c', 's'*i+'r'*(n-i)+'a',       'r', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('c', 'c', 's'*i+'r'*(n-i-1)+'d'+'a', 'r', (1, 1)) for i in range(1, n)])
            ERES.extend([('c', 'c', 's'*i+'r'*(n-i)+'b',       'r', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('c', 'c', 's'*i+'r'*(n-i-1)+'d'+'b', 'r', (1, 1)) for i in range(1, n)])
        elif (fL, sL, fR) == ('c', 'c', 'd'):
            if n == 1:
                ERES.extend([('c', 'c', 'd'+'a', 'd', (1, -1))])
            ERES.extend([('c', 'c', 's'*i+'r'*(n-i)+'a',       'd', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('c', 'c', 's'*i+'r'*(n-i-1)+'d'+'a', 'd', (1, 1)) for i in range(1, n)])
            ERES.extend([('c', 'c', 's'*i+'r'*(n-i)+'b',       'd', (1, -1)) for i in range(1, n+1)])
            ERES.extend([('c', 'c', 's'*i+'r'*(n-i-1)+'d'+'b', 'd', (1, 1)) for i in range(0, n)])
        return ERES 
        

def sdot_switcher(drcL, drcR, nR):
    rdtauL = (*(c.count('*')+c.count('s') for c in drcL), )
    rdtauR = (nR, *(c.count('*') for c in drcR))
    rddrcR, rddrcL = next(
        fill_rdot((rdtauR, rdtauL), sym='s', simp_Wrepn=False))
    ntauL = tuple(rddrcL[i] + c[rdtauL[i]:] for i, c in enumerate(drcL))
    ntauR = (rddrcR[0], *(rddrcR[i+1] + c[rdtauR[i+1]:]
                          for i, c in enumerate(drcR)))
    return (ntauL, ntauR)




def lift_drc_M_B(drc, a):
    """
    Here we use extended drc diagram:
    'a'/'b' at the end of the longest column to indicate the form of B
    is given by adds 1 on p or q. 
    """
    drcL, drcR = drc
    """
    Get the first and second column of left diagram
    and the first column of the right diagram.
    """
    fL, sL, fR, sR = getz(drcL, 0, ''), getz(drcL, 1, ''), getz(drcR, 0, ''), getz(drcR, 1, '')
    nL, nsL, nR = len(fL), len(sL), len(fR)
    if nL != nR:
        t = min(nL, nR)
        assert(nL-t <= 1 and nR - t <= 1)
    elif fL[-1:] == '*':
        t = len(fL)
    else:
        t = max(nR-1, 0)
    assert(nR <= a)
    tdrcL = (fL[:t], sL[:t], * drcL[2:])
    tdrcR = (fR[:t], * drcR[1:])
    try:
        tdrcL, tdrcR = sdot_switcher(tdrcL, tdrcR, t)
    except:
        print(str_dgms(drc), ' t=', t)
        print(fL,sL,fR)
        print(tdrcL,tdrcR)
        print(str_dgms((tdrcL,tdrcR)))
        return None
    #bdrcL, bdrcR = _add_bullet_D([fL[:nR]]+list(drcL[1:]),drcR)
    # print(fL)
    RES = []
    eRES = []
    ldrcD2 = gen_drc_B_two(fL[t:], sL[t:], fR[t:], a-t)
    for ffL, ssL, ffR, ssR, twist in ldrcD2:
        # print('%s,%s,%s'%(ffL,ffR,ssR))
        drcLL = (tdrcL[0]+ffL, getz(tdrcL, 1, '') + ssL, * tdrcL[2:])
        drcRR = (tdrcR[0]+ffR, tdrcR[1]+ssR, * tdrcR[2:])
        ndrc = reg_drc((drcLL, drcRR))
        RES.append(ndrc)
        eRES.append((ndrc, twist))
    try:
        assert(len(RES) == len(set(RES)))
    except:
        print(RES)
    return eRES

## New version

def gen_fR_B(tL,tR, L,R, n):
    """
    Generate columns of the right diagram
    for O(2n+1)
    """
    LfR = []
    LfR.extend([('s'*i+'r'*(n-i)+'a', (1, -1)) for i in range(0, n+1)])
    LfR.extend([('s'*i+'r'*(n-i-1)+'d'+'a', (1, 1)) for i in range(0, n)])
    LfR.extend([('s'*i+'r'*(n-i)+'b', (1, -1)) for i in range(0, n+1)])
    LfR.extend([('s'*i+'r'*(n-i-1)+'d'+'b', (1, 1)) for i in range(0, n)])
    ERES = []
    for  fR, twist in LfR:
        LL = (tL,  *L[1:])
        RR = (tR+fR, *R)
        ERES.append((LL, RR, twist))
    return ERES

def gen_drc_B_two_new(L, R,  n):
    """
    agruments: last row of left diagram and right diagram
    returns the tail of
    first column of L, second column of L, first column of R, second column of R, tiwst
    """
    #print('fL, fR, n: %s, %s, %d'%(fL,fR,n))
    #RES = []
    ERES = []
    if len(L) == 0 and len(R) == 0:
        ERES = gen_fR_B('','',L,R,n)
    elif len(R) == 0:
        if L[0]=='s':
            ERES = gen_fR_B('*','*',L,R,n-1)
            LL = ('c',* L[1:])
            ERES.append((LL, ('r'*n+'a',), (1,-1)))
            ERES.append((LL, ('r'*(n-1)+'d'+'a',), (1,1)))
        elif L[0]=='c':
            ERES = gen_fR_B('c','s',L,R,n-1)
            LL = ('c',* L[1:])
            ERES.append((LL, ('r'*(n-1)+'d'+'b',), (1,1)))
            ERES.append((LL, ('r'*n+'b',), (1,-1)))
    elif len(L) == 0:
        if R[0]=='r':
            ERES = gen_fR_B('','s',L,R,n-1)
            ERES.append((tuple(), ('r'*n+'a','d',R[2:]), (1,-1)))
            ERES.append((tuple(), ('r'*(n-1)+'d'+'a','d',*R[2:]), (1,1)))
        elif R[0]=='d':
            ERES = gen_fR_B('','s',L,R,n-1)
            ERES.append((tuple(), ('r'*(n-1)+'d'+'b','d',*R[2:]), (1,1)))
            ERES.append((tuple(), ('r'*n+'b','d',R[2:]), (1,-1)))
    else:
        if (L[0],R[0]) == ('s','r'):
            ERES = gen_fR_B('*','*',L,R,n-1)
            # if n>1: # or len(L)==len(R):
            #     ERES.append((('c',*L[1:]), ('r'*n + 'a','d',*R[1:]),(1, -1)))
        elif (L[0],R[0]) == ('s','d'):
            ERES = gen_fR_B('*','*',L,R,n-1)
            ERES.append((('c',*L[1:]), ('r'*(n-1)+'d'+'a',*R),(1, 1)))
            # if n==1 and len(L)==len(R):
            ERES.append((('c',*L[1:]), ('r'*n+'a', *R),(1,-1)))
            #ERES.append((('c',*L[1:]), ('r'*n+'a','d',*R[1:]),(1,-1)))
            #ERES.append((('c',*L[1:]), ('r'*n+'b','d',*R[1:]),(1, -1)))
        elif (L[0],R[0]) == ('c','r'):
            ERES = gen_fR_B('c','s',L,R,n-1)
            # if n==1 and len(L)!=len(R):
            #     ERES.append((('c',*L[1:]), ('r'+'a','d',*R[1:]),(1, -1)))
        elif (L[0],R[0]) == ('c','d'):
            ERES = gen_fR_B('c','s',L,R,n-1)
            #ERES.append((('c',*L[1:]), ('r'*n+'b','d',*R[1:]),(1, -1)))
            ERES.append((('c',*L[1:]), ('r'*n+'b', *R),(1, -1)))
            ERES.append((L, ('r'*(n-1)+'d'+'b',*R),(1, 1)))
            # if n==1 and len(L)!=len(R):
            #     ERES.append((('c',*L[1:]), ('d'+'a','d',*R[1:]),(1, -1)))
            # if n==1 and len(L)==len(R):
            #     ERES.append((('c',*L[1:]), ('d'+'a','d',*R[1:]),(1, -1)))
            # if n>1:
            #     ERES.append((L, ('r'*n+'b',*R),(1, 1)))
    return ERES

## New version
def lift_drc_M_B(drc, a):
    """
    Here we use extended drc diagram:
    'a'/'b' at the end of the longest column to indicate the form of B
    is given by adds 1 on p or q.
    """
    drcL, drcR = drc
    """
    Get the first and second column of left diagram
    and the first column of the right diagram.
    """
    fL, fR = getz(drcL, 0, ''), getz(drcR, 0, '')
    nL,  nR = len(fL), len(fR)
    if nL != nR:
        t = min(nL, nR)
        assert(nL-t <= 1 and nR - t <= 1)
    elif fL[-1:] == '*':
        t = len(fL)
    else:
        t = max(nR-1, 0)
    assert(nR <= a)
    tdrcL = tuple(col[:t] for col in drcL)
    tdrcR = tuple(col[:t] for col in drcR)
    try:
        tdrcL, tdrcR = sdot_switcher(tdrcL, tdrcR, t)
    except:
        print(str_dgms(drc), ' t=', t)
        print(fL,sL,fR)
        print(tdrcL,tdrcR)
        print(str_dgms((tdrcL,tdrcR)))
        return None
    #bdrcL, bdrcR = _add_bullet_D([fL[:nR]]+list(drcL[1:]),drcR)
    # print(fL)
    RES = []
    eRES = []
    L = ''.join(col[t:] for col in drcL)
    R = ''.join(col[t:] for col in drcR)
    ldrcD2 = gen_drc_B_two_new(L, R, a-t)
    for LL, RR, twist in ldrcD2:
        # print('%s,%s,%s'%(ffL,ffR,ssR))
        drcLL = tuple(col+getz(LL, i, '')  for i, col in enumerate(tdrcL))
        drcRR = tuple(col+getz(RR, i, '')  for i, col in enumerate(tdrcR))
        ndrc = reg_drc((drcLL, drcRR))
        RES.append(ndrc)
        eRES.append((ndrc, twist))
    try:
        assert(len(RES) == len(set(RES)))
    except:
        print(RES)
    return eRES

def updateDRCLS(RES, odrc, oLS, drc, LS, reportann = True):
    if drc in RES:
        print(concat_strblocks('Collision of keys: ', str_dgms(odrc), ' --> ', str_dgms(drc)))
        print(concat_strblocks(str_LS(RES[drc]),' --- ', str_LS(LS)))
    else:
        if reportann:
            if len(oLS) > len(LS):
                print('annihlation of LS: ')
                print(concat_strblocks(str_dgms(odrc),' --> ', str_dgms(drc)))
                print(concat_strblocks(str_LS(oLS), ' --> ',
                                       str_LS(LS)))
        RES[drc] = LS


def lift_drcs(DRCLS, rtype='C', ltype='l', report=False, reportann=False):
    """
    rtype is the target root system type.
    ltype is the lifting type:
                l: normal lift, 
                L: gneralized lift,
                n: size of orthogonal group if rtype = B/D
    """
    RES = dict()
    if rtype == 'C' and ltype == 'l':
        for drc, LS in DRCLS.items():
            pO, nO = gp_form_D(drc)
            ppO, nnO = sign_LS(LS)
            assert((pO, nO) == (ppO, nnO))
            anSp = len(drc[0][0])
            nSp = anSp + (pO+nO)//2
            # Lift trivial twist
            ndrc = lift_drc_D_C_trivial(drc)
            nLS = lift_D_C(LS, nSp)
            updateDRCLS(RES, drc, LS, ndrc, nLS, reportann=reportann)
            # Lift det twist
            dLS = char_twist_D(LS, (-1, -1))
            ndLS = lift_D_C(dLS, nSp)
            nddrc = twist_C_nonspecial(ndrc)
            updateDRCLS(RES, drc, dLS, nddrc, ndLS, reportann=reportann)
            if report:
                print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
                print(concat_strblocks(str_dgms(drc), '=d==>', str_dgms(nddrc)))
                print(concat_strblocks(str_LS(dLS), '==d==>', str_LS(ndLS)))
    elif rtype == 'C' and ltype == 'L':
        for drc, LS in DRCLS.items():
            pO, nO = gp_form_D(drc)
            ppO, nnO = sign_LS(LS)
            assert((pO, nO) == (ppO, nnO))
            anSp = len(drc[0][0])-1
            nSp = anSp + (pO+nO)//2
            # Lift trivial twist
            ndrc = lift_drc_D_C_gd(drc)
            if ndrc is not None:
                nLS = lift_D_C(LS, nSp)
                updateDRCLS(RES, drc, LS, ndrc, nLS, reportann=reportann)
                #RES[ndrc] = nLS
                if report:
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
    elif rtype == 'D':
        ltype == int(ltype)
        assert(ltype > 0)
        if len(DRCLS) == 0:
            zdrc = (('',), ('',))
            DRCLS[zdrc] = frozenset([tuple()])
        for drc, LS in DRCLS.items():
            if drc is None:
                continue
            nSp = gp_form_C(drc)
            nnSp = sign_LS(LS)[0]
            assert(nSp == nnSp)
            aL = ltype//2 - nSp
            NDRCS = lift_drc_C_D(drc, aL)
            for ndrc, twist in NDRCS:
                pO, nO = gp_form_D(ndrc)
                nLS = lift_C_D(LS, pO, nO)
                # if schar_is_trivial_D(ndrc):
                #     twist = (1,-1)
                # else:
                #     twist = (1,1)
                nLS = char_twist_D(nLS, twist)
                updateDRCLS(RES, drc, LS, ndrc, nLS, reportann=reportann)
                # RES[ndrc]=nLS
                if report:
                    print('twit sign', twist)
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS),
                                           '==d==>', str_LS(
                                               char_twist_B(nLS, (-1, -1))),
                                           '==td==>', str_LS(
                                               char_twist_B(nLS, (1, -1))),
                                           '==dt==>', str_LS(
                                               char_twist_B(nLS, (-1, 1))),
                                           ))
    elif rtype == 'M' and ltype == 'l':
        """
        we work on extended drc diagram!
        """
        for drc, LS in DRCLS.items():
            drcL, drcR = drc
            if len(drcR) == 0:
                drcR = ('',)
                drc = (drcL, drcR)
            pO, nO = gp_form_B_ext(drc)
            ppO, nnO = sign_LS(LS)
            assert((pO, nO) == (ppO, nnO))
            acL = len(getz(drcR, 0, ''))
            nSp = acL + (pO+nO-1)//2
            # Lift trivial twist
            ndrc = lift_extdrc_B_M_trivial(drc, acL)
            if ndrc is None:
                print('drc has no lift', drc)
                continue
            nLS = lift_B_M(LS, nSp)
            updateDRCLS(RES, drc, LS, ndrc, nLS, reportann=reportann)
            # Lift the determinant twist
            nddrc = twist_M_nonspecial(ndrc)
            if nddrc is None:
                print('ndrc has no twist', ndrc)
                continue
            dLS = char_twist_B(LS, (-1, -1))
            ndLS = lift_B_M(dLS, nSp)
            updateDRCLS(RES, drc, dLS, nddrc, ndLS, reportann=reportann)
            if report:
                print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
                print(concat_strblocks(str_dgms(drc), '=d==>', str_dgms(nddrc)))
                print(concat_strblocks(str_LS(dLS), '==d==>', str_LS(ndLS)))
    elif rtype == 'M' and ltype == 'L':
        for drc, LS in DRCLS.items():
            drcL, drcR = drc
            if len(drcR) == 0:
                drcR = ('',)
                drc = (drcL, drcR)
            pO, nO = gp_form_B_ext(drc)
            ppO, nnO = sign_LS(LS)
            assert((pO, nO) == (ppO, nnO))
            acL = len(getz(drcR, 0, '')) - 1
            nSp = acL + (pO+nO-1)//2
            # Lift trivial twist
            ndrc = lift_extdrc_B_M_trivial(drc, acL)
            if ndrc is not None:
                #print(concat_strblocks(str_dgms(drc),' has no lift'))
                #continue
                nLS = lift_B_M(LS, nSp)
                updateDRCLS(RES, drc, LS, ndrc, nLS, reportann=reportann)
                if report:
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
    elif rtype == 'B':
        assert(ltype == int(ltype))
        assert(ltype > 0)
        if len(DRCLS) == 0:
            zdrc = (('',), ('',))
            DRCLS[zdrc] = frozenset([tuple()])
        LSDIC = dict()
        for drc, LS in DRCLS.items():
            if drc is None:
                continue
            nSp = gp_form_M(drc)
            nnSp = sign_LS(LS)[0]
            assert(nSp == nnSp)
            aL = (ltype-1)//2 - nSp
            NDRCS = lift_drc_M_B(drc, aL)
            # try:
            #     NDRCS = lift_drc_M_B(drc, aL)
            # except:
            #     print('Exception on lift_drc_M_B')
            #     print(str_dgms(drc))
            for ndrc, twist in NDRCS:
                pO, nO = gp_form_B_ext(ndrc)
                nLS = lift_M_B(LS, pO, nO)
                if len(nLS) == 0:
                    print('the ndrc and LS has no lift')
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
                nLS = char_twist_B(nLS, twist)
                updateDRCLS(RES, drc, LS, ndrc, nLS, reportann=reportann)
                ndLS = char_twist_B(nLS, (-1, -1))
                keyLS = frozenset([str_LS(nLS), str_LS(ndLS)])
                if keyLS in LSDIC:
                    LSDIC[keyLS].extend(['  ', str_LS(LS), '<=>', str_dgms(drc),
                                         '==>', str_dgms(ndrc), str_LS(nLS)])
                    print('Collision of LS')
                    print(concat_strblocks(str_LS(nLS), '<==d==>', str_LS(ndLS)))
                    print(concat_strblocks(*LSDIC[keyLS]))
                else:
                    LSDIC[keyLS] = [str_LS(LS), '<=>', str_dgms(drc), ' ==>',
                                    str_dgms(ndrc), '<=>', str_LS(nLS)]
                if report:
                    print('twit sign', twist)
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS),
                                           '==d==>', str_LS(
                                               char_twist_B(nLS, (-1, -1))),
                                           '==td==>', str_LS(
                                               char_twist_B(nLS, (1, -1))),
                                           '==dt==>', str_LS(
                                               char_twist_B(nLS, (-1, 1))),
                                           ))
                #print(ndrc, nLS)
            RES['LSDIC'] = LSDIC
    return RES


GPSIGN = {
    'D': gp_form_D,
    'B': gp_form_B,
    'C': gp_form_C,
    'M': gp_form_M,
}


def print_DRCLS(DRCLS, rtype):
    for drc, LS in DRCLS.items():
        # print(drc,LS)
        print(str_dgms(drc))
        if rtype in ('C', 'M'):
            print('drc sign', (GPSIGN[rtype](drc)))
        else:
            print('drc sign', (GPSIGN[rtype](drc)))
        print(str_LS(LS))
        print('LS sign', sign_LS(LS))
        print('----------------------')


def print_LSDRC(LSDRC):
    for LS, drcs in LSDRC.items():
        # print(drc,LS)
        print(str_LS(LS))
        for drc in drcs:
            print('~~~~~~~~~~~~~~~~~')
            print(str_dgms(drc))
        print('----------------------')


def schar_is_trivial_D(drc):
    drcL, drcR = drc
    if drcL[0][-1] == 'd':
        return False
    else:
        return True


def test_young_dg(dg):
    return all(len(getz(dg, i, '')) >= len(getz(dg, i+1, ''))
               for i in range(len(dg)))


def test_young_drc(drc):
    drcL, drcR = drc
    return test_young_dg(drcL) and test_young_dg(drcR)


def test_bullets_drc(drc):
    drcL, drcR = drc
    for i in range(max(len(drcL), len(drcR))):
        cL, cR = getz(drcL, i, ''), getz(drcR, i, '')
        nL, nR = cL.count('*'), cR.count('*')
        if (len(cL), len(cR)) != (nL, nR) or len(cL) != len(cR):
            return False
    return True


def remove_tail_letter(dg, l, onerow=False):
    ddg = []
    for col in dg:
        dcol = col.rstrip(l)
        if onerow and len(col)-len(dcol) > 1:
            return None
        ddg.append(dcol)
    return tuple(ddg)


def verify_drc(drc, rtype='C'):
    if rtype == 'C':
        drcL, drcR = drc
        if test_young_dg(drcL) is False or test_young_dg(drcR) is False:
            return False
        cdrcL = remove_tail_letter(drcL, 'd', onerow=True)
        if cdrcL is None or test_young_dg(cdrcL) is False:
            return False
        ccdrcL = remove_tail_letter(cdrcL, 'c', onerow=True)
        if ccdrcL is None or test_young_dg(ccdrcL) == False:
            return False
        rccdrcL = remove_tail_letter(ccdrcL, 'r')
        rdrcR = remove_tail_letter(drcR, 's')
        if rccdrcL is None or test_young_dg(rccdrcL) is False or \
                rdrcR is None or test_young_dg(rdrcR) is False or\
                test_bullets_drc((rccdrcL, rdrcR)) is False:
            return False
    elif rtype == 'D':
        drcL, drcR = drc
        if test_young_dg(drcL) is False or test_young_dg(drcR) is False:
            return False
        cdrcL = remove_tail_letter(drcL, 'd', onerow=True)
        if cdrcL is None or test_young_dg(cdrcL) is False:
            return False
        ccdrcL = remove_tail_letter(cdrcL, 'c', onerow=True)
        if ccdrcL is None or \
                test_young_dg(cdrcL) == False:
            return False
        rccdrcL = remove_tail_letter(ccdrcL, 'r')
        if rccdrcL is None:
            return False
        srccdrcL = remove_tail_letter(rccdrcL, 's')
        if srccdrcL is None or \
                test_bullets_drc((srccdrcL, drcR)) is False:
            return False
    return True


def switch_kv(D):
    RD = dict()
    for k, v in D.items():
        RD.setdefault(v, []).append(k)
    return RD


def reg_drc(drc):
    if drc is None:
        return None
    drcL, drcR = drc
    drcL = tuple(x for x in drcL if len(x) > 0)
    drcR = tuple(x for x in drcR if len(x) > 0)
    return (drcL, drcR)


def compare_drc(DRCL1, DRCL2):
    DRCL1 = set(reg_drc(drc) for drc in DRCL1)
    DRCL2 = set(reg_drc(drc) for drc in DRCL2)
    return (DRCL1-DRCL2, DRCL2-DRCL1)


def compare_LS(LLS1, LLS2):
    LLS1 = set(LLS1)
    LLS2 = set(LLS2)
    return (LLS1-LLS2, LLS2-LLS1)


def det_DRCLS(DRCLS):
    RES = dict()
    for drc, LS in DRCLS:
        RES[drc] = (LS, char_twist_D(LS, (-1, -1)))
    return RES


TWISTFUN = {'D': char_twist_D,
            'B': char_twist_B}


def det_all_LS(LSS, rtype='D'):
    RES = set()
    twistfun = TWISTFUN[rtype]
    for LS in LSS:
        RES.update([LS, twistfun(LS, (-1, -1))])
    return RES

def det_only_LS(LSS, rtype='D'):
    twistfun = TWISTFUN[rtype]
    RES = set(twistfun(LS,(-1,-1)) for LS in LSS)
    return RES

def asign_all_LS(LSS, rtype='D'):
    RES = set()
    twistfun = TWISTFUN[rtype]
    for LS in LSS:
        RES.update([LS, twistfun(LS, (-1, 1)),
                    twistfun(LS, (1, -1)), twistfun(LS, (-1, -1))])
    return RES


def print_nonone(LSDRC):
    for LS, drcs in LSDRC3.items():
        if len(drcs) > 1:
            print(str_LS(LS))
            print('\n~~~~~~~~~~~~\n'.join([str_dgms_D(drc) for drc in drcs]))


LtypesLST = {
    'D': ('D', 'C'),
    'C': ('C', 'D'),
    'M': ('M', 'B'),
    'B': ('B', 'M'),
}


def ext_drc2drc(edrc):
    edrcL, edrcR = edrc
    drcR = (edrcR[0][:-1], *edrcR[1:])
    return (edrcL, drcR)


def test_LSDRC(part, rtype='D', report=False, reportann=False):
    Ltypes = LtypesLST[rtype]
    DRCLS = dict()
    for i in range(len(part)-1, -1, -1):
        # 'p' means present
        ppart = part[i:]
        prtype = Ltypes[i % 2]
        if prtype in ('D', 'B'):
            if (ppart[0] % 2 == 1 and prtype == 'D') or \
               (ppart[0] % 2 == 0 and prtype == 'B'):
                ppart = (ppart[0]+1, *ppart[1:])
            ldrcarg = (DRCLS, prtype, sum(ppart))
        elif prtype in ('C', 'M'):
            if (ppart[0] % 2 == 1 and prtype == 'C') or \
               (ppart[0] % 2 == 0 and prtype == 'M'):
                ldrcarg = (DRCLS, prtype, 'L')
            else:
                ldrcarg = (DRCLS, prtype, 'l')

        DRCLS = lift_drcs(*ldrcarg, report=report, reportann=reportann)
        # LSDIC
        LSDIC = None
        if prtype == 'B':
            LSDIC = DRCLS.pop('LSDIC',None)
        # print(DRCLS)
        Adrcs = part2drc(ppart, prtype, printdig=False, report=report)
        ALS = part2LS(ppart, prtype, report=report)

        print('Partition type %s  %s:' % (prtype, ppart))
        Gdrcs = DRCLS.keys()
        if prtype == 'B':
            Gdrcs = set([ext_drc2drc(edrc) for edrc in Gdrcs])
        LDDRC, RDDRC = compare_drc(Adrcs, Gdrcs)
        if len(RDDRC) > 0:
            print('Adrcs dose not include DRCLS', RDDRC)
        if len(LDDRC) > 0:
            print('Number of all DRCS:', len(Adrcs))
            print('Number of lifted DRCS:', len(Gdrcs))
            for drc in LDDRC:
                print(str_dgms(drc))
                print(GPSIGN[prtype](drc))

        LLS = DRCLS.values()
        if prtype == 'D':
            LLS = det_all_LS(LLS, rtype=prtype)
        elif prtype == 'B':
            LLS = det_all_LS(LLS, rtype=prtype)
            #LLS = asign_all_LS(LLS, rtype=prtype)
        DLS, _ = compare_LS(ALS, LLS)
        # print(ALS)
        # print(DRCLS)
        #print_DRCLS(DRCLS, prtype)
        if len(DLS) > 0:
            print('Missing %d LS:' % len(DLS))
            for LS in DLS:
                print(str_LS(LS))
                #if LSDIC and prtype == 'B':
                #    sLS = str_LS(LS), 
                print('~~~~~~~~~~~~~~~')
            return False
    return True



def test_purelyeven(part, rtype='D', report=False, reportann=False, reportpack = False):
    Ltypes = LtypesLST[rtype]

    lDRCLS = [dict()]
    lLSDRC = [dict()]
    for i in range(len(part)-1, -1, -1):
        DRCLS = lDRCLS[-1]
        LSDRC = lLSDRC[-1]
        # 'p' means previous
        ppart = part[i:]
        prtype = Ltypes[i % 2]
        if prtype in ('D', 'B'):
            if (ppart[0] % 2 == 1 and prtype == 'D') or \
               (ppart[0] % 2 == 0 and prtype == 'B'):
                ppart = (ppart[0]+1, *ppart[1:])
            ldrcarg = (DRCLS, LSDRC, prtype, sum(ppart))
        elif prtype in ('C', 'M'):
            if (ppart[0] % 2 == 1 and prtype == 'C') or \
               (ppart[0] % 2 == 0 and prtype == 'M'):
                ldrcarg = (DRCLS, LSDRC, prtype, 'L')
            else:
                ldrcarg = (DRCLS, LSDRC, prtype, 'l')

        nDRCLS, nLSDRC = lift_pedrcs(*ldrcarg, report=report, reportann=reportann)
        lDRCLS.append(nDRCLS)
        lLSDRC.append(nLSDRC)

        # print(DRCLS)
        Adrcs = part2drc(ppart, prtype, printdig=False, report=report)
        ALS = part2LS(ppart, prtype, report=report)

        Gdrcs = nDRCLS.keys()
        LLS = set(nLSDRC.keys())
        if prtype == 'D':
            #LLS = det_all_LS(LLS, rtype=prtype)
            DetLS = det_only_LS(LLS,rtype=prtype)
            assert(DetLS.isdisjoint(LLS))
            LLS = DetLS.union(LLS)
        elif prtype == 'B':
            LLS = det_all_LS(LLS, rtype=prtype)
            #LLS = asign_all_LS(LLS, rtype=prtype)
        # report some basic facts
        print('Partition type %s  %s:' % (prtype, ppart))
        if rtype == 'B':
            print('#DRCS:\t%d,\t#ALS\t%s' %(len(Adrcs)*2, len(ALS)))
        else:
            print('#DRCS:\t%d,\t#ALS\t%s' %(len(Adrcs), len(ALS)))
        print('#GDRCS:\t%d,\t#GLS\t%s' % (len(Gdrcs), len(LLS)))


        if reportpack:
            for LS, (sign, lst) in nLSDRC.items():
                if len(lst)>1:
                    print('Packet of %s (%d,%d)'%(rtype, *sign))
                    for dd, ll, odd, oeps, oll in lst:
                        print(concat_strblocks(str_dgms(odd),', %d , '%oeps, str_LS(oll), ' ---> ',
                                               str_dgms(dd),' , ', str_LS(ll)))



        if prtype == 'B':
            Gdrcs = set([ext_drc2drc(edrc) for edrc in Gdrcs])
        LDDRC, RDDRC = compare_drc(Adrcs, Gdrcs)
        if len(RDDRC) > 0:
            print('Adrcs dose not include DRCLS', RDDRC)
        if len(LDDRC) > 0:
            print('Number of all DRCS:', len(Adrcs))
            print('Number of lifted DRCS:', len(Gdrcs))
            for drc in LDDRC:
                print(str_dgms(drc))
                print(GPSIGN[prtype](drc))

        DLS, _ = compare_LS(ALS, LLS)
        # print(ALS)
        # print(DRCLS)
        #print_DRCLS(DRCLS, prtype)
        if len(DLS) > 0:
            print('Missing %d LS:' % len(DLS))
            for LS in DLS:
                print(str_LS(LS))
                #if LSDIC and prtype == 'B':
                #    sLS = str_LS(LS),
                print('~~~~~~~~~~~~~~~')
            return (lDRCLS, lLSDRC)
    return (lDRCLS, lLSDRC)

def getLSpacket(LS, dLSDRC):
    sign, lst = dLSDRC.get(LS,((0,0),[]))
    res = [(dd, oeps) for dd, ll, odd, oeps, oll in lst]
    return res

def strLSpacket(LS, dLSDRC):
    res = getLSpacket(LS, dLSDRC)
    return concat_strblocks(*('%d\n%s'%(oeps, str_dgms(dd)) for dd, oeps in res), sep=' , ')

#def updatepeDRCLS(DRCLS, LSDRC, odrc, oeps, oLS, drc, LS, reportann = False, reportLSpack = True):
def updatepeDRCLS(DRCLS, LSDRC, odrc, oeps, oLS, drc, LS, reportann = False, reportLSpack = False):
    if drc in DRCLS:
        print(concat_strblocks('Collision of keys: ', str_dgms(odrc), ' --> ', str_dgms(drc)))
        print(concat_strblocks(str_LS(RES[drc]),' --- ', str_LS(LS)))
    else:
        if reportann:
            if len(oLS) > len(LS):
                print('annihlation of LS: ')
                print(concat_strblocks(str_dgms(odrc),' --> ', str_dgms(drc)))
                print(concat_strblocks(str_LS(oLS), ' --> ',
                                       str_LS(LS)))
        DRCLS[drc] = LS
        if LS in LSDRC:
            ooLSsign, lst = LSDRC[LS]
            oLSsign = sign_LS(oLS)
            if reportLSpack or ooLSsign != oLSsign:
                print('a local system packet lifted from different forms', oLSsign, ooLSsign)
                print(concat_strblocks(str_dgms(odrc),', %d , '%oeps,  str_LS(oLS), ' ---> ',
                                       str_dgms(drc),' , ', str_LS(LS)))
                for dd, ll, odd, oeps, oll in lst:
                    print(concat_strblocks(str_dgms(odd),', %d , '%oeps, str_LS(oll), ' ---> ',
                                           str_dgms(dd),' , ', str_LS(ll)))
            # Test the packet has same oeps
            lst.append( (drc,LS, odrc, oeps, oLS) )
            if len(set(it[3] for it in lst))>1:
                print('a local system packet has different epsilon')
                for dd, ll, odd, oeps, oll in lst:
                    print(concat_strblocks(str_dgms(odd),', %d , '%oeps, str_LS(oll), ' ---> ',
                                           str_dgms(dd),' , ', str_LS(ll)))
            LSDRC[LS] = (ooLSsign,  lst)
        else:
            LSDRC[LS] = (sign_LS(oLS), [(drc, LS, odrc, oeps, oLS)] )

def lift_pedrcs(DRCLS, LSDRC, rtype='C', ltype='l', report=False, reportann=False):
    """
    rtype is the target root system type.
    ltype is the lifting type:
                l: normal lift,
                L: gneralized lift,
                n: size of orthogonal group if rtype = B/D
    """
    nDRCLS, nLSDRC = dict(), dict()
    RES = dict()
    if rtype == 'C' and ltype == 'l':
        for drc, LS in DRCLS.items():
            pO, nO = gp_form_D(drc)
            ppO, nnO = sign_LS(LS)
            assert((pO, nO) == (ppO, nnO))
            anSp = len(drc[0][0])
            nSp = anSp + (pO+nO)//2
            # Lift trivial twist, oeps = 0
            oeps = 0
            ndrc = lift_drc_D_C_trivial(drc)
            nLS = lift_D_C(LS, nSp)
            updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, ndrc, nLS, reportann=reportann)
            # Lift det twist, oeps = 1
            oeps = 1
            dLS = char_twist_D(LS, (-1, -1))
            ndLS = lift_D_C(dLS, nSp)
            nddrc = twist_C_nonspecial(ndrc)
            updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, dLS, nddrc, ndLS, reportann=reportann)
            if report:
                print(concat_strblocks(str_dgms(drc),  '====>', str_dgms(ndrc)))
                print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
                print(concat_strblocks(str_dgms(drc), '=d==>', str_dgms(nddrc)))
                print(concat_strblocks(str_LS(dLS), '==d==>', str_LS(ndLS)))
    elif rtype == 'C' and ltype == 'L':
        for drc, LS in DRCLS.items():
            pO, nO = gp_form_D(drc)
            ppO, nnO = sign_LS(LS)
            assert((pO, nO) == (ppO, nnO))
            anSp = len(drc[0][0])-1
            nSp = anSp + (pO+nO)//2
            # Lift trivial twist
            ndrc = lift_drc_D_C_gd(drc)
            if ndrc is not None:
                nLS = lift_D_C(LS, nSp)
                # only lift the trivial twist, oeps = 0
                oeps = 0
                updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, ndrc, nLS, reportann=reportann)
                #RES[ndrc] = nLS
                if report:
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
    elif rtype == 'D':
        ltype == int(ltype)
        assert(ltype > 0)
        if len(DRCLS) == 0:
            zdrc = (('',), ('',))
            zLS = frozenset([tuple()])
            DRCLS[zdrc] = zLS
            LSDRC[zLS] = ((0,0), [(zdrc, zLS, zdrc, 0, zLS)])
        for drc, LS in DRCLS.items():
            #if drc is None:
            #    continue
            nSp = gp_form_C(drc)
            nnSp = sign_LS(LS)[0]
            assert(nSp == nnSp)
            aL = ltype//2 - nSp
            NDRCS = lift_drc_C_D(drc, aL)
            for ndrc, twist in NDRCS:
                pO, nO = gp_form_D(ndrc)
                nLS = lift_C_D(LS, pO, nO)
                nLS = char_twist_D(nLS, twist)
                if twist == (1,1):
                    oeps = 0
                else:
                    oeps = 1
                updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, ndrc, nLS, reportann=reportann)
                # RES[ndrc]=nLS
                if report:
                    print('twit sign', twist)
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS),
                                           '==d==>', str_LS(
                                               char_twist_B(nLS, (-1, -1))),
                                           '==td==>', str_LS(
                                               char_twist_B(nLS, (1, -1))),
                                           '==dt==>', str_LS(
                                               char_twist_B(nLS, (-1, 1))),
                                           ))
    elif rtype == 'M' and ltype == 'l':
        """
        we work on extended drc diagram!
        """
        for drc, LS in DRCLS.items():
            drcL, drcR = drc
            if len(drcR) == 0:
                drcR = ('',)
                drc = (drcL, drcR)
            pO, nO = gp_form_B_ext(drc)
            ppO, nnO = sign_LS(LS)
            assert((pO, nO) == (ppO, nnO))
            acL = len(getz(drcR, 0, ''))
            nSp = acL + (pO+nO-1)//2
            # Lift trivial twist, oeps = 0
            oeps = 0
            ndrc = lift_extdrc_B_M_trivial(drc, acL)
            if ndrc is None:
                print('drc has no lift', drc)
                continue
            nLS = lift_B_M(LS, nSp)
            updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, ndrc, nLS, reportann=reportann)
            # Lift the determinant twist
            # Lift the determinant twist, oeps = 1
            oeps = 1
            nddrc = twist_M_nonspecial(ndrc)
            if nddrc is None:
                print('ndrc has no twist', ndrc)
                continue
            dLS = char_twist_B(LS, (-1, -1))
            ndLS = lift_B_M(dLS, nSp)
            updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, nddrc, ndLS, reportann=reportann)
            if report:
                print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
                print(concat_strblocks(str_dgms(drc), '=d==>', str_dgms(nddrc)))
                print(concat_strblocks(str_LS(dLS), '==d==>', str_LS(ndLS)))
    elif rtype == 'M' and ltype == 'L':
        for drc, LS in DRCLS.items():
            drcL, drcR = drc
            if len(drcR) == 0:
                drcR = ('',)
                drc = (drcL, drcR)
            pO, nO = gp_form_B_ext(drc)
            ppO, nnO = sign_LS(LS)
            assert((pO, nO) == (ppO, nnO))
            acL = len(getz(drcR, 0, '')) - 1
            nSp = acL + (pO+nO-1)//2
            # Lift trivial twist
            ndrc = lift_extdrc_B_M_trivial(drc, acL)
            if ndrc is not None:
                #print(concat_strblocks(str_dgms(drc),' has no lift'))
                #continue
                nLS = lift_B_M(LS, nSp)
                # only lift the trivial twist, oeps = 0
                oeps = 0
                updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, ndrc, nLS, reportann=reportann)
                if report:
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
    elif rtype == 'B':
        assert(ltype == int(ltype))
        assert(ltype > 0)
        if len(DRCLS) == 0:
            zdrc = (('',), ('',))
            DRCLS[zdrc] = frozenset([tuple()])
        for drc, LS in DRCLS.items():
            if drc is None:
                continue
            nSp = gp_form_M(drc)
            nnSp = sign_LS(LS)[0]
            assert(nSp == nnSp)
            aL = (ltype-1)//2 - nSp
            NDRCS = lift_drc_M_B(drc, aL)
            # try:
            #     NDRCS = lift_drc_M_B(drc, aL)
            # except:
            #     print('Exception on lift_drc_M_B')
            #     print(str_dgms(drc))
            for ndrc, twist in NDRCS:
                pO, nO = gp_form_B_ext(ndrc)
                nLS = lift_M_B(LS, pO, nO)
                if len(nLS) == 0:
                    print('the ndrc and LS has no lift')
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
                nLS = char_twist_B(nLS, twist)
                if twist == (1,1):
                    oeps = 0
                else:
                    oeps = 1
                updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, ndrc, nLS, reportann=reportann)
                #updateDRCLS(RES, drc, LS, ndrc, nLS, reportann=reportann)
                ndLS = char_twist_B(nLS, (-1, -1))
                keyLS = frozenset([str_LS(nLS), str_LS(ndLS)])
                #print(ndrc, nLS)
                if report:
                    print('twit sign', twist)
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS),
                                           '==d==>', str_LS(
                                               char_twist_B(nLS, (-1, -1))),
                                           '==td==>', str_LS(
                                               char_twist_B(nLS, (1, -1))),
                                           '==dt==>', str_LS(
                                               char_twist_B(nLS, (-1, 1))),
                                           ))
            #RES['LSDIC'] = LSDIC
    #print('[red]end test_pedrclift[/red]')
    return nDRCLS, nLSDRC
