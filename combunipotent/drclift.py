from rich import print
from itertools import chain, zip_longest
from copy import copy, deepcopy
from multiset import FrozenMultiset as frozenset
from .tool import getz, dualBVW, concat_strblocks
from .drc import str_dgms, reg_drc, verify_drc, gp_form_D, gp_form_B,gp_form_C, gp_form_M, dpart2drc, countdrcform
from .LS import lift_C_D, lift_D_C, lift_B_M, lift_M_B, char_twist_D, char_twist_B, part2LS, str_LS, sign_LS

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


def lift_extdrc_B_M(drc, a):
    # Attache a length 'a' columne on the left diagram
    # We assume a > 0
    drcL, drcR = drc
    assert(len(drcR[0])>0)
    exttype = drcR[0][-1]
    assert(exttype in ('a','b'))
    # This get the usual drc diagram.
    drcR = (drcR[0][:-1], *drcR[1:])

    fL, fR = getz(drcL,0,''), getz(drcR,0,'')

    if exttype == 'a':
        ndrcL = ('*'*(a-1)+'*', *drcL)
    else: #exttype == 'b'
        #if a == len(fR) and fR[-1] in ('s','*'):
        #    return None
        ndrcL = ('*'*(a-1)+'c', *drcL)
    try:
        ndrc = _fill_ds_M((ndrcL,drcR))
        return ndrc
    except:
        return None


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

def descent_drc(drc, rtype):
    drcL, drcR = drc
    fL, sL, fR = getz(drcL, 0, ''), getz(drcL, 1, ''), getz(drcR, 0, '')
    if rtype == 'C':
        if len(fL)>len(fR):
            # Non-special shape case:
            # Twist back to the spacial partition
            drcL,drcR = twist_nsp2sp(drc,'C')
        # naive descent
        res = _fill_ds_D((drcL, drcR[1:]))
        assert(verify_drc(res,'D'))
    elif rtype == 'D':
        # naive descent
        res = _fill_ds_C((drcL[1:],drcR))
        resL, resR = res
        if len(sL) == len(fR)+1:
            # This is the case r_2(dpart) = r_3(dpart)
            # Exceptional case: drcL[2] end with 'c' and drcL(i,1) in 'rd' for all |sL|<= i
            # In other words: fL[|sL|-1:] contains no 's' and 'c'
            if fL.count('c')==0 and fL[len(sL)-1:].count('s')==0 and sL[-1:] == 'c':
                res = ((resL[0][:-1]+'r', *resL[1:]), resR)
        elif len(sL)>= len(fR)+2:
            # This is the case (2,3) in PP
            # drc has non-special shape
            x0 = fL[len(sL)-2]
            if x0 in 'rc':
                res = ((resL[0][:-2]+'r'+x0, *resL[1:]), resR)
        elif rtype == 'M':
            pass
    res = reg_drc(res)
    return res


def lift_dgms_D_C(dgms, cR):
    S = []
    for drc in dgms:
        ldrc = lift_drc_D_C(drc, cR)
        if ldrc is not None:
            S.append(ldrc)
    return S


def _count_ds(s):
    """
    count the number of '*' and 's' in a string
    """
    return s.count('*') + s.count('s')

def _fill_ds_C(drc):
    drcL, drcR = drc
    ndrcL,ndrcR = [], []
    for colL, colR in zip_longest(drcL, drcR, fillvalue=''):
        cL, cR = _count_ds(colL), len(colR)
        assert(cL<=cR)
        ndrcL.append('*'*cL+colL[cL:])
        ndrcR.append('*'*cL+'s'*(cR-cL))
    res = reg_drc((tuple(ndrcL), tuple(ndrcR)))
    return res


def _fill_ds_B(drc):
    drcL, drcR = drc
    ndrcR = [] #tuple('*'*len(col) for col in drcR)
    ndrcL = []
    for colL, colR in zip_longest(drcL,drcR, fillvalue=''):
        cL, cR = _count_ds(colL), _count_ds(colR)
        if cL > cR:
            print('error')
            print(str_dgms(drc))
            assert(cL<=cR)
        ndrcL.append('*'*cL+colL[cL:])
        ndrcR.append('*'*cL+'s'*(cR-cL)+colR[cR:])
    res = (tuple(ndrcL), tuple(ndrcR))
    assert(verify_drc(res,'B'))
    return reg_drc(res)

def _fill_ds_M(drc):
    drcL, drcR = drc
    ndrcR = [] #tuple('*'*len(col) for col in drcR)
    ndrcL = []
    for colL, colR in zip_longest(drcL,drcR, fillvalue=''):
        cL, cR = _count_ds(colL),  _count_ds(colR)
        assert(cL>=cR)
        ndrcL.append('*'*cR+'s'*(cL-cR)+colL[cL:])
        ndrcR.append('*'*cR+colR[cR:])
    res = (tuple(ndrcL), tuple(ndrcR))
    assert(verify_drc(res,'M'))
    return reg_drc(res)


def lift_drc_D_C(drc, cR, printdrop=False):
    """
    cR : The length of the new first column on the right
    if the lenght of '*'/'s' in the first column of drcL > cR
    then there is no lift. 
    Otherwise there is a lift.
    """
    drcL, drcR = drc
    # the number of '*s' in the first column of drcL
    bL = _count_ds(getz(drcL,0,''))
    if bL > cR:
        return None
    else:
        res = _fill_ds_C((drcL, ('*'*cR, *drcR)))
        return res


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


def test_sp2nsp_twist(dpart,rtype,print=print):
    """
    This function tests our special-nonspecial shape twisting algorithm
    It shows that the twisting gives a bijection.
    """
    print(r'Let $\mathcal O^\vee$ has rows $%s$'%(list(dpart),))
    part = dualBVW(dpart,rtype,partrc='c')
    print(r'Then $\mathcal O$ has columns $%s$'%(part,))
    WLC = dualpart2LC(dpart,rtype)


    PBPlist = LC2pbps(WLC,rtype)

    for pp, PBPs in PBPlist.items():
        tau = WLC[pp]
        if 0 not in pp:
            print(f"The  $\\wp = $ {set(pp)} \
                    $\\mapsto \\tau =$ {tau[0]} $\\times$ {tau[1]} \
                    attached to {len(PBPs)} PBPS")
            # tau_pp is special shape in this case
            PBPns = []
            for pbp in PBPs:
                pbpns = twist_sp2nsp(pbp,rtype)
                rpbp = twist_nsp2sp(pbpns,rtype)
                assert(rpbp == pbp)
                PBPns.append(pbpns)
            PBPns = set(PBPns)
            PPup = frozenset(pp|set([0]))
            print(f"The non-special $\\wp_{{\\uparrow}}=$  {set(PPup)} and $|PBP(\\tau_{{\\wp_{{\\uparrow}}}})| = $ {len(PBPns)}")
            #print(PBPlist[PPd])
            #print(pbpdowns)
            #print(frozenset(PBPlist[PPd])-frozenset(pbpdowns))
            #print(frozenset(pbpdowns)-frozenset(PBPlist[PPd]))
            #printpbplist(pbpdowns)
            assert(frozenset(PBPlist[PPup])==frozenset(PBPns))

def twist_nsp2sp(drc,rtype):
    if rtype == 'C':
        """
        send a non-special diagram to special diagram
        non-special diagram means c_1(tau_L)>= c_1(tau_R)+2
        """
        drcL, drcR = drc
        fL, sL, fR = getz(drcL, 0, ''), getz(drcL, 1, ''), getz(drcR, 0, '')
        l  = len(fL)-len(fR)-2
        # Check that pbp has non-special shape
        assert(l>=0)
        if fL[-2] == 'c':
            if len(fR)>0 and fL[len(fR)-1] == 'r':
                fLL = fL[:len(fR)-1]+'cd'
                sLL = sL
                fRR = fR + 's'*(l+1)
            else:
                fLL = fL[:len(fR)]+'*'
                sLL = sL
                fRR = fR + '*'+'s'*l
        else:
            # Now fL[-2] == 'r'
            if len(fR)+1 == len(sL) and (sL[-1],fL[-1]) == ('c','d'):
                fLL = fL[:len(fR)]+'*'
                sLL = sL[:len(fR)]+'r'
                fRR = fR +'*'+'s'*l
            else:
                fLL = fL[:len(fR)]+fL[-1]
                sLL = sL
                fRR = fR + 's'*(l+1)
        spdrc = ((fLL, sLL, *drcL[2:]), (fRR, *drcR[1:]))
    elif rtype == 'M':
        spdrc = twist_M_nonspecial(drc)
    else:
        raise ValueError("Wrong root system type")
    if not verify_drc(spdrc, rtype):
        print('Invalid special drc\n original: \n%s\n new:\n%s\n'
            % (str_dgms(drc), str_dgms(spdrc)))
    return reg_drc(spdrc)

def twist_sp2nsp(drc,rtype):
    if rtype == 'C':
        res = twist_C_nonspecial(drc)
    elif rtype == 'M':
        res = twist_M_nonspecial(drc)
    else:
        raise ValueError("Wrong root system type")
    return reg_drc(res)

## The general Version
def twist_C_nonspecial(drc):
    """
    send a special diagram to non-special diagram
    special diagram means 0<c_1(tau_L)<= c_1(tau_R)
    """
    drcL, drcR = drc
    # first, second column of drcL and first column of drcR
    fL, sL, fR = getz(drcL, 0, ''), getz(drcL, 1, ''), getz(drcR, 0, '')
    l  = len(fR)-len(fL)
    # Check drc has special shape
    assert(l >= 0 and len(fL) > 0)
    fRR,x3 = fR[:-l-1], fR[-l-1]
    # x3 == 's' iff x2 := fL[-1] != '*'
    # x3 == '*' iff x2 := fL[-1] == '*'
    if x3 == 's':
        if len(fL) == 1 or fL[-2] != 'c':
            fLL = fL[:-1]+'r'*(l+1)+fL[-1:]
        else:
            # In this case fL[-2:] = 'cd'
            fLL = fL[:-2]+'r'*(l+1)+fL[-2:]
        nspdrc = ((fLL, *drcL[1:]), (fRR, *drcR[1:]))
    else:
        # Now fR[-l-1] == '*'
        if getz(sL, len(fL)-1, '') == 'r':
            fLL = fL[:-1]+'r'*l+'rd'
            sLL = sL[:-1]+'c'
        else:
            fLL = fL[:-1]+'r'*l+'cd'
            sLL = sL
        nspdrc = ((fLL, sLL, *drcL[2:]), (fRR, *drcR[1:]))
    if not verify_drc(nspdrc, 'C'):
        print('Invalid nonspecial drc\n original: \n%s\n new:\n%s\n'
              % (str_dgms(drc), str_dgms(nspdrc)))
    return nspdrc



#Map_cdrs = { 'c':'d', 'd':'c','r':'s', 's':'r'}
TRcdrs = str.maketrans('cdrs','dcsr')

# Very New version
def twist_M_nonspecial(drc):
    """
    send a the special diagram to non-special diagram
    special diagram means `switch' the left diagram longest column
    to right diagram
    We only implement fL \neq fR case (the general case)
    We will not check whether drc is a valide drc
    """
    drcL, drcR = drc
    # first column of drcL and first, second column of drcR
    fL, fR = getz(drcL, 0, ''), getz(drcR, 0, '') # getz(drcR, 1, '')
    assert(not len(fL) == len(fR))
    fLL = fR.translate(TRcdrs)
    fRR = fL.translate(TRcdrs)
    nspdrc = ((fLL, *drcL[1:]), (fRR, *drcR[1:]))
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
    if (len(sL)>1):
        print(fL,sL)
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


def _fill_ds_D(drc):
    drcL, drcR = drc
    ndrcR = [] #tuple('*'*len(col) for col in drcR)
    ndrcL = []
    for colL, colR in zip_longest(drcL,drcR, fillvalue=''):
        cL = _count_ds(colL)
        cR = len(colR)
        if cR > cL:
            print('Error')
            print(concat_strblocks(str_dgms(drc)))
            assert(cR<=cL)
        ndrcL.append('*'*cR+'s'*(cL-cR)+colL[cL:])
        ndrcR.append('*'*cR)
    res = (tuple(ndrcL), tuple(ndrcR))
    assert(verify_drc(res,'D'))
    return reg_drc(res)

def lift_drc_C_D(drc, a):
    drcL, drcR = drc
    fL, sL, fR = getz(drcL, 0, ''), getz(drcL, 1,''), getz(drcR, 0, '')
    nfL, nsL, nfR = len(fL), len(sL), len(fR)
    assert(nfL <= a)
    if nfL <= nfR+1:
        # drc has special shape
        # This could be: r_1(dpart)=r_2(dpart), i.e. (1,2) is not a primitive pair
        #               (1,2) is a primtive pair but the diagram has special shape
        nR = nfR
    else:
        # drc has non-special shape
        nR = nfL -2
        assert(nR>=0)
        if nsL-nR>1:
            print('Error drc')
            print(str_dgms(drc))

    # bdrcL, bdrcR = _add_bullet_D((fLL, *drcL[1:]), drcR)
    # print(fL)
    ldrcD2 = gen_drc_D_two(fL[nR:], sL[nR:], a-nR)
    RES = []
    for ffL, nsL, ntL,  twist in ldrcD2:
        # ffL: very first column
        # nsL: new second column
        # sL: old second colunn
        drcLL = ('*'*nR + ffL, fL[:nR]+nsL, sL[:nR]+ntL, *drcL[2:])
        ndrc = _fill_ds_D((drcLL,drcR))
        if not verify_drc(ndrc, 'D'):
            print('Invalid drc')
            print(concat_strblocks('original: ', str_dgms(drc),
                                   '  a = %d'%a, '  --> new:', str_dgms(ndrc)))
        RES.append((ndrc, twist))
    ## There is no collision of the newly generated drcs
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




'''
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
'''

## New version


'''
def gen_drc_B_two_new(L, R,  n):
    """
    agruments: last row of left diagram and right diagram
    returns the tail of
    first column of L, second column of L, first column of R, second column of R, tiwst
    """
    #print('fL, fR, n: %s, %s, %d'%(fL,fR,n))
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
        elif (L[0],R[0]) == ('s','d'):
            ERES = gen_fR_B('*','*',L,R,n-1)
            ERES.append((('c',*L[1:]), ('r'*(n-1)+'d'+'a',*R),(1, 1)))
            ERES.append((('c',*L[1:]), ('r'*n+'a', *R),(1,-1)))
        elif (L[0],R[0]) == ('c','r'):
            ERES = gen_fR_B('c','s',L,R,n-1)
        elif (L[0],R[0]) == ('c','d'):
            ERES = gen_fR_B('c','s',L,R,n-1)
            ERES.append((('c',*L[1:]), ('r'*n+'b', *R),(1, -1)))
            ERES.append((L, ('r'*(n-1)+'d'+'b',*R),(1, 1)))
    return ERES
'''

def gen_fR_B(tL,aR, tR, n):
    """
    Generate columns of the right diagram
    for O(2n+1)
    With "hat"
    tL   ,   aR   tR
              s
              r
              d
             a/b
    """
    LfR = []
    LfR.extend([('s'*i+'r'*(n-i)+'a', (1, -1)) for i in range(0, n+1)])
    LfR.extend([('s'*i+'r'*(n-i-1)+'d'+'a', (1, 1)) for i in range(0, n)])
    LfR.extend([('s'*i+'r'*(n-i)+'b', (1, -1)) for i in range(0, n+1)])
    LfR.extend([('s'*i+'r'*(n-i-1)+'d'+'b', (1, 1)) for i in range(0, n)])
    ERES = []
    for  fR, twist in LfR:
        ERES.append((tL, aR+fR, tR, twist))
    return ERES

def gen_drc_B_two_new(tL, tR,  n):
    """
    agruments: last row of left diagram and right diagram
    returns the tail of
    first column of L, second column of L, first column of R, second column of R, tiwst
    """
    #print('fL, fR, n: %s, %s, %d'%(fL,fR,n))
    ERES = []
    if tL == '' and tR == '':
        ERES = gen_fR_B('', '','', n)
    elif tR == '':
        if tL =='s':
            ERES = gen_fR_B('*','*','',n-1)
            ERES.append(('c', 'r'*n+'a', '', (1,-1)))
            ERES.append(('c', 'r'*(n-1)+'d'+'a', '', (1,1)))
        elif tL =='c':
            ERES = gen_fR_B('c','s','',n-1)
            ERES.append(('c', 'r'*(n-1)+'d'+'b','' , (1,1)))
            ERES.append(('c', 'r'*n+'b', '', (1,-1)))
    elif tL == '':
        if tR =='r':
            ERES = gen_fR_B('','s','r',n-1)
            ERES.append(('', 'r'*n+'a','d', (1,-1)))
            ERES.append(('', 'r'*(n-1)+'d'+'a','d', (1,1)))
        elif tR =='d':
            ERES = gen_fR_B('','s','d',n-1)
            ERES.append(('', 'r'*(n-1)+'d'+'b','d', (1,1)))
            ERES.append(('', 'r'*n+'b','d', (1,-1)))
    else:
        if (tL,tR) == ('*','*'):
            ERES = gen_fR_B('*','*','s',n-1)
        elif (tL,tR) == ('s','r'):
            ERES = gen_fR_B('*','*','r',n-1)
        elif (tL,tR) == ('s','d'):
            ERES = gen_fR_B('*','*','d',n-1)
            ERES.append(('c', 'r'*n+'a','d',(1,-1)))
            ERES.append(('c', 'r'*(n-1)+'d'+'a','d',(1, 1)))
        elif (tL,tR) == ('c','r'):
            ERES = gen_fR_B('c','s','r',n-1)
        elif (tL,tR) == ('c','d'):
            ERES = gen_fR_B('c','s','d',n-1)
            ERES.append(('c','r'*n+'b','d',(1, -1)))
            ERES.append(('c','r'*(n-1)+'d'+'b','d',(1, 1)))
    return ERES


## New version
def lift_drc_M_B(drc, a):
    """
    a: the length of column attached to the right diagram
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
    assert(nR <= a)

    t = max(max(nL,nR)-1,0)

    #tdrcL = tuple(col[:t] for col in drcL)
    #tdrcR = ('*'*t,*(col[:t] for col in drcR))

    tL, tR = fL[t:], fR[t:]

    RES = []
    eRES = []
    ldrcD2 = gen_drc_B_two_new(tL, tR, a-t)
    for nL, nR, nsR, twist in ldrcD2:
        # print('%s,%s,%s'%(ffL,ffR,ssR))
        # drcLL = tuple(col+getz(LL, i, '')  for i, col in enumerate(tdrcL))
        # drcRR = tuple(col+getz(RR, i, '')  for i, col in enumerate(tdrcR))
        drcLL = (fL[:t]+nL, *drcL[1:])
        drcRR = ('*'*t+nR, fR[:t]+nsR, *drcR[1:])
        ndrc = _fill_ds_B((drcLL,drcRR))
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


def reg_purelyeven_dpart(dpart, rtype):
    '''
    regularize purelyeven dual partition:
        stripe away zeros
        test where the partition satisfies the parity condition.
    '''
    # dpart is a decreasing sequence.
    dpart = (*(a for a in dpart if a>0 ),)
    assert all(a-dpart[i+1]>=0 for i,a in enumerate(dpart[:-1]))
    assert rtype in ('B','C','CS','D','DS','M'), f"Type must be in ('B','C','CS','D','DS','M'), {rtype}"

    if rtype in ('D','DS','C','CS'):
        # All parts are odd
        assert all(a%2 == 1 for a in dpart), f'All parts must be odd: {dpart} for {rtype}'
    else:  # rtype in ('B','M')
        # All parts are even
        assert all(a%2 == 0 for a in dpart), f'All parts must be even: {dpart} for {rtype}'

    if rtype in ('D','M','B','DS'):
        assert sum(dpart)%2 == 0, f'total size must be '
    else: # rtype in ('C','CS')
        assert(sum(dpart)%2 == 1)

    return dpart




def test_dpart2drcLS(dpart, rtype='D', report=False, reportann=False, reportpack = False, test=True):
    """
    dpart: dual partition

    DRCS : drc generated by definition
    GDRCS: drc generated by theta lifting
    ALS : LS generated by theta
    GLS : LS generated by macthing algorithm of drc and LS.
    """
    Ltypes = LtypesLST[rtype]

    dpart = reg_purelyeven_dpart(dpart,rtype)

    # dpart always have assume to have even number of parts
    # in type B D.
    # So we starts with So
    if rtype == 'D' and len(dpart)>0 and dpart[-1]!=0:
        dpart = (*dpart, 0)

    # We start the induction from Mp(0)
    if rtype == 'B':
        if len(dpart) %2 == 0:
            dpart = (*dpart, 0,0)
        else:
            dpart = (*dpart, 0)

    lDRCLS = [dict()]
    lLSDRC = [dict()]
    for i in range(len(dpart)-1, -1, -1):
        DRCLS = lDRCLS[0]
        LSDRC = lLSDRC[0]
        # 'pdpart' means present dual partition.
        # 'prtype' means present root system type.
        pdpart = dpart[i:]
        prtype = Ltypes[i % 2]


        print('Group type %s, dual partition:  %s' % (prtype, pdpart))

        nDRCLS, nLSDRC = lift_DRCLS(DRCLS, LSDRC, pdpart, prtype,
                                    report=report, reportann=reportann)
        lDRCLS.insert(0, nDRCLS)
        lLSDRC.insert(0, nLSDRC)

        # print(DRCLS)
        Adrcs = dpart2drc(pdpart, prtype, printdig=False, report=report)
        ppart = dualBVW(pdpart,prtype,partrc='c')
        print(f"The dBV(dO): {prtype}, {ppart}")
        ALS = part2LS(ppart, prtype, report=report)

        Gdrcs = nDRCLS.keys()
        LLS = set(nLSDRC.keys())
        if prtype == 'D' and sum(pdpart)!=0:
            #LLS = det_all_LS(LLS, rtype=prtype)
            DetLS = det_only_LS(LLS,rtype=prtype)
            if test:
                assert(DetLS.isdisjoint(LLS))
            LLS = DetLS.union(LLS)
        elif prtype == 'B':
            DetLS = det_only_LS(LLS,rtype=prtype)
            if test:
                assert(DetLS.isdisjoint(LLS))
            LLS = DetLS.union(LLS)
            #LLS = det_all_LS(LLS, rtype=prtype)
            #LLS = asign_all_LS(LLS, rtype=prtype)
        # report some basic facts

        if prtype == 'B':
            print('#PBPext:\t%d, #PBPext*2:\t%d, \t#ALS\t%s' %(len(Adrcs)*2, len(Adrcs)*4, len(ALS)))
            print('#GPBPext:\t%d, #GPBPext*2:\t%d, \t#GLS\t%s' % (len(Gdrcs),len(Gdrcs)*2, len(LLS)))
        elif prtype == 'D':
            print('#PBP:\t%d, #PBP*2:\t%d, \t#ALS\t%s' %(len(Adrcs), len(Adrcs)*2, len(ALS)))
            print('#GPBP:\t%d, #GPBP*2:\t%d, \t#GLS\t%s' % (len(Gdrcs),len(Gdrcs)*2, len(LLS)))
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

        if test:
            DLS, _ = compare_LS(ALS, LLS)
            # print(ALS)
            # print(DRCLS)
            #print_DRCLS(DRCLS, prtype)
            if len(DLS) > 0:
                # print(ALS)
                # print(LLS)
                print('Missing %d LS:' % len(DLS))
                for LS in DLS:
                    print(str_LS(LS))
                    #if LSDIC and prtype == 'B':
                    #    sLS = str_LS(LS),
                    print('~~~~~~~~~~~~~~~')
                return (lDRCLS, lLSDRC)
    return (lDRCLS, lLSDRC)



def lift_DRCLS(DRCLS, LSDRC, dpart, rtype='C', ltype='l', report=False, reportann=False):
    """
    rtype is the target root system type.
    # ltype is the lifting type:
    #             l: normal lift,
    #             L: gneralized lift,
    #             n: size of orthogonal group if rtype = B/D
    """
    nDRCLS, nLSDRC = dict(), dict()
    # Get the first and second row of the dual partition.
    fRow, sRow = getz(dpart,0, 0), getz(dpart,1,0)

    """
    terms in LSDRC:
    key: LS
    value: list of tuple (drc, LS, descent of drc, descent of LS, det_twist)
    """

    if rtype == 'C':
        # Sp(2n), n is the rank
        n = (sum(dpart)-1)//2
        # The length of column to attach on the left of drcR
        crow = (fRow-1)//2
        if sRow ==0:
            l = (fRow - 1 )//2
        else:
            l = (fRow - sRow -2)//2
        # sRow == 0:
        #     # There is a unique pbp attached to the trivial local system
        #     tdrc = (('',), ('s'*l,))
        #     tLS = frozenset([tuple((l,l))])
        #     DRCLS[tdrc] = tLS
        #     LSDRC[tLS] = ((l,l), [(tdrc, tLS, None, 0, None)])
        if fRow > sRow and sRow > 0:
            # (1,2) is a primitive pair
            for drc, LS in DRCLS.items():
                #signature of drc
                pO, nO = gp_form_D(drc)
                #signature of LS
                ppO, nnO = sign_LS(LS)
                assert((pO, nO) == (ppO, nnO))
                # Lift trivial twist, oeps = 0
                oeps = 0
                ndrc = lift_drc_D_C(drc, crow)
                assert(descent_drc(ndrc,'C') == drc )
                nLS = lift_D_C(LS, n)
                updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, ndrc, nLS, reportann=reportann)
                # Lift det twist, oeps = 1
                oeps = 1
                dLS = char_twist_D(LS, (-1, -1)) # det twist of the original LS
                ndLS = lift_D_C(dLS, n) # lift of the LS*det
                nsdrc = twist_sp2nsp(ndrc, 'C') # non-special shape drc
                updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, dLS, nsdrc, ndLS, reportann=reportann)
                if report:
                    print(concat_strblocks(str_dgms(drc),  '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
                    print(concat_strblocks(str_dgms(drc), '=d==>', str_dgms(nddrc)))
                    print(concat_strblocks(str_LS(dLS), '==d==>', str_LS(ndLS)))
        else:
            # (1,2) is not a primitive pair
            for drc, LS in DRCLS.items():
                # signature of drc
                pO, nO = gp_form_D(drc)
                # signature of LS
                pLS, nLS = sign_LS(LS)
                assert((pO, nO) == (pLS, nLS))
                # Lift trivial twist
                ndrc = lift_drc_D_C(drc,crow)
                if ndrc is not None:
                    nLS = lift_D_C(LS, n)
                    # only lift the trivial twist, oeps = 0
                    oeps = 0
                    updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, ndrc, nLS, reportann=reportann)
                    #RES[ndrc] = nLS
                    if report:
                        print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                        print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
    elif rtype == 'D':
        if sum(dpart) == 0:
            # Zero diagram, the initial case
            print(dpart)
            zdrc = (('',), ('',))
            zLS = frozenset([tuple()])
            updatepeDRCLS(nDRCLS, nLSDRC, zdrc, 0, zLS, zdrc, zLS, reportann=reportann)
        else:
            crow = (fRow+1)//2
            for drc, LS in DRCLS.items():
                # Some ckeck
                nSp = gp_form_C(drc)
                nnSp = sign_LS(LS)[0]
                #print(LS)
                #print(nSp, nnSp)
                assert(nSp == nnSp)
                NDRCS = lift_drc_C_D(drc, crow)
                for ndrc, twist in NDRCS:
                    dndrc = descent_drc(ndrc,'D')
                    if dndrc != drc:
                        print(concat_strblocks(str_dgms(ndrc), '=dec=>',str_dgms(dndrc),' origin:', str_dgms(drc)))
                    pO, nO = gp_form_D(ndrc)
                    nLS = lift_C_D(LS, pO, nO)
                    assert(nLS)
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
    elif rtype == 'M':
        """
        we work on extended drc diagram!
        This initial case is Mp(0)
        """
        # Mp(2nSp)
        # The length of column to attach on the left of drcL
        nSp = sum(dpart)//2
        crow = fRow//2

        if fRow ==0:
            #print(dpart)
            zdrc = (('',), ('',))
            zLS = frozenset([tuple()])
            updatepeDRCLS(nDRCLS, nLSDRC, zdrc, 0, zLS, zdrc, zLS, reportann=reportann)
        else: #first Row >= second Row:
            for drc, LS in DRCLS.items():
                drcL, drcR = drc
                if len(drcR) == 0:
                    drcR = ('',)
                    drc = (drcL, drcR)
                pO, nO = gp_form_B_ext(drc)
                pLS, nLS = sign_LS(LS)
                assert((pO, nO) == (pLS, nLS))
                # Lift trivial twist, oeps = 0
                oeps = 0
                ndrc = lift_extdrc_B_M(drc, crow)
                if ndrc is None:
                    #print('drc has no lift', drc)
                    continue
                nLS = lift_B_M(LS, nSp)
                updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, ndrc, nLS, reportann=reportann)
                # Lift the determinant twist
                # Lift the determinant twist, oeps = 1
                if fRow > sRow :
                    # (1,2) is a primitive pair
                    # Also lift the determinant twist.
                    oeps = 1
                    nddrc = twist_M_nonspecial(ndrc)
                    if nddrc is None:
                        print('ndrc has no twist (should not happen)', ndrc)
                        continue
                    dLS = char_twist_B(LS, (-1, -1))
                    ndLS = lift_B_M(dLS, nSp)
                    updatepeDRCLS(nDRCLS, nLSDRC, drc, oeps, LS, nddrc, ndLS, reportann=reportann)
                if report:
                    print(concat_strblocks(str_dgms(drc), '====>', str_dgms(ndrc)))
                    print(concat_strblocks(str_LS(LS), '=====>', str_LS(nLS)))
                    if fRow >sRow:
                        print(concat_strblocks(str_dgms(drc), '=d==>', str_dgms(nddrc)))
                        print(concat_strblocks(str_LS(dLS), '==d==>', str_LS(ndLS)))
    elif rtype == 'B':
        # if sRow == 0:
        #     # This is the initial case
        #     zdrc = (('',), ('',))
        #     DRCLS[zdrc] = frozenset([tuple()])
        #

        # The initial case is Mp(0)

        for drc, LS in DRCLS.items():
            nSp = gp_form_M(drc)
            nnSp = sign_LS(LS)[0]
            assert(nSp == nnSp)
            aL = getz(dpart,0)//2
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
                else:  # twist = (1,-1)
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
    return nDRCLS, nLSDRC

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

def updatepeDRCLS(DRCLS, LSDRC, odrc, oeps, oLS, drc, LS, reportann = False, reportLSpack = False):
    """
    Update dictionaries DRC->LS and LS->DRC.
    o = old, oeps, the det^epsilon twist.
    """
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
                # keyLS = frozenset([str_LS(nLS), str_LS(ndLS)])
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
