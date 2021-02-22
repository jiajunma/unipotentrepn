import itertools
from copy import copy, deepcopy
from multiset import FrozenMultiset as frozenset

from .tool import *

def getz(C,idx,default=None):
    """
    Get the element in C[idx]
    if idx is out of the range, return the default value.
    """
    try:
        return C[idx]
    except IndexError:
        return default

def list_2list_BC(C):
    """
    From special orbit to special representations of the Weyl group
    """
    C = [x for x in C if x!=0]
    ll = len(C)
    a = int(ll/2)
    if ll %2 == 0:
        C=C+[0]
        ll = ll+1
    C=sorted(C)
    #print(C,a)
    tauL = [int((C[2*i-1]+1)/2) for i in range(1,a+1)]
    tauR = [int(C[2*i]/2) for i in range(a+1)]
    return (tauL,tauR)
    
        
def S_Wrepns_B(tau):
    """
    Type B
    Special representation ot set of representation in 
    coherent continuations. 
    the correct formula is 
    (c_2i+1,c_{2i})<--> (c_{2i},c_{2i+1})
    
    We assume tauL and tauR are arranged in incresing order
    """
    tauL,tauR = tau
    # tauL and tauR must have length a and a+1 respectively
    a = len(tauL)
    assert(a +1 == len(tauR))
    tauL,tauR = sorted(tauL), sorted(tauR) 
    cidxs = [ i for i in range(a) if tauL[i]!=tauR[i]]
    Atau = []
    for k in range(len(cidxs)+1):
        for oidxs in itertools.combinations(cidxs,k):
            tauLL= [tauR[i] if i in oidxs else tauL[i] for i in range(a)]
            tauRR= [tauL[i] if i in oidxs else tauR[i] for i in range(a)]+[tauR[a]]
            Atau.append((tauLL,tauRR))
    return Atau
        
def S_Wrepns_C(tau):
    """
    Type C
    Special representation ot set of representation in 
    coherent continuations. 
    the correct formula is 
    (c_2i,c_{2i-1})<--> (c_{2i-1}-1,c_2i+1)
    """
    tauL,tauR = tau
    # tauL and tauR must have length a and a+1 respectively
    a = len(tauL)
    assert(a +1 == len(tauR))
    tauL,tauR = sorted(tauL), sorted(tauR) 
    cidxs = [ i for i in range(a) if tauL[i]!=tauR[i+1]+1]
    Atau = []
    for k in range(len(cidxs)+1):
        for oidxs in itertools.combinations(cidxs,k):
            tauLL= [tauR[i+1]+1 if i in oidxs else tauL[i] for i in range(a)]
            tauRR= [tauR[0]]+[tauL[i]-1 if i in oidxs else tauR[i+1] for i in range(a)]
            Atau.append((tauLL,tauRR))
    return Atau

def column2row(C):
    C=sorted(C)
    l= len(C)
    if l>0:
        c = C[0]
        return column2row([x-c for x in C[1:]])+[l for i in range(c)]
    else:
        return []

#diag_trans=column2row    

def part_trans(part):
    part=sorted([x for x in part if x>0])
    if len(part) == 0:
        return []
    else:
        tpart = []
        for i in range(part[-1]):
            ri  = len([x for x in part if x>i])
            tpart.append(ri)
        return sorted(tpart, reverse=True)

    
def _simp_dec_seq(P):
    """
    return the simplify the sequence 
    [c_1, ..., c_k]
    strip zeros in the tail, 
    If the sequence is not decresing 
    return None # Note that [] != None
    """
    NP = []
    for i in range(len(P)):
        if P[i]< getz(P,i+1,0):
            return None
        elif P[i]>0:
            NP.append(P[i])
    return NP
    
def _simp_W_repn(tau):
    tauL, tauR = tau
    simpL = _simp_dec_seq(tauL)
    if simpL is None: 
        return None
    else:
        simpR = _simp_dec_seq(tauR)
        if simpR is None: 
            return None
        else:
            return (simpL,simpR)
    

def _fill_r_dgms_C(tau):
    """
    Here the Young diagram is parameterized by columns 
    ([tauL_0, ...], [tauR_0, ...])
    Here r'=s are the r's in the right diagram
    """
    tau = _simp_W_repn(tau)
    #print("tau",tau)
    if tau is None: 
        return []
    else:
        tauL,tauR = tau
        rL, rR = len(tauL),len(tauR)
        #print("rL,rR: %d %d"%(rL,rR))
        S = []
        tauRR = [x-1 for x in tauR]
        tauLL = [x-1 for x in tauL]
        #print "tauLLRR", tauLL,tauRR
        if rR == rL + 1:
            SS =  _fill_r_dgms_C((tauLL,tauRR))
            for drcL,drcR in SS:
                drcL = ['*'+x for x in drcL]+['*']*(rL-len(drcL))
                drcR = ['*'+x for x in drcR]+['*']*(rR-len(drcR))
                #if len(drcR) == len(tauR):
                #    drcR[-1] = 's'+drcR[-1][1:]
                #else:
                #    assert(len(drcR) +1 == len(tauR))
                #    drcR.append('s')
                drcR[-1] = 's'+drcR[-1][1:]
                S.append((drcL,drcR))
            return S
        elif rL== rR+1:
            SS =  _fill_r_dgms_C((tauLL,tauRR))
            for drcL,drcR in SS:
                drcL = ['*'+x for x in drcL]+['*']*(rL-len(drcL))
                drcR = ['*'+x for x in drcR]+['*']*(rR-len(drcR))
                #if len(drcL) == len(tauL):
                #    drcL[-1] = 'r'+drcL[-1][1:]
                #else:
                #    assert(len(drcL) +1 == len(tauL))
                #    drcL.append('r')
                drcL[-1] = 'r'+drcL[-1][1:]
                S.append((drcL,drcR))
            return S
        elif rL==rR:
            if rL==0 and rR==0:
                return [([],[])]
            else:
                SS =  _fill_r_dgms_C((tauLL,tauRR))
                for drcL,drcR in SS:
                    drcL = ['*'+x for x in drcL]+['*' for i in range(rL-len(drcL))]
                    drcR = ['*'+x for x in drcR]+['*' for i in range(rR-len(drcR))]
                    S.append((copy(drcL),copy(drcR)))
                    if (len(drcL[-1])<2 or (drcL[-1][1]!='*')) \
                        and (len(drcR[-1])<2 or (drcR[-1][1]!='*')):
                        drcL[-1]='r'+drcL[-1][1:]
                        drcR[-1]='s'+drcR[-1][1:]
                        S.append((drcL,drcR))
                return S
        else:
            return []
        
def _fill_c_dgms_C(tau):
    """
    fill c'=d in the longest column
    here c' = d, r' = s
    """
    tau = _simp_W_repn(tau)
    if tau is None: 
        return []
    tauL,tauR = tau
    rL = len(tauL)
    S =[]
    # Put totally k "c"'s in the left diagram
    # k = 0,..., rL
    frow_lst = frow_col_list(tauL)
    #for k in range(rL+1):
        # cidx = the column index to put "c"
        #for cidx in itertools.combinations(range(rL),k):
    #    for cidx in yield_cidx(frow_lst,k):
    for cidx in yield_cindex(frow_lst):
            tauLL = copy(tauL)
            for i in cidx:
                tauLL[i] -=1
            SS = _fill_r_dgms_C((tauLL,tauR))
            for drcL,drcR in SS:
                drcL = drcL+['']*(rL-len(drcL))
                for i in cidx:
                    drcL[i] = getz(drcL,i,'')+'c'
                S.append((drcL,drcR))
    return S


def frow_col_list(part):
   """
   This function return a list of list records the group of final rows
   """ 
   lidx = {}
   for i,l in enumerate(part):
       lidx[l] = lidx.get(l,[])+[i]
   return list(lidx.values())    

def yield_cindex(lidxs):
        """
        lidxs is a list of list of  indexes
        [[a_11, ..., a_1k],[a_21,..., a_2l], ..., [...]]
        the function yield an iterator return 
        a list of indexes [i_1, ..., i_k]
        where consists last k_i elements in the i-th list
        """
        N = 0
        nlst = len(lidxs) # Length of the list 
        llens = [len(lt) for lt in lidxs]
        cidx = [0 for lt in lidxs]
        # yields the first index
        idx = [x for j, lt in enumerate(lidxs) for x in lt]
        yield idx
        while True:
            for i in reversed(range(nlst)):
               if cidx[i] != llens[i]:
                   break
            else:
                return
            cidx[i] += 1
            cidx = cidx[:i+1]+[0]*(nlst-i-1)
            idx = [x for j, lt in enumerate(lidxs) for x in lt[cidx[j]:llens[j]] ]
            #print('#%d: %s'%(N,idx))
            yield idx

def yield_cidx(lidxs,k):
        """
        lidxs is a list of list of  indexes
        [[a_11, ..., a_1k],[a_21,..., a_2l], ..., [...]]
        the function yield an iterator return 
        a list of indexes [i_1, ..., i_k]
        where consists last k_i elements in the i-th list
        """
        N = 0
        nlst = len(lidxs) # Length of the list 
        if nlst ==0 :
            if k==0 :
                yield []
            return 
        llens = [len(lt) for lt in lidxs]
        cidx = [len(lt) for lt in lidxs]
        kz = 0
        for i in range(nlst):
            rr = min((k-kz), llens[i])
            if rr>0: 
                cidx[i] -= rr
                kz += rr 
            if kz == k:
                break
        else:
            return
        # yields the first index
        idx = [x for j, lt in enumerate(lidxs) for x in lt[cidx[j]:llens[j]]]
        #print('#%d: %s'%(N,idx))
        #N=N+1
        yield idx
        
        while True:
            for i in reversed(range(nlst)):
               if cidx[i] != llens[i]:
                   break
            else:
                return
            cidx[i] += 1
            cidx = cidx[:i+1]+llens[i+1:]
            kz = sum(llens[j]-cidx[j] for j in range(i+1))
            for j in range(i+1, nlst):
                rr = min((k-kz), llens[j])
                if rr>0: 
                    cidx[j] -= rr
                    kz += rr 
                if kz == k:
                    break
            else:
                cidx[i:] = llens[i:]
                continue 
            idx = [x for j, lt in enumerate(lidxs) for x in lt[cidx[j]:llens[j]] ]
            #print('#%d: %s'%(N,idx))
            N=N+1
            yield idx
                
def _fill_cp_dgms_C(tau):
    """
    fill c' in the longest column
    here c' = d, r' = s
    """
    tau = _simp_W_repn(tau)
    if tau is None: 
        return []
    tauL,tauR = tau
    rL = len(tauL)
    S =[]
    # Put totally k "d"'s in the left diagram
    # k = 0,..., rL
    frow_lst = frow_col_list(tauL)
    #for k in range(rL+1):
        # cidx = the column index to put "d"
        #for cidx in itertools.combinations(range(rL),k):
    #    for cidx in yield_cidx(frow_lst,k):
    for cidx in yield_cindex(frow_lst):
            tauLL = copy(tauL)
            for i in cidx:
                tauLL[i] -=1
            SS = _fill_c_dgms_C((tauLL,tauR))
            for drcL,drcR in SS:
                drcL = drcL+['']*(rL-len(drcL))
                for i in cidx:
                    drcL[i] +='d'
                S.append((drcL,drcR))
    return S
                    
                    
                
            
    
def drc_dgms_C(tau):
    """
    Compute all dot-r-c diagrams for type C for 
    a Weyl group representation.
    
    Note that trivial representation corresponds to a single row
              sign    representation corresponds to a single column
    In this construction, we assume 
          tau = ([tauL_0>=tauL_1>= ...],[tauR_0>tauR_1>...])
    """
    tauL,tauR=tau
    tauL = sorted([x for x in tauL if x!=0],reverse=True)
    tauR = sorted([x for x in tauR if x!=0],reverse=True)
    tau =(tauL,tauR)
    return _fill_cp_dgms_C(tau)


def str_dgms_C(drc):
    """
    Format of drc:
    drc = (drcL,drcR)
    drcL and drcR are string lists
    drcL = [cl_1, ..., cl_k], 
        each cl_i represents
        the symbol of a column
    """
    drcL,drcR = drc
    cL,cR = len(drcL),len(drcR)
    r = max(len(getz(drcL,0,'')),len(getz(drcR,0,'')))
    S = []
    for i in range(r):
        ll = [getz(cl,i,' ') for cl in drcL]
        rr = [getz(cr,i,' ') for cr in drcR]
        S.append(''.join(ll)+'|'+''.join(rr))
    s = '\n'.join(S)
    s = s.replace('*','.')
    s = s.replace('s','r')
    return s   

def str_dgms_B(drc):
    """
    Format of drc for type C:
    drc = (drcL,drcR)
    drcL and drcR are string lists
    drcL = [r_1, ..., r_k], 
        each r_i represents
        the symbol of a row 
    The result of drc is from the type C computation 
    """
    ts = str.maketrans('rscd*','ccrs.')
    # switch the left and right diagram
    drcR, drcL = drc
    sR = [row.translate(ts) for row in drcR] 
    sL = [row.translate(ts) for row in drcL]
    cR = max([len(row) for row in sR]+[0])
    cL = max([len(row) for row in sL]+[0])
    rows = max([len(sR), len(sL)])
    S = []
    for i in range(rows):
        rR = getz(sR,i,'')
        rL = getz(sL,i,'')
        row = rL+' '*(cL - len(rL))+'|' \
            + rR +' '*(cR - len(rR))
        S.append(row)
    return '\n'.join(S) 

def all_drc_dgms_C(tauS):
    S = [x
         for tau in tauS
         for x in drc_dgms_C(tau)]
    return S


def all_drc_dgms_B(tauS):
    S = [x
         for tau in tauS
         for x in drc_dgms_B(tau)]
    return S

"""
We use the counting program for type C to deduce the counting for type B

If tau = (tauL,tauR) is the representation for type B, then tau' = (tauR^t, tauL^t) 
is the corresponding representation for type C
 Type B  <---> Type C
      r  <--->  c
      r' <--->  c'
      c  <--->  r
"""

def part2SW_B(part):
    """
    From special orbit to special representations of the Weyl group of type B
    """
    
    part = [x for x in part if x!=0]
    a, res = divmod(len(part),2)
    if res == 0:
        part=part+[0]
    part.sort()
    # Last columne must be odd
    assert(part[-1]%2 == 1)
    # C_2i and C_{2i+1} must have same parity 
    assert(not any([(part[2*i]-part[2*i+1])%2 for i in range(a)]))

    """
    e = 0,1
    C_2i = 2 c_2i +e,         ==> c_2i = (C_2i-e)/2 =  C_2i//2
    C_{2i+1} = 2 c_{2i+1} -e  ==> c_{2i+1} = (C_{2i+1}+e)/2 = (C_{2i+1}+1)//2
    """
    tauL, tauR = [], []
    for i,C in enumerate(part):
        if i %2 == 0:
            tauR.append(C//2)
        else:
            tauL.append((C+1)//2)
    return (tauL,tauR)

    
    
def drc_dgms_B(tau):
    """
    Compute all dot-r-c diagrams for type C for 
    a Weyl group representation.
    
    Note that trivial representation corresponds to a single row
              sign    representation corresponds to a single column
    In this construction, we assume 
          tau = ([tauL_0>=tauL_1>= ...],[tauR_0>tauR_1>...])
    """
    tauL,tauR=tau
    ttauL = part_trans(tauR)
    ttauR = part_trans(tauL)
    S = _fill_cp_dgms_C((ttauL,ttauR))
    #SS = []
    #for sL,sR in S:
    #j    SS.append(diag_tran(s))
    return S 

def get_drc_diag_C(partition):
    """
    print the dcr_diag attached to Nilpotent orbit of type C
    partition: = [c_1>=c_2... >=c_k] is the list of column lengths of a type C nilpotent orbits. 
    """
    tau = list_2list_BC(partition)
    Stau = S_Wrepns_C(tau)
    Adrc =  all_drc_dgms_C(Stau)
    return Adrc
    
def print_drc_diag_C(partition, report=True, printdig=False, getlist=False,print_Wrepn=False):
    """
    print the dcr_diag attached to Nilpotent orbit of type C
    partition: = [c_1>=c_2... >=c_k] is the list of column lengths of 
                  a type C nilpotent orbits. 
    """
    tau = list_2list_BC(partition)
    Stau = S_Wrepns_C(tau)
    if report:
        print("Type C partition: %s"%partition)
    if print_Wrepn:
        print("List of relevent W_n representations")
        print(Stau)
    #print(tau)
    Adrc =  all_drc_dgms_C(Stau)
    if report:
        print("Number of drc diagrams: %d"%len(Adrc))
    if printdig:
        for drc in Adrc:
            print("%s"%str_dgms_C(drc))
            print("dual form is SO(%d,%d)\n"%dual_form_C(drc))
    return Adrc


def print_drc_diag_B(partition, printdig=False, splitform=False, getlist=False,
                     print_Wrepn=False):
    """
    print the dcr_diag attached to Nilpotent orbit of type B
    partition: = [c_2a>=c_2a-1... >=c_0] 
                 is the list of column lengths of a type B nilpotent orbits. 
    """
    tau = part2SW_B(partition)
    Stau = S_Wrepns_B(tau)
    print("Type B partition: %s"%partition)
    if print_Wrepn:
        print("List of relevent W_n representations")
        print(Stau)
    #print(tau)
    Adrc =  all_drc_dgms_B(Stau)
    Sdrc = [] 
    Rdrc = []
    if splitform:
        for drcL,drcR in Adrc:
            Cc = sum(col.count('c') for col in drcL)
            Cd = sum(col.count('d') for col in drcL)
            if Cc == Cd:
                Sdrc.append((drcL,drcR))
        Rdrc = Sdrc
        print("The total number of drc diagrams for the split form is: %d"%len(Rdrc))
        print("Unipotent repn. of the split orthogonal group is: %d"%(len(Rdrc)*2))
    else:
        Rdrc = Adrc
        print("The total number of drc diagrams: %d"%len(Rdrc))
        print("Unipotent repn. of all forms: %d"%(len(Rdrc)*4))
    #print(Adrc)
    if printdig:
        for drc in Rdrc:
            print("%s\n"%str_dgms_B(drc))
    if getlist:
        return Rdrc
    else:
        pass


"""
Code for counting local systems of type C
Data structure:
an irreducible local system is represented by a tuple [(p_1,n_1),(p_2,n_2),...(p_k,n_k)]
p_i: means there are |p_i| rows with length i and "+" at the end of the row,
    p_i>0 if the local system is trivial, 
    p_i <0 if the local system is the non-trivial one
    p_i =0, 0 is neither positive nor negative, and we don't have to assign local system. 
n_i: means there are |n_i| rows with length i and "-" at the end of the row
    n_i>0 means trivial system, n_i<0 means non-trivial one. 

For visialization:
    + : trivial system on + sign, 
    * : non-trivial system on + sign
    - : trivial system on - sign,
    = : non-trivial system on - sign. 

A local system is frozenset of irreducible local systems
Question: do I need the FrozenMultiset ?

Example:
    +-+-+
    -+-+-
    *=*
    -+-
    =*
    *
    =
   
   
Very important: There is a twist of characters when lifting local systems. 

Warnning: Don't flip the sign. 
"""

#def _sign_twist(t):
#    res = (1,0,-1,0)
#    return res[t%4]
    

def _sign_ILS(irr_s):
    p, n = 0, 0
    for i,(pp,nn) in enumerate(irr_s):
        dii, rii = divmod(i+1,2)
        p += abs(pp)*(dii+rii)+abs(nn)*dii
        n += abs(nn)*(dii+rii)+abs(pp)*dii
    return (p,n)

def _sign_ILS_firstcol(irr_s):
    p,n = 0,0
    #print(irr_s)
    for i, (pp,nn) in enumerate(irr_s):
        if i%2 == 0:
            p += abs(pp)
            n += abs(nn)
        else:
            p += abs(nn)
            n += abs(pp)
    return (p,n)
        
    
def leading_ILS(LS):
    nLS = []
    if len(LS) == 0:
        print(LS)
        return None
    for irr in LS:
        nt = (*((abs(n), 1 if n>=0 else -1) if i%2 ==0
                else (abs(p), 1 if p>=0 else -1)
                for i,(p,n) in enumerate(irr)), irr)
        nLS.append(nt)
    maxILS = max(nLS)    
    #print(maxILS)
    #print(maxILS[-1])
    #if len(sILS)>1:
    #    print('ILS is not unique!')
    #    print(str_LS(LS))
    #print(concat_strblocks(str_LS(LS), '--->', str_LS(set([maxILS[-1]]))))
    return maxILS[-1] 

    

def test_leading_ILS(LLS):
    l_LLS = []
    l_LLS = [leading_ILS(LS) for LS in LLS] 
    assert(None not in l_LLS)
    l_LLS = set(l_LLS)
    
    if len(LLS) > len(l_LLS):
        print('leading term size:', len(l_LLS))
        print('test failed')
        return False
    else:
        print('test passed')
        return True

def contragrident_LS(LS):
    nLS = [] 
    for irr_s in LS:
        nLS.append(tuple((nn,pp) for pp,nn in irr_s))
    return frozenset(nLS)
        
def _char_twist_C_t(irr_s,twist):
    """
    twist the irreducible local system by the strange sign charactor det^tp . det^tn twist = (tp,tn)
    """
    if twist == 1:
        return irr_s
    elif twist == -1:
        # only twist even length row,
        # If the row is length 2k, then det restricted to det^k on each factor. 
        irr_ss = [(-pp, -nn) if (i+1)%4==2 else (pp,nn) for i, (pp,nn) in enumerate(irr_s)]
        return tuple(irr_ss)
    else:
        assert(False)
        
def _char_twist_C(irr_s, ps, ns):
    """
    Here (ps,ns) is the signature of the other group = orthogonal group.
    """
    if (ps - ns) %4 == 2:
        return _char_twist_C_t(irr_s, -1)
    else:
        return irr_s

def char_twist_D(LS, twist):
    nLS = frozenset(_char_twist_D(irr_s, twist) for irr_s in LS)
    return nLS
    
def _char_twist_D(irr_s,twist):
    """
    twist type D irreducible local system 
    """
    tp, tn = twist
    irr_ss = []
    for i, (pp,nn) in enumerate(irr_s):
        hrl, rrl = divmod(i+1, 2)
        if rrl == 0:
            irr_ss.append((pp,nn))
        else:
            tpp = (tp**(hrl+1))*(tn**hrl)
            tnn = (tn**(hrl+1))*(tp**hrl)
            irr_ss.append((tpp*pp,tnn*nn))
    return tuple(irr_ss)

def _part_size(part):
    return sum(part)

def lift_irr_D_C(irr_s, n):
    """
    irr_s: an irreducible local system
    Lift type D irr_s to type C_n
    """
    ps, ns = _sign_ILS(irr_s)
    #Even orthogonal group
    assert((ps+ns)%2 == 0)
    # sign of first column
    fps,fns = _sign_ILS_firstcol(irr_s)
    # first column must always be even
    if (fps+fns) %2 ==0:
        addp, addn = n-ps-fns,n-ns-fps
        # The descent case
        if addp>=0 and addn>=0:
            irr_ss = ((addp,addn),)+irr_s
            # twist det^((ps-ns)/2), so twist "det" when ps-ns is 4k+2.
            irr_ss = _char_twist_C(irr_ss, ps, ns)
            return [irr_ss]
        #The generalized descent case
        elif (addp,addn) in [(-1,-1),(-2,0),(0,-2)]: 
            pp, nn = irr_s[0]
            ss = []
            #irr_ss = [(nn,pp) for pp,nn in irr_s[1:]]
            """
            +   lifts to -+, - lifts to +-
            +                -
            """
            if pp>0:
                irr_ss = ((0,0),(pp-1,nn))+irr_s[1:]
                irr_ss = _char_twist_C(irr_ss, ps,ns)
                ss.append(tuple(irr_ss))
            if nn>0:
                irr_ss = ((0,0),(pp,nn-1))+irr_s[1:]
                irr_ss = _char_twist_C(irr_ss, ps,ns)
                ss.append(tuple(irr_ss))
            return ss
        else:
            return []
    else:
        raise ValueError("type D to C parity error")
        


def lift_D_C(s, n, increase=False):
    """
    Lift from orthogonal group to Sp(2n)
    if increase = True, only return non-empty lift which size is increase than before. 
    """
    ss = []
    for irr_s in s:
        ss.extend(lift_irr_D_C(irr_s,n))
    ss = frozenset(ss)
    if increase:
        if len(ss)>=len(s):
            return ss
        else:
            if lift_D_C.print_LS_size_decrease and len(ss)>0:
                print("-----Decrease of size:----\n%s\n%s\n "%(str_LS(s),str_LS(ss)))
            return []
    else:
        return ss
lift_D_C.print_LS_size_decrease= False
    
def lift_C_D(s, ps,ns, increase=False):
    """
    (ps,ns) is the signature of orthogonal group
    if increase = True, only return non-empty lift which size is increase than before. 
    """
    ss = []
    for irr_s in s:
        ss.extend(lift_irr_C_D(irr_s,ps,ns))
    ss = frozenset(ss)
    if increase:
        if len(ss)>=len(s):
            return ss
        else:
            if lift_C_D.print_LS_size_decrease and len(ss)>0:
                print("-----Decrease of size:----\n%s\n%s\n "%(str_LS(s),str_LS(ss)))
            return []
    else:
        return ss
lift_C_D.print_LS_size_decrease= False

def lift_irr_C_D(irr_s,ps,ns):
    pps,nns = _sign_ILS(irr_s)
    # irr_s is local system of symplectic group
    assert(pps==nns)
    # sign of first column
    fps,fns = _sign_ILS_firstcol(irr_s)
    # column added must always be even
    if (ps+ns) %2 ==0:
        addp, addn = ps-pps-fns,ns-nns-fps
        # The descent case
        if addp>=0 and addn>=0:
            # Twist 
            irr_s = _char_twist_C(irr_s,ps,ns)
            #print(irr_s )
            irr_ss = ((addp,addn),)+irr_s
            return [irr_ss]
        else:
            return []
    else: 
        raise ValueError("%s,%s,%s"%(irr_s,ps,ns))

def LS_C(part,increase=False):
    """
    Take a partition of type C
    part = (Ca, Cap, ..., C_1)
    If Ca is odd, Ca = Cap, we use generalized descent, 
                            lift LS of type D with (Cap+1, ..., C_1)
    If Ca is even, Cap must be even, we use descent
    """
    part = _simp_dec_seq(part)
    partsize = _part_size(part)
    n, res = divmod(partsize, 2)
    assert(res == 0)
    if partsize == 0:
        # return the set of empty tuple
        return set([frozenset([()])])
    else:
        Ca, Cap = part[0],getz(part, 1,0)
        if Ca % 2 ==0:
            assert(Cap%2 == 0)
            S = LS_D(part[1:], increase)
        elif Ca == Cap:
            S = LS_D([Cap+1]+part[2:], increase)
        else:
            raise ValueError("parity error")
        SS = []
        for s in S:
            ss = lift_D_C(s,n, increase)
            if len(ss)>0:
                SS.append(frozenset(ss))
        return set(SS)

    
    
def LS_D(part, increase=False):
    """
    Take a partition of type D
    part = (Ca, Cap, \cdots, C_1)
    Ca must be even!
    """
    part = _simp_dec_seq(part)
    partsize = _part_size(part)
    n, res = divmod(partsize, 2)
    assert(res == 0)
    if partsize == 0:
        # return the set of empty tuple
        return set([frozenset([()])])
    else:
        S = LS_C(part[1:],increase)
        # Lift trivial system first
        SS = []
        for i in range(partsize+1):
            for s in S:
                ss = lift_C_D(s, i, partsize-i,increase)
                if ss!= []:
                    SS.append(frozenset(ss))
        SSS = []
        for (tp,tn) in [(1,1),(1,-1),(-1,1), (-1,-1)]:
            for ss in SS:
                sss = []
                for irr_ss in ss:
                    sss.append(_char_twist_D(irr_ss,(tp,tn)))
                if sss!= []:
                    SSS.append(frozenset(sss))
        return set(SSS)


    
PNPN = '+-+'
QMQM = '*=*'
def str_row_irr_LR(irr_s):
    rows = []
    #print(irr_s)
    for i,(rp,rn) in enumerate(irr_s):
        hii, rii = divmod(i+1,2)
        onerow = ''
        if rn > 0:
            onerow = PNPN[1]*rii + PNPN[0:2]*hii
        elif rn <0:
            onerow = QMQM[1]*rii + QMQM[0:2]*hii 
        #print((rp,rn))
        rows.extend([onerow]*abs(rn))
        if rp > 0:
            onerow = PNPN[0]*rii + PNPN[1:3]*hii
        elif rp <0:
            onerow = QMQM[0]*rii + QMQM[1:3]*hii
        rows.extend([onerow]*abs(rp))
    rows.reverse()
    return rows
    
def str_LS(SS, show_sign=False):
    strILS = [str_row_irr_LR(irr_s) for irr_s in SS]
    if strILS != []:
        rowl = max([len(irr_rows) for irr_rows in strILS])
        #print(rowl)
        coll = max([len(getz(irr_rows,0,'')) for irr_rows in strILS])
        SR = []
        for i in range(rowl):
            row = []
            for irr_rows in strILS:
                irr_row = getz(irr_rows,i,'') 
                row.append(irr_row+' '*(coll-len(irr_row)))
            SR.append(' | '.join(row))
        strLS = '\n'.join(SR)
        if show_sign:
            strLS = '%s\n(%d,%d)'%(strLS, *sign_LS(SS))
        return strLS
    else:
        return ''
   

def print_list_LS_D(part, report=True, printdig=False, increase=False):
    LLS = LS_D(part, increase)
    if report:
        print('Partition:', part)
        print('Number of LS: %d' % len(LLS))
    if printdig:
        for SS in LLS:
            print('%s\n' % (str_LS(SS)))
    return LLS


def print_list_LS_C(part, report=True,printdig=False,increase=False):
    LLS = LS_C(part,increase)
    if report:
        print('Partition:', part)
        print('Number of LS: %d'%(len(LLS)))
    if printdig:
        for SS in LLS:
            print('%s\n'%(str_LS(SS)))
    return LLS

            

"""
Code for counting local systems of type B and metaplectic group 
Data structure:
an irreducible local system is represented by a tuple [(p_1,n_1),(p_2,n_2),...(p_k,n_k)]
p_i: means there are |p_i| rows with length i and "+" at the end of the row,
    p_i>0 if the local system is trivial, 
    p_i <0 if the local system is the non-trivial one
    p_i =0, 0 is neither positive nor negative, and we don't have to assign local system. 
n_i: means there are |n_i| rows with length i and "-" at the end of the row
    n_i>0 means trivial system, n_i<0 means non-trivial one. 

For visialization:
    + : trivial system on + sign, 
    * : non-trivial system on + sign
    - : trivial system on - sign,
    = : non-trivial system on - sign. 

A local system is frozenset of irreducible local systems
"""


"""
def _sign_ILS(irr_s):
    p,n = 0,0
    for i,(pp,nn) in enumerate(irr_s):
        dii, rii = divmod(i+1,2)
        p += abs(pp)*(dii+rii)+abs(nn)*dii
        n += abs(nn)*(dii+rii)+abs(pp)*dii
    return (p,n)

def _sign_ILS_firstcol(irr_s):
    p,n = 0,0
    #print(irr_s)
    for i, (pp,nn) in enumerate(irr_s):
        if i%2 == 0:
            p += abs(pp)
            n += abs(nn)
        else:
            p += abs(nn)
            n += abs(pp)
    return (p,n)
"""        

# def _char_twist_M_t(irr_s,twist):
#     """
#     twist the irreducible local system of type metaplectic by det^t
#     K_Mp = {(g,e)| e^2 = det(g): g\in U(n)}.
#     det^1/2(g,e) = e
#     O(V_p) act on V_p\otimes W_2k
#     (dim V_p = p, W_2k is the standard repn of SL_2)
#     (g,e)\in \wtO(V_p), then acts by e^k.
#     # When k is even, det is the default twist
#     # When k is odd, det^1/2 is the default twist
#     The default twist is always det^(k/2)
#     """
#     # Suppose we twist det^1/2|K_X:
#     # only twist even length row,
#     # If the row is length 2k, then det restricted to det^(k/2) on each factor.
#     # If k is even don't twist the character
#     # If k is odd, we fix the default twist to be det^1/2
#     #              the other twist is det^(-1/2)
#     if twist == 1:
#         irr_ss = tuple((-pp, -nn) if (i+1)%8==6 else (pp,nn)
#                        for i, (pp,nn) in enumerate(irr_s))
#         return irr_ss
#     elif twist == 3:
#         irr_ss = tuple((-pp, -nn) if (i+1)%8==2 else (pp,nn)
#                        for i, (pp,nn) in enumerate(irr_s))
#         return irr_ss
#     else:
#         assert(False)



def _char_twist_CM(irr_s,j):
    """
    twist the irreducible local system of type CM j times:
    When j is even no tiwst
    When j is odd twist the 2k rows for k odd.
    """
    if j %2 == 1:
        irr_ss = tuple((-pp, -nn) if (i+1)%4==2 else (pp,nn)
                       for i, (pp,nn) in enumerate(irr_s))
        return irr_ss
    else:
        return irr_s



def _char_twist_M(irr_s, ps, ns):
    """
    Here (ps,ns) is the signature of the other group = odd orthogonal group.
    """
    assert((ps-ns)%2 ==1)
    return _char_twist_M_t(irr_s, (ps-ns)%4)

def _flip_sign(irr_s):
    res = tuple( (nn,pp,) for pp,nn in irr_s)
    return res

def flip_sign_LS(LS):
    nLS = frozenset(_flip_sign(irr_s) for irr_s in LS)
    return nLS

def char_twist_B(LS, twist):
    nLS = [_char_twist_B(irr_s, twist) for irr_s in LS]
    return frozenset(nLS)

def _char_twist_B(irr_s,twist):
    """
    twist type B irreducible local system 
    """
    tp, tn = twist
    irr_ss = []
    for i, (pp,nn) in enumerate(irr_s):
        hrl, rrl = divmod(i+1, 2)
        if rrl == 0:
            irr_ss.append((pp,nn))
        else:
            tpp = (tp**(hrl+1))*(tn**hrl)
            tnn = (tn**(hrl+1))*(tp**hrl)
            irr_ss.append((tpp*pp,tnn*nn))
    return tuple(irr_ss)

#def _part_size(part):
#    return sum(part)

def lift_irr_B_M(irr_s, n):
    """
    irr_s: an irreducible local system
    Lift type B irr_s to type M_n
    """
    ps, ns = _sign_ILS(irr_s)
    #Odd orthogonal group
    assert((ps+ns)%2 == 1)
    # sign of first column
    fps,fns = _sign_ILS_firstcol(irr_s)
    # first column must always be odd 
    if (fps+fns) %2 ==1:
        addp, addn = n-ps-fns,n-ns-fps
        # The descent case
        if addp>=0 and addn>=0:
            irr_ss = ((addp,addn),)+irr_s
            irr_ss = _char_twist_CM(irr_ss, (ps-ns-1)/2)
            return [irr_ss]
        #The generalized descent case
        elif (addp,addn) in [(-1,-1),(-2,0),(0,-2)]: 
            pp, nn = irr_s[0]
            ss = []
            #irr_ss = [(nn,pp) for pp,nn in irr_s[1:]]
            """
            +   lifts to -+, - lifts to +-
            +                -
            """
            if pp>0:
                irr_ss = ((0,0),(pp-1,nn))+irr_s[1:]
                irr_ss = _char_twist_CM(irr_ss, (ps-ns-1)/2)
                ss.append(tuple(irr_ss))
            if nn>0:
                irr_ss = ((0,0),(pp,nn-1))+irr_s[1:]
                irr_ss = _char_twist_CM(irr_ss, (ps-ns-1)/2)
                ss.append(tuple(irr_ss))
            return ss
        else:
            return []
    else:
        raise ValueError("type B to M parity error")
        
    
def lift_B_M(s, n, increase=False):
    """
    Lift local system from odd orthogonal group to Metaplectic group 
    """
    ss = []
    for irr_s in s:
        ss.extend(lift_irr_B_M(irr_s,n))
    ss = frozenset(ss)
    return ss

def lift_M_B(s, ps,ns, increase=False):
    """
    Lift the local system from metaplectic group to odd orthogonal group
    (ps,ns) is the signature of orthogonal group
    """
    ss = []
    for irr_s in s:
        ss.extend(lift_irr_M_B(irr_s,ps,ns))
    ss = frozenset(ss)
    return ss

def lift_irr_M_B(irr_s,ps,ns):
    pps,nns = _sign_ILS(irr_s)
    # irr_s is local system of metaplectic group
    assert(pps==nns)
    # sign of first column
    fps,fns = _sign_ILS_firstcol(irr_s)
    # column added must always be odd 
    if (ps+ns) %2 ==1:
        addp, addn = ps-pps-fns,ns-nns-fps
        # The descent case
        if addp>=0 and addn>=0:
            # Twist 
            irr_s = _char_twist_CM(irr_s,(ps-ns+1)/2)
            #print(irr_s )
            irr_ss = ((addp,addn),)+irr_s
            return [irr_ss]
        else:
            return []
    else: 
        raise ValueError("%s,%s,%s"%(irr_s,ps,ns))

def LS_M(part):
    """
    Take a partition of type M
    part = (Ca, Cap, ..., C_1)
    If Ca is even, Ca = Cap, we use generalized descent, 
                            lift LS of type B with (Cap+1, ..., C_1)
    If Ca is odd, Cap  must be odd, we use descent
    """
    part = _simp_dec_seq(part)
    partsize = _part_size(part)
    n, res = divmod(partsize, 2)
    assert(res == 0)
    if partsize == 0:
        # return the set of empty tuple
        return set([frozenset([()])])
    else:
        Ca, Cap = part[0],getz(part, 1,0)
        if Ca % 2 ==1:
            assert(Cap%2 == 1)
            S = LS_B(part[1:])
        elif Ca == Cap:
            S = LS_B([Cap+1]+part[2:])
        else:
            raise ValueError("parity error")
        SS = []
        for s in S:
            ss = lift_B_M(s,n)
            if len(ss)>0 :
                SS.append(frozenset(ss))
        return set(SS)

    
    
def LS_B(part, splitform=False):
    """
    Take a partition of type B
    part = (Ca, Cap, \cdots, C_1)
    Ca must be odd!
    """
    part = _simp_dec_seq(part)
    partsize = _part_size(part)
    n, res = divmod(partsize, 2)
    #total number of boxes must be odd.
    assert(res == 1)
    if partsize == 0:
        # return the set of empty tuple
        return set([frozenset([()])])
    else:
        S = LS_M(part[1:])
        # Lift trivial system first
        SS = []
        #ogroups = []
        if splitform:
            ogroups = [(partsize//2+1, partsize//2)]
        else:
            ogroups = [(ps,partsize-ps) for ps in range(partsize+1)]
        for (ps,ns) in ogroups:
            for s in S:
                ss = lift_M_B(s, ps, ns)
                if ss!= []:
                    SS.append(frozenset(ss))
        SSS = []
        for (tp,tn) in [(1,1),(1,-1),(-1,1), (-1,-1)]:
            for ss in SS:
                sss = []
                for irr_ss in ss:
                    sss.append(_char_twist_B(irr_ss,(tp,tn)))
                if sss!= []:
                    SSS.append(frozenset(sss))
        return set(SSS)
    
def typeerr(part):
    raise ValueErrow('Wrong type %s'%rtype)
    

def part2LS(part, rtype, report=True, printdig=False):
    fundict = {'B': LS_B,
               'BS': lambda part: LS_B(part, splitform=True),
               'M': LS_M,
               'C': LS_C,
               'D': LS_D,
               }
    partfun = fundict.get(rtype, typeerr)
    LLS = partfun(part)
    if report:
        print('Type %s  partition: %s'%(rtype, part))
        print('Number of LS: %d'%len(LLS))
        if rtype=='BS':
            print('Number of LS of the split form with tivial 1-rows: %g'%((len(LLS)/2)))
    if printdig:
        for SS in LLS:
            print('%s\n'%(str_LS(SS)))
    return LLS

print_list_LS = part2LS

def remove_odd_rows(part):
    res = sorted(part, reverse=True)
    oddrows = [res[2*i]-getz(res,2*i+1) for i in range(len(res)//2)]
    res =  [x - sum(oddrows[(i+1)//2:]) for i,x in enumerate(res)] 
    return res

def show_drc_dgms(dgms, rtype):
    rtype_funs = {'C':str_dgms_C, 'B':str_dgms_B, 'D':str_dgms_D}
    for dd in dgms:
        print("%s\n\n"%rtype_funs[rtype](dd))
        
def dual_form_C(drc):
    sdrc = str_dgms_C(drc)
    cplx = sdrc.count('.')
    real = sdrc.count('r')
    cpt1 = sdrc.count('c')
    cpt2 = sdrc.count('d')
    dp, dq = cplx+real+cpt1*2+1, cplx+real+cpt2*2
    return (dp,dq)

"""
Construct diagrams for type D = SO(p,q)
"""

def form_C(drc):
    drcL, drcR = drc
    return sum(len(c) for c in itertools.chain(drcL,drcR))


def S_Wrepn_D(part):
    """
    From type D special orbit to special representations of the Weyl group
    """
    part = [x for x in part if x!=0]
    ll = len(part)
    part.sort()
    a, res = divmod(ll,2) 
    if res == 1:
        part=[0]+part
        a = a+1
    #print(C,a)
    # The last entry C_{2a-1} must be even
    assert(part[-1]%2 ==0)
    tauL = [(part[2*i+1]+1)//2 for i in range(a)]
    tauR = [part[2*i]//2 for i in range(a)]
    return (tauL,tauR)


"""
New version
"""
def S_Wrepns_D(tau):
    """
    Type D
    Special representation ot set of representation in 
    coherent continuations. 
    the formula is 
    (c_{2i},c_{2i-1})<--> (c_{2i-1}-1,c_{2i}+1)
    
    We assume tauL and tauR are arranged in incresing order
    """
    
    tauL, tauR = tau
    assert(len(tauL) == len(tauR))
    a = len(tauL)
    tauL,tauR = sorted(tauL), sorted(tauR) 
    # tauL[i-1] = c_{2i-1}, tauR[i] = c_{2i}
    cidxs = [i for i in range(1,a) if tauL[i-1]!=tauR[i]+1]
    Atau = []
    for k in range(len(cidxs)+1):
        for oidxs in itertools.combinations(cidxs,k):
            tauLL= [tauR[i]+1 if i in oidxs else tauL[i-1] for i in range(1,a)]+[tauL[a-1]]
            tauRR= [tauR[0]]+[tauL[i-1]-1 if i in oidxs else tauR[i] for i in range(1,a)]
            Atau.append((tauLL,tauRR))
    return Atau


                
def _fill_cp_dgms_D(tau):
    """
    fill c' in the longest column
    """
    tau = _simp_W_repn(tau)
    if tau is None: 
        return []
    tauL,tauR = tau
    rL = len(tauL)
    S =[]
    # Put totally k "d"'s in the left diagram
    # k = 0,..., rL
    frow_lst = frow_col_list(tauL)
    for cidx in yield_cindex(frow_lst):
            tauLL = copy(tauL)
            for i in cidx:
                tauLL[i] -=1
            SS = _fill_c_dgms_D((tauLL,tauR))
            for drcL,drcR in SS:
                drcL = drcL+['']*(rL-len(drcL))
                for i in cidx:
                    drcL[i] +='d'
                S.append((drcL,drcR))
    return S
                    
          
def _fill_c_dgms_D(tau):
    """
    fill c in the longest column
    """
    tau = _simp_W_repn(tau)
    if tau is None: 
        return []
    tauL,tauR = tau
    rL = len(tauL)
    S =[]
    # Put totally k "c"'s in the left diagram
    # k = 0,..., rL
    frow_lst = frow_col_list(tauL)
    for cidx in yield_cindex(frow_lst):
            tauLL = copy(tauL)
            for i in cidx:
                tauLL[i] -=1
            SS = _fill_r_dgms_D((tauLL,tauR))
            for drcL,drcR in SS:
                drcL = drcL+['']*(rL-len(drcL))
                for i in cidx:
                    drcL[i] = getz(drcL,i,'')+'c'
                S.append((drcL,drcR))
    return S

def frow_data(part):
    assert(len(part)>0)
    Rind = [part[i]-part[i+1] for i in range(len(part)-1)]+[part[-1]]
    return Rind

def yield_r_del(Rind):
        """
        lidxs is a list of list of  numbers 
        [c_0, ..., c_k]
        the function yield an iterator return 
        a list of numbers [r_0, ..., r_k]
        such that r_i <= c_i
        """
        N = 0
        nlst = len(Rind) # Length of the list 
        ridx = [r for r in Rind]
        # yields the first index
        yield ridx
        while True:
            for i in range(nlst):
                if ridx[i] >0:
                   break
            else:
                return
            ridx = Rind[:i]+[ridx[i]-1]+ridx[i+1:]
            yield ridx

def _fill_r_dgms_D(tau):
    """
    Here the Young diagram is parameterized by columns 
    ([tauL_0, ...], [tauR_0, ...])
    Here r'=s are the r's in the right diagram
    """
    tau = _simp_W_repn(tau)
    if tau is None: 
        return []
    tauL,tauR = tau
    rL = len(tauL)
    if rL == 0:
        if len(tauR)==0:
            return [([],[])]
        else:
            return []
    S = []
    frow_lst = frow_data(tauL)
    for rdel in yield_r_del(frow_lst):
            tauLL = [tauL[i] -rdel[i] for i in range(rL)]
            SS = _fill_rp_dgms_D((tauLL,tauR))
            for drcL,drcR in SS:
                drcL = drcL+['']*(rL-len(drcL))
                for i in range(rL):
                    drcL[i] = drcL[i]+('r'*rdel[i])
                S.append((drcL,drcR))
    return S

def _fill_rp_dgms_D(tau):
    """
    Here the Young diagram is parameterized by columns 
    ([tauL_0, ...], [tauR_0, ...])
    Here r'=s are the r's in the right diagram
    """
    tau = _simp_W_repn(tau)
    if tau is None: 
        return []
    tauL,tauR = tau
    drcL, drcR = [],[]
    cols = max(len(tauL),len(tauR))
    for i in range(cols):
        cL, cR = getz(tauL,i,0), getz(tauR,i,0)
        ncL = getz(tauL,i+1,0)
        if cL < cR or cL-cR > cL - ncL:
            return []
        else:
            bul = '*'*cR
            drcR.append(bul)
            drcL.append(bul+'s'*(cL-cR))
    return [(drcL,drcR)]

def drc_dgms_D(tau):
    """
    Compute all dot-r-c diagrams for type D for 
    a Weyl group representation.
    
    Note that trivial representation corresponds to a single row
              sign    representation corresponds to a single column
    In this construction, we assume 
          tau = ([tauL_0>=tauL_1>= ...],[tauR_0>tauR_1>...])
    """
    tauL,tauR=tau
    tauL = sorted([x for x in tauL if x!=0],reverse=True)
    tauR = sorted([x for x in tauR if x!=0],reverse=True)
    tau =(tauL,tauR)
    return _fill_cp_dgms_D(tau)


def all_drc_dgms(tauS, drc_fun):
    S = [x
         for tau in tauS
         for x in drc_fun(tau)]
    return S

def print_drc_diag_D(partition, report = True,printdig=False, getlist=False,print_Wrepn=False):
    """
    print the dcr_diag attached to Nilpotent orbit of type D
    partition: = [C_{2a-1}>=C_{2a-2}... >=C_0>=0] is the list of column lengths of 
                  a type C nilpotent orbits. 
    """
    tau = S_Wrepn_D(partition)
    Stau = S_Wrepns_D(tau)
    if report:
        print("Type D partition: %s"%partition)
    if print_Wrepn:
        print("List of relevent W_n representations")
        print(Stau)
    #print(tau)
    Adrc =  all_drc_dgms(Stau,drc_dgms_D)
    if report:
        print("Number of drc diagrams: %d"%len(Adrc))
    if printdig:
        for drc in Adrc:
            print("%s"%str_dgms_D(drc))
            print("form is SO(%d,%d), dual form is SO(%d,%d)\n"
                  % (*form_D(drc), *dual_form_D(drc)))
    return Adrc


def form_D(drc):
    sdrc = str_dgms_D(drc)
    cplx = sdrc.count('.')
    cpt1 = sdrc.count('r')
    cpt2 = sdrc.count('s')
    real1 = sdrc.count('c')
    real2 = sdrc.count('d')
    dp, dq = cplx+real1+real2+cpt1*2, cplx+real1+real2+cpt2*2
    return (dp,dq)

def dual_form_D(drc):
    sdrc = str_dgms_D(drc)
    cplx = sdrc.count('.')
    real1 = sdrc.count('r')
    real2 = sdrc.count('s')
    cpt1 = sdrc.count('c')
    cpt2 = sdrc.count('d')
    dp, dq = cplx+real1+real2+cpt1*2, cplx+real1+real2+cpt2*2
    return (dp,dq)

def count_dgms_D_forms(Adrc):
    return count_signs(Adrc, form_D)


def count_LS_D_forms(LS):
    return count_signs(LS, sign_LS)


def sign_LS(ls):
    sgnls = set(_sign_ILS(ils) for ils in ls)
    if len(sgnls) >1:
        print('sign of LS is not unique', sgnls)
        print(str_LS(ls))
    if len(sgnls) == 0:
        return None
    return sgnls.pop()


def compare_sign(Adrc, LS):
    sgnDRC = count_dgms_D_forms(Adrc)
    sgnLS = count_LS_D_forms(LS)
    keys = {*sgnDRC.keys(), *sgnLS.keys()}
    Esgns = dict()
    for k in keys:
        ndrc, nls = sgnDRC.get(k, 0), sgnLS.get(k, 0)
        if 2*ndrc != nls:
            Esgns[k] = 2*ndrc-nls
    return Esgns


def count_signs(Adrc,count_fun):
    DD = dict()
    for drc in Adrc:
        sgn = count_fun(drc)
        DD[sgn] = DD.get(sgn,0)+1
    return DD


def str_dgms_D(drc):
    """
    Format of drc:
    drc = (drcL,drcR)
    drcL and drcR are string lists
    drcL = [cl_1, ..., cl_k], 
        each cl_i represents
        the symbol of a column
    """
    drcL,drcR = drc
    cL,cR = len(drcL),len(drcR)
    r = max(len(getz(drcL,0,'')),len(getz(drcR,0,'')))
    S = []
    for i in range(r):
        ll = [getz(cl,i,' ') for cl in drcL]
        rr = [getz(cr,i,' ') for cr in drcR]
        S.append(''.join(ll)+'|'+''.join(rr))
    s = '\n'.join(S)
    s = s.replace('*','.')
    return s   


"""
Following lifting only realize the algorithm for the orbits
after the reduction. These orbits satisfies C_{2i} = C_{2i-1}.
So we only realize the algorithm 
for adding a column of lenght equal to the longest lenght column in type D
or the generalized descent case (C_{2i} = C_{2i-1} is odd).  
"""
def lift_drc_D_C(drc,cR,printdrop=False):
    drcL, drcR = drc
    """
    if the lenght of '*'/'s' in the fisrt column > cR 
    then there is no lift. 
    Otherwise there is a lift. 
    """
    drcLL = [col.replace('s','*') for col in drcL]
    drcR = ['*'*cR]+drcR
    drcRR = []
    for i in range(max(len(drcLL),len(drcR))):
        colL, colR = getz(drcLL,i,''), getz(drcR,i,'')
        bL =  colL.count('*')
        cR, cnR = len(colR), len(getz(drcR,i+1, ''))
        assert(bL>=cnR)
        if bL> cR:
            if printdrop:
                print('\n%s\n---------\n'%(str_dgms_C((drcL,drcR))))
            return None
        else:
            drcRR.append('*'*bL+'s'*(cR-bL))
    return (drcLL,drcRR)
    

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


def lift_drc_D_C_det(drc):
    """
    Lift the representation with the determinant twist,
    change c_{2a-1} to c_{2a-1}+1,
    and attache c_{2a}-1 on the right diagram
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


def lift_drc_D_C(drc,cR,printdrop=False):
    drcL, drcR = drc
    """
    if the lenght of '*'/'s' in the fisrt column > cR 
    then there is no lift. 
    Otherwise there is a lift. 
    """
    drcLL = [col.replace('s','*') for col in drcL]
    drcR = ['*'*cR]+list(drcR)
    drcRR = []
    for i in range(max(len(drcLL),len(drcR))):
        colL, colR = getz(drcLL,i,''), getz(drcR,i,'')
        bL =  colL.count('*')
        cR, cnR = len(colR), len(getz(drcR,i+1, ''))
        assert(bL>=cnR)
        if bL> cR:
            if printdrop:
                print('\n%s\n---------\n'%(str_dgms_C((drcL,drcR))))
            return None
        else:
            drcRR.append('*'*bL+'s'*(cR-bL))
    return (tuple(drcLL),tuple(drcRR))
    
def lift_drc_D_C_gd(drc):
    drcL, drcR = drc
    """
    if the lenght of '*'/'s' in the fisrt column > cR 
    then there is no lift. 
    Otherwise there is a lift. 
    """
    drcL, drcR = drc
    col0 = getz(drcL, 0, '')
    assert(len(col0)>0)
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
    assert(len(col0)>0)
    return lift_drc_D_C(drc, len(col0))    

def lift_dgms_D_C_gd(dgms):
    S = []
    for drc in dgms:
        ldrc = lift_drc_D_C_gd(drc)
        if ldrc is not None:
            S.append(ldrc)
    return S


def twist_C_nonspecial(drc):
    """
    send a the special diagram to non-special diagram
    special diagram means the longest column length of 
    the left and right diagram are the same
    """
    drcL, drcR = drc
    # first, second column of drcL and first column of drcR
    fL, sL, fR = getz(drcL,0,''), getz(drcL,1,''), getz(drcR,0,'')
    assert(len(fR)==len(fL) and len(fR)>0)
    fRR = fR[:-1]
    if fR[-1] == 's':
        if len(fL)==1 or fL[-2] != 'c':
            fLL = fL[:-1]+'r'+fL[-1:]
        else:
            fLL = fL[:-2]+'r'+fL[-2:]
        nspdrc = (tuple([fLL]+list(drcL[1:])),tuple([fRR]+list(drcR[1:])))
    elif (fL[-1], getz(sL,len(fL)-1,'')) == ('*','r'):
        fLL = fL[:-1]+'rd'
        sLL = sL[:-1]+'c'
        nspdrc = (tuple([fLL,sLL]+list(drcL[2:])),tuple([fRR]+list(drcR[1:])))
    else :
        fLL = fL[:-1]+'cd'
        nspdrc = (tuple([fLL]+list(drcL[1:])),tuple([fRR]+list(drcR[1:])))
    if not verify_drc(nspdrc,'C'):
        print('Invalid nonspecial drc\n original: \n%s\n new:\n%s\n'
              %(str_dgms_C(drc),str_dgms_C(nspdrc)))
        return None
    return nspdrc

def lift_drc_D_C_det(drc):
    spdrc = lift_drc_D_C_trivial(drc)
    nspdrc = twist_C_nonspecial(spdrc)
    return nspdrc

def _add_bullet_D(drcL,drcR):
    fL, fR = drcL[0], getz(drcR,0, '')
    nfL,nfR = len(fL), len(fR)
    assert(nfL==nfR)
    rr = max(len(drcL),len(drcR))
    Rlen = [len(getz(drcR,i,'')) for i in range(rr)]
    bRlen = [getz(drcR,i,'').count('*') for i in range(rr)]
    ndrcR = tuple('*'*cl for cl in Rlen)
    ndrcL = ['*'*nfL]
    for i in range(rr):
        col = getz(drcL,i,'')
        nlR, nnlR = getz(bRlen,i,0), getz(Rlen,i+1,0) 
        ncol = '*'*nnlR+'s'*(nlR-nnlR)+col[nlR:]
        ndrcL.append(ncol)
    return (tuple(ndrcL), ndrcR)
    
def gen_drc_D_two(fL, n):
    RES =  []
    if fL in ['','d']:
        RES.extend([('s'*i+'r'*(n-i),fL) for i in range(n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c',fL) for i in range(n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d',fL) for i in range(n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd',fL) for i in range(n-1)])
    elif fL == 'c':
        RES.extend([('s'*i+'r'*(n-i),fL) for i in range(1,n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c',fL) for i in range(1,n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d',fL) for i in range(1,n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd',fL) for i in range(1,n-1)])
        if n>=1:
            RES.extend([('r'*(n-1)+'c','c'),])
        if n>=2:
            RES.extend([('r'*(n-2)+'cd','c')]) 
    elif fL == 'r':
        RES.extend([('s'*i+'r'*(n-i),fL) for i in range(1,n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c',fL) for i in range(1,n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d',fL) for i in range(1,n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd',fL) for i in range(1,n-1)])
        RES.append(('r'*n,'c'))
        if n>=2:
            RES.extend([('r'*(n-1)+'d','c')])
        #if n>2:
        #    RES.extend([('r'*(n-2)+'cd','c')])    
    elif fL == 'rr':
        assert(n>=2)
        RES.extend([('s'*i+'r'*(n-i),'rr') for i in range(2,n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c','rr') for i in range(2,n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d','rr') for i in range(2,n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd','rr') for i in range(2,n-1)])
        RES.extend([('r'*n,'cd'),
                    ('r'*(n-1)+'c','cd'),
                    ('r'*(n-1)+'d','cd')])
        if n>=3:
            RES.extend([('r'*(n-2)+'cd','cd')])
        #if n>2:
        #    RES.extend([('s'*i+'r'*(n-i-1)+'d',fL) for i in range(2,n)])
        #else:
        #    RES.extend([('cd','cd')])
        #if n==2:
        #    RES = [('rr','cd'),('rc','cd'),('rd','cd'),('ss','rr')]
    elif fL == 'rc':
        assert(n>=2)
        RES.extend([('s'*i+'r'*(n-i),fL) for i in range(1,n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c',fL) for i in range(1,n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd',fL) for i in range(1,n-1)])
        if n>2:
            RES.extend([('s'*i+'r'*(n-i-1)+'d',fL) for i in range(1,n)])
        else:
            RES.extend([('cd','cd')])
        #if n==2:
        #    RES = [('sr','rc'), ('ss','rc'),('sc','rc'), ('cd','cd')]
    elif fL == 'rd':
        assert(n>=2)
        RES.extend([('s'*i+'r'*(n-i),fL) for i in range(1,n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c',fL) for i in range(1,n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d',fL) for i in range(1,n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd',fL) for i in range(1,n-1)])
        #if n==2:
        #    RES =  [('sr',fL), ('ss',fL),('sc',fL),('sd',fL)]
    elif fL == 'cd':
        assert(n>=2)
        RES.extend([('s'*i+'r'*(n-i),fL) for i in range(1,n+1)])
        RES.extend([('s'*i+'r'*(n-i-1)+'c',fL) for i in range(1,n)])
        RES.extend([('s'*i+'r'*(n-i-1)+'d',fL) for i in range(1,n)])
        RES.extend([('s'*i+'r'*(n-i-2)+'cd',fL) for i in range(1,n-1)])
        #if n==2:
        #    RES =  [('sr',fL), ('ss',fL),('sc',fL),('sd',fL)]
    return RES

def lift_drc_C_D(drc,a):
    drcL, drcR = drc
    fL, fR = getz(drcL, 0, ''),getz(drcR, 0, '')
    nL, nR = len(fL), len(fR)
    assert(nL-nR <= 2)
    assert(nL <= a)
    bdrcL, bdrcR = _add_bullet_D([fL[:nR]]+list(drcL[1:]),drcR)
    #print(fL)
    ldrcD2 = gen_drc_D_two(fL[nR:],a-nR)
    RES = []
    for ffL, fL in ldrcD2:
        drcLL = [bdrcL[0]+ffL,bdrcL[1]+fL] + list(bdrcL[2:])
        ndrc = (tuple(drcLL),tuple(bdrcR))
        if not verify_drc(ndrc,'D'):
            print('Invalid drc:',str_dgms_D(drc),a)
            print('Invalid drc:',str_dgms_D(ndrc))
        RES.append(ndrc)
    assert(len(RES)==len(set(RES)))
    #print(drc)
    #print(RES)
    return RES

def updateDRCLS(RES, drc, LS):
    if drc in RES:
        print('Collision of keys', drc)
        print('%s\n~~~~~~~~~~~\n%s'%(str_LS(RES[drc]),str_LS(LS)))
    else:
        RES[drc] = LS
    
def lift_drcs(DRCLS, rtype='C', ltype='l'):
    RES = dict()
    if rtype == 'C' and ltype == 'l':
        for drc, LS in DRCLS.items():
            pO,nO = form_D(drc)
            ppO,nnO = sign_LS(LS)
            assert((pO,nO)==(ppO,nnO))
            anSp = len(drc[0][0])
            nSp = anSp + (pO+nO)//2
            # Lift trivial twist
            ndrc = lift_drc_D_C_trivial(drc)
            nLS = lift_D_C(LS, nSp)
            updateDRCLS(RES,ndrc,nLS)
            #RES[ndrc] = nLS
            # Lift det twist
            dLS = char_twist_D(LS, (-1,-1))
            ndLS = lift_D_C(dLS,nSp)
            nspdrc = twist_C_nonspecial(ndrc)
            updateDRCLS(RES,nspdrc,ndLS)
            #RES[nspdrc] = ndLS
    elif rtype == 'C' and ltype == 'L':
        for drc, LS in DRCLS.items():
            pO,nO = form_D(drc)
            ppO,nnO = sign_LS(LS)
            assert((pO,nO)==(ppO,nnO))
            anSp = len(drc[0][0])-1
            nSp = anSp + (pO+nO)//2
            # Lift trivial twist
            ndrc = lift_drc_D_C_gd(drc)
            if ndrc is not None:
                nLS = lift_D_C(LS,nSp)
                updateDRCLS(RES,ndrc,nLS)
                #RES[ndrc] = nLS
    elif rtype == 'D':
        ltype == int(ltype)
        assert(ltype>0)
        if len(DRCLS) == 0:
            zdrc = (('',), ('',))
            DRCLS[zdrc] = frozenset([tuple()])
        for drc, LS in DRCLS.items():
            if drc is None: continue
            nSp = form_C(drc)
            nnSp = sign_LS(LS)[0]
            assert(nSp==nnSp)
            aL = ltype//2 - nSp
            NDRCS = lift_drc_C_D(drc, aL)
            for ndrc in NDRCS:
                pO, nO = form_D(ndrc)
                nLS= lift_C_D(LS, pO, nO)
                if schar_or_trivial_D(ndrc):
                    nLS = char_twist_D(nLS, (1,-1))
                updateDRCLS(RES,ndrc,nLS)
                #RES[ndrc]=nLS
    return RES


def print_DRCLS(DRCLS):
    for drc, LS in DRCLS.items():
        #print(drc,LS)
        print(str_dgms_D(drc))
        print(str_LS(LS))
        print('----------------------')
        
def print_LSDRC(LSDRC):
    for LS, drcs in LSDRC.items():
        #print(drc,LS)
        print(str_LS(LS))
        for drc in drcs:
            print('~~~~~~~~~~~~~~~~~')
            print(str_dgms_D(drc))
        print('----------------------')
   
        
def schar_or_trivial_D(drc):
    drcL, drcR = drc
    if drcL[0][-1] == 'd':
        return False
    else:
        return True
            
def test_young_dg(dg):
    return all(len(getz(dg,i,''))>= len(getz(dg,i+1,'')) 
               for i in range(len(dg)))

def test_young_drc(drc):
    drcL, drcR = drc
    return test_young_dg(drcL) and test_young_dg(drcR)

def test_bullets_drc(drc):
    drcL, drcR = drc
    for i in range(max(len(drcL),len(drcR))):
        cL, cR = getz(drcL, i, ''), getz(drcR, i, '')
        nL, nR = cL.count('*'), cR.count('*')
        if  (len(cL),len(cR)) != (nL, nR) or len(cL) != len(cR):
            return False
    return True
    
def remove_tail_letter(dg,l,onerow=False):
    ddg = []
    for col in dg:
        dcol = col.rstrip(l)
        if onerow and len(col)-len(dcol)>1:
            return None
        ddg.append(dcol)
    return tuple(ddg)

            
def verify_drc(drc, rtype='C'):
    if rtype == 'C':
        drcL, drcR = drc
        if test_young_dg(drcL) is False or test_young_dg(drcR) is False:
            return False
        cdrcL = remove_tail_letter(drcL,'d',onerow=True)
        if cdrcL is None or test_young_dg(cdrcL) is False:
            return False
        ccdrcL = remove_tail_letter(cdrcL,'c',onerow=True)
        if ccdrcL is None or test_young_dg(ccdrcL) == False:
            return False
        rccdrcL = remove_tail_letter(ccdrcL,'r')
        rdrcR = remove_tail_letter(drcR,'s')
        if rccdrcL is None or test_young_dg(rccdrcL) is False or \
            rdrcR is None or test_young_dg(rdrcR) is False or\
            test_bullets_drc((rccdrcL,rdrcR)) is False:
            return False
    elif rtype == 'D':
        drcL, drcR = drc
        if test_young_dg(drcL) is False or test_young_dg(drcR) is False:
            return False
        cdrcL = remove_tail_letter(drcL,'d',onerow=True)
        if cdrcL is None or test_young_dg(cdrcL) is False:
            return False
        ccdrcL = remove_tail_letter(cdrcL,'c',onerow=True)
        if ccdrcL is None or \
            test_young_dg(cdrcL) == False:
            return False
        rccdrcL = remove_tail_letter(ccdrcL,'r')
        if rccdrcL is None:
            return False
        srccdrcL = remove_tail_letter(rccdrcL,'s')
        if srccdrcL is None or \
            test_bullets_drc((srccdrcL,drcR)) is False:
            return False  
    return True

def switch_kv(D):
    RD = dict()
    for k,v in D.items():
        RD.setdefault(v, []).append(k)
    return RD

def reg_drc(drc):
    if drc is None: return None
    drcL, drcR = drc
    drcL = tuple(x for x in drcL if len(x)> 0)
    drcR = tuple(x for x in drcR if len(x)> 0)
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
        RES[drc] = (LS,char_twist_D(LS,(-1,-1)))
    return RES

def det_all_LS(LSS):
    RES = set()
    for LS in LSS:
        RES.update([LS,char_twist_D(LS,(-1,-1))])
    return RES

def print_nonone(LSDRC):
    for LS,drcs in LSDRC3.items():
        if len(drcs)>1:
            print(str_LS(LS))
            print('\n~~~~~~~~~~~~\n'.join([str_dgms_D(drc) for drc in drcs]))

            
