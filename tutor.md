```python
%load_ext autoreload
%autoreload 2
from IPython.display import Markdown as md
from IPython.display import Latex as lt
from combunipotent import *
```

Notation: 

$[r_1, r_2, \cdots, r_k]$ denote a Young diagram with rows $r_1, \cdots, r_k$. 

$(c_1, c_2, \cdots, c_k)$ denote a Young diagram with columns $c_1, \cdots, c_k$. 

Let $\mathcal O^\vee = [r_1, r_2, \cdots, r_k]$ be a nilpotent orbit, we can comput its Barbasch-Vogan dual.

The following is an example of computing the Barbasch-Vogan dual {{aa}}


```python
dO,rtype = (15,11,7,7,5,5,3,3,1,1),'D'
display(lt(r'Let $\mathcal O^\vee$ (a orbit of type D) has rows $%s$'%(list(dO),)))
O = dualBVW(dO,rtype,partrc='c')
display(lt(r'Then $\mathcal O$ (a orbit of type D) has columns $%s$'%(tuple(O),)))
display(lt(r'The set of Weyl group representations attached to $\mathcal O^\vee$ are the follows (the first one is special)'))
RR = dualpart2Wrepn(dO,rtype)
aa = lt(r'%s'%(list(dO)))
for tau in RR:
    display(lt(r'$%s \times %s$'%tau))
#RRA = dualpart2WrepnA(dO,rtype)
#print(len(RR), RR)
#print(len(RRA), RRA)
#set(RR) == set(RRA)
```


Let $\mathcal O^\vee$ (a orbit of type D) has rows $[15, 11, 7, 7, 5, 5, 3, 3, 1, 1]$



Then $\mathcal O$ (a orbit of type D) has columns $(16, 10, 8, 6, 6, 4, 4, 2, 2)$



The set of Weyl group representations attached to $\mathcal O^\vee$ are the follows (the first one is special)



$(8, 4, 3, 2, 1) \times (5, 3, 2, 1)$



$(8, 6, 3, 2, 1) \times (3, 3, 2, 1)$



$(8, 4, 4, 2, 1) \times (5, 2, 2, 1)$



$(8, 4, 3, 3, 1) \times (5, 3, 1, 1)$



$(8, 4, 3, 2, 2) \times (5, 3, 2)$



$(8, 6, 4, 2, 1) \times (3, 2, 2, 1)$



$(8, 6, 3, 3, 1) \times (3, 3, 1, 1)$



$(8, 6, 3, 2, 2) \times (3, 3, 2)$



$(8, 4, 4, 3, 1) \times (5, 2, 1, 1)$



$(8, 4, 4, 2, 2) \times (5, 2, 2)$



$(8, 4, 3, 3, 2) \times (5, 3, 1)$



$(8, 6, 4, 3, 1) \times (3, 2, 1, 1)$



$(8, 6, 4, 2, 2) \times (3, 2, 2)$



$(8, 6, 3, 3, 2) \times (3, 3, 1)$



$(8, 4, 4, 3, 2) \times (5, 2, 1)$



$(8, 6, 4, 3, 2) \times (3, 2, 1)$


Suppose $\mathcal O^\vee$ is a of type $\star = C$ and $(1,2)\in \mathrm{PP}(\mathcal O^\vee)$ there is a switch between the set of painted bipartition of special shapes and 
non-special shapes. 
The following is an example:


```python
dO, rtype = (5,3,3,3,1),'C' 
display(lt(r'Let $\mathcal O^\vee$ has rows $%s$'%(list(dO),)))
O = dualBVW(dO,'C',partrc='c')
display(lt(r'Then $\mathcal O$ has columns $%s$'%(O,)))
Wrepns = dualpart2Wrepn(dO,rtype)
taus = Wrepns[0]
tauns = Wrepns[1]
display(lt(r'The special representation (columns) $\tau =$ %s $\times$  %s is paired with $\bar\tau = $ %s $\times$ %s  (with $\wp_{\bar\tau} = \{(1,2)\}$)'%(taus+tauns)))
display(lt(r'The switching between  $\mathrm{PBP}_C(\mathcal O^\vee,\emptyset)$ and $\mathrm{PBP}_C(\mathcal O^\vee, \{(1,2)\})$ is given by:'))
Adrcs = [drc for drc in Wrepn2drcs(taus,'C')]
for drc in  Adrcs:
    nsdrc  = twist_C_nonspecial(drc)
    res = concat_strblocks(str_dgms(drc),"<==>",str_dgms(nsdrc))
    print(res)
```


Let $\mathcal O^\vee$ has rows $[5, 3, 3, 3, 1]$



Then $\mathcal O$ has columns $[4, 4, 3, 3]$



The special representation (columns) $\tau =$ (2, 2) $\times$  (2, 1) is paired with $\bar\tau = $ (3, 2) $\times$ (1, 1)  (with $\wp_{\bar\tau} = \{(1,2)\}$)



The switching between  $\mathrm{PBP}_C(\mathcal O^\vee,\emptyset)$ and $\mathrm{PBP}_C(\mathcal O^\vee, \{(1,2)\})$ is given by:



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.c|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .c|.s
dd|s       rd|  
           d |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.r|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .r|.s
dd|s       rd|  
           d |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|.. <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> ..|..
dd|s       rd|  
           d |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.c|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .c|.s
cd|s       rd|  
           c |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.r|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .r|.s
cd|s       rd|  
           c |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|.. <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> ..|..
cd|s       rd|  
           c |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.c|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .c|.s
rd|s       rd|  
           r |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.c|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .c|.s
.d|.       cd|  
           d |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.r|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .r|.s
rd|s       rd|  
           r |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.r|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .r|.s
.d|.       cd|  
           d |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|.. <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> ..|..
rd|s       rd|  
           r |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|.. <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> ..|..
.d|.       cd|  
           d |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.r|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .r|.s
cc|s       rc|  
           c |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|.. <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> ..|..
cc|s       rc|  
           c |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.r|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .r|.s
rc|s       rc|  
           r |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.r|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .r|.s
.c|.       cc|  
           d |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|.. <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> ..|..
rc|s       rc|  
           r |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|.. <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> ..|..
.c|.       cc|  
           d |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.r|.s <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> .r|.s
.r|.       rc|  
           d |  
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|.. <span style="font-weight: bold">&lt;</span><span style="color: #000000">==</span><span style="font-weight: bold">&gt;</span> ..|..
.r|.       rc|  
           d |  
</pre>




```python
dO, rtype = (4,4,4,2),'M' 
display(lt(r'Let $\mathcal O^\vee$ has rows $%s$'%(list(dO),)))
O = dualBVW(dO,rtype,partrc='c')
display(lt(r'Then $\mathcal O$ has columns $%s$'%(O,)))
Wrepns = dualpart2Wrepn(dO,rtype)
taus = Wrepns[0]
tauns = Wrepns[1]
display(lt(r'The special representation (columns) $\tau =$ %s $\times$  %s is paired with $\bar\tau = $ %s $\times$ %s  (with $\wp_{\bar\tau} = \{(1,2)\}$)'%(taus+tauns)))
display(lt(r'The switching between  $\mathrm{PBP}_C(\mathcal O^\vee,\emptyset)$ and $\mathrm{PBP}_C(\mathcal O^\vee, \{(1,2)\})$ is given by:'))
Adrcs = [drc for drc in Wrepn2drcs(taus,rtype)]
for drc in  Adrcs:
    #nsdrc  = twist_M_nonspecial(drc)
    #res = concat_strblocks(str_dgms(drc),"<==>",str_dgms(nsdrc))
    print(str_dgms(drc))
```


Let $\mathcal O^\vee$ has rows $[4, 4, 4, 2]$



Then $\mathcal O$ has columns $[4, 4, 4, 2]$



The special representation (columns) $\tau =$ (2, 2) $\times$  (2, 1) is paired with $\bar\tau = $ (2, 1) $\times$ (2, 2)  (with $\wp_{\bar\tau} = \{(1,2)\}$)



The switching between  $\mathrm{PBP}_C(\mathcal O^\vee,\emptyset)$ and $\mathrm{PBP}_C(\mathcal O^\vee, \{(1,2)\})$ is given by:



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.d
cc|d 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.d
sc|d 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.r
cc|d 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|..
cc|d 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.r
sc|d 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|..
sc|d 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.d
cc|r 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.d
sc|r 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.d
.c|. 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.d
.s|. 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.r
cc|r 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|..
cc|r 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.r
sc|r 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.r
.c|. 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|..
sc|r 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|..
.c|. 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">.s|.r
.s|. 
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">..|..
.s|. 
</pre>




```python
## example of good parity dual orbit

dO, rtype = (13,11,5,5,5,5,3,3,1,1),'D' 
display(lt(r'Let $\mathcal O^\vee$ has rows $%s$'%(list(dO),)))
O = dualBVW(dO,rtype,partrc='c')
display(lt(r'Then $\mathcal O$ has columns $%s$'%(O,)))
Wrepns = springer_part2family(dO,rtype)
WrepnsB = dualpart2Wrepn(dO,rtype)
Wrepns, WrepnsB = set(Wrepns), set(WrepnsB)
#print(Wrepns, len(Wrepns))
print(WrepnsB, len(WrepnsB))
print("WrepnB is a subset of Wrepns by Springer theory:", WrepnsB.issubset(Wrepns))


AdrcSp = dpart2drc(dO,rtype)
print(len(AdrcSp))

AdrcSp = dpart2pbp(dO,rtype)
print(len(AdrcSp))

```


Let $\mathcal O^\vee$ has rows $[13, 11, 5, 5, 5, 5, 3, 3, 1, 1]$



Then $\mathcal O$ has columns $[14, 10, 6, 5, 5, 4, 4, 2, 2]$



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="font-weight: bold">{</span>
    <span style="font-weight: bold">((</span><span style="color: #000080; font-weight: bold">7</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">5</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))</span>,
    <span style="font-weight: bold">((</span><span style="color: #000080; font-weight: bold">7</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">5</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))</span>,
    <span style="font-weight: bold">((</span><span style="color: #000080; font-weight: bold">7</span>, <span style="color: #000080; font-weight: bold">6</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))</span>,
    <span style="font-weight: bold">((</span><span style="color: #000080; font-weight: bold">7</span>, <span style="color: #000080; font-weight: bold">6</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span><span style="font-weight: bold">))</span>,
    <span style="font-weight: bold">((</span><span style="color: #000080; font-weight: bold">7</span>, <span style="color: #000080; font-weight: bold">6</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))</span>,
    <span style="font-weight: bold">((</span><span style="color: #000080; font-weight: bold">7</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">5</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span><span style="font-weight: bold">))</span>,
    <span style="font-weight: bold">((</span><span style="color: #000080; font-weight: bold">7</span>, <span style="color: #000080; font-weight: bold">6</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))</span>,
    <span style="font-weight: bold">((</span><span style="color: #000080; font-weight: bold">7</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">5</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))</span>
<span style="font-weight: bold">}</span>
<span style="color: #000080; font-weight: bold">8</span>
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">WrepnB is a subset of Wrepns by Springer theory: <span style="color: #00ff00; font-style: italic">True</span>
</pre>



    Type D dual-partition: (13, 11, 5, 5, 5, 5, 3, 3, 1, 1)
    [1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024]
    Number of drc diagrams: 8192



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="color: #000080; font-weight: bold">8192</span>
</pre>



    Type D partition: (13, 11, 5, 5, 5, 5, 3, 3, 1, 1)
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1024, 1024, 0, 1024, 1024, 0, 0, 0, 0, 0, 1024, 1024, 0, 1024, 1024, 0, 0, 0, 0, 0, 0]
    Number of drc diagrams: 8192



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="color: #000080; font-weight: bold">8192</span>
</pre>




```python
## example of good parity dual orbit

dO, drtype = (6,6,4,4,4,4,4,2,2,2),'C' 
display(lt(r'Let $\mathcal O^\vee$ has rows $%s$'%(list(dO),)))
O = dualBVW(dO,rtype,partrc='c')
display(lt(r'Then $\mathcal O$ has columns $%s$'%(O,)))
Wrepns = springer_part2family(dO,rtype)
WrepnsB = dualpart2Wrepn(dO,rtype)
Wrepns, WrepnsB = set(Wrepns), set(WrepnsB)
#print(Wrepns, len(Wrepns))
print(WrepnsB, len(WrepnsB))
print("WrepnB is a subset of Wrepns by Springer theory:", WrepnsB.issubset(Wrepns))


AdrcSp = dpart2drc(dO,rtype)
print(len(AdrcSp))

AdrcSp = dpart2pbp(dO,rtype)
print(len(AdrcSp))

```


Let $\mathcal O^\vee$ has rows $[6, 6, 4, 4, 4, 4, 4, 2, 2, 2]$



Then $\mathcal O$ has columns $[6, 6, 4, 4, 4, 4, 4, 2, 2, 2]$



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="font-weight: bold">{((</span><span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))</span>, <span style="font-weight: bold">((</span><span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))}</span>
<span style="color: #000080; font-weight: bold">2</span>
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">WrepnB is a subset of Wrepns by Springer theory: <span style="color: #ff0000; font-style: italic">False</span>
</pre>



    Type D dual-partition: (6, 6, 4, 4, 4, 4, 4, 2, 2, 2)
    [304, 304]
    Number of drc diagrams: 608



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="color: #000080; font-weight: bold">608</span>
</pre>



    Type D partition: (6, 6, 4, 4, 4, 4, 4, 2, 2, 2)
    [0, 4]
    Number of drc diagrams: 4



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="color: #000080; font-weight: bold">4</span>
</pre>




```python
## example of good parity dual orbit

dO, drtype = (6,6,4,4,4,4,4,2,2,2),'C' 
display(lt(r'Let $\mathcal O^\vee$ has rows $%s$'%(list(dO),)))
O = dualBVW(dO,rtype,partrc='c')
display(lt(r'Then $\mathcal O$ has columns $%s$'%(O,)))
Wrepns = springer_part2family(dO,rtype)
WrepnsB = dualpart2Wrepn(dO,rtype)
Wrepns, WrepnsB = set(Wrepns), set(WrepnsB)
#print(Wrepns, len(Wrepns))
print(WrepnsB, len(WrepnsB))
print("WrepnB is a subset of Wrepns by Springer theory:", WrepnsB.issubset(Wrepns))


AdrcSp = dpart2drc(dO,rtype)
print(len(AdrcSp))

AdrcSp = dpart2pbp(dO,rtype)
print(len(AdrcSp))

```


Let $\mathcal O^\vee$ has rows $[6, 6, 4, 4, 4, 4, 4, 2, 2, 2]$



Then $\mathcal O$ has columns $[6, 6, 4, 4, 4, 4, 3, 3, 2, 2]$



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="font-weight: bold">{((</span><span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))</span>, <span style="font-weight: bold">((</span><span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))}</span>
<span style="color: #000080; font-weight: bold">2</span>
</pre>




<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace">WrepnB is a subset of Wrepns by Springer theory: <span style="color: #ff0000; font-style: italic">False</span>
</pre>



    Type C dual-partition: (6, 6, 4, 4, 4, 4, 4, 2, 2, 2)
    [216, 216]
    Number of drc diagrams: 432



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="color: #000080; font-weight: bold">432</span>
</pre>



    Type C partition: (6, 6, 4, 4, 4, 4, 4, 2, 2, 2)
    [16, 128]
    Number of drc diagrams: 144



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="color: #000080; font-weight: bold">144</span>
</pre>




```python
## example of bad parity dual orbit of type D

dO, rtype = (6,6,6,6,2,2,2,2),'D' 
display(lt(r'Let $\mathcal O^\vee$ has rows $%s$'%(list(dO),)))
O = dualBVW(dO,rtype,partrc='c')
display(lt(r'Then $\mathcal O$ has columns $%s$'%(O,)))
Wrepns = springer_part2family(dO,rtype)
Wrepns = set(Wrepns)
print(Wrepns, len(Wrepns))
#print("WrepnB is a subset of Wrepns by Springer theory:", WrepnsB.issubset(Wrepns))

AdrcSp = dpart2pbp(dO,rtype)
print(len(AdrcSp))
```


Let $\mathcal O^\vee$ has rows $[6, 6, 6, 6, 2, 2, 2, 2]$



Then $\mathcal O$ has columns $[6, 6, 6, 6, 2, 2, 2, 2]$



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="font-weight: bold">{((</span><span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))}</span>
<span style="color: #000080; font-weight: bold">1</span>
</pre>



    Type D partition: (6, 6, 6, 6, 2, 2, 2, 2)
    [1]
    Number of drc diagrams: 1



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="color: #000080; font-weight: bold">1</span>
</pre>




```python
## example of bad parity dual orbit of type C

dO, drtype, rtype = (5,5,3,3,3,3,3,3,1,1),'C' , 'B'
display(lt(r'Let $\mathcal O^\vee$ has rows $%s$'%(list(dO),)))
O = dualBVW(dO,rtype,partrc='c')
display(lt(r'Then $\mathcal O$ has columns $%s$'%(O,)))
Wrepns = springer_dpart2family(dO,drtype,symbol=False)
Wrepns = set(Wrepns)
print(Wrepns, len(Wrepns))

AdrcSp = dpart2drc(dO,rtype)
print(len(AdrcSp))

AdrcSp = dpart2pbp(dO,rtype)
print(len(AdrcSp))
```


Let $\mathcal O^\vee$ has rows $[5, 5, 3, 3, 3, 3, 3, 3, 1, 1]$



Then $\mathcal O$ has columns $[5, 5, 3, 3, 3, 3, 3, 3, 1, 1, 1]$



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="font-weight: bold">{((</span><span style="color: #000080; font-weight: bold">3</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">)</span>, <span style="font-weight: bold">(</span><span style="color: #000080; font-weight: bold">2</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span>, <span style="color: #000080; font-weight: bold">1</span><span style="font-weight: bold">))}</span>
<span style="color: #000080; font-weight: bold">1</span>
</pre>



    Type B dual-partition: (5, 5, 3, 3, 3, 3, 3, 3, 1, 1)
    [48, 48, 48, 48, 48, 48, 48, 48]
    Number of drc diagrams: 384



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="color: #000080; font-weight: bold">384</span>
</pre>



    Type B partition: (5, 5, 3, 3, 3, 3, 3, 3, 1, 1)
    [1]
    Number of drc diagrams: 1



<pre style="white-space:pre;overflow-x:auto;line-height:normal;font-family:Menlo,'DejaVu Sans Mono',consolas,'Courier New',monospace"><span style="color: #000080; font-weight: bold">1</span>
</pre>




```python

```
