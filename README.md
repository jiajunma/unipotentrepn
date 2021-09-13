# GFM url syntax
# https://render.githubusercontent.com/render/math?math={math_equation}
# equation syntax
F=P(1%2B\frac{i}{n})^{nt}            # normal, valid
\large F=P(1%2B\frac{i}{n})^{nt}     # large: before encoding spaces, invalid
%5Clarge%20F=P(1%2B\frac{i}{n})^{nt} # large: after `%20` space and `%5C` backslash/reverse solidus `\` encoding, valid
\large+F=P(1%2B\frac{i}{n})^{nt}     # large: after `+` space encoding, valid
# e.g. https://render.githubusercontent.com/render/math?math=e%5E%7Bi%5Cpi%7D%20%3D%20-1
#
# CodeCogs url syntax
# https://latex.codecogs.com/svg.latex?{math_equation}
# equation syntax
F=P(1+\frac{i}{n})^{nt}            # normal, valid
\large F=P(1+\frac{i}{n})^{nt}     # large: before encoding spaces, invalid
%5Clarge%20=P(1+\frac{i}{n})^{nt}  # large: after `%20` space and `%5C` backslash/reverse solidus `\` encoding, valid
# e.g. https://latex.codecogs.com/svg.latex?%5Clarge%20F=P(1+\frac{i}{n})^{nt}

# unipotentrepn
Unipotent representations of classical groups
