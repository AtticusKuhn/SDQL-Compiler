Let `V` be a semi-module over `k`.
Let `B : V * V -> K` be a bilinear form

`V ⊗ V` is a semi-ring, where multiplication is given by
$$(a \otimes b) * (x \otimes y) = B(b, x) \cdot (a \otimes y)$$.

All semi-modules in SDQL have a bilinear form.

For dictionary 
`B(f,g) = sum_{k in f} f(k) * g(k)`
For record
`B(<f1, f2, ..., fn>,  <g1, g2, ..., gn>) = B1(f1,g1) + B2(f2,g2) + ... + Bn(fn, gn)`.


Example: `{int -> real}` is a semi-module over `real`,
so ` {int -> real} ⊗ {int -> real} = {int -> int -> real}` is a semi-ring.
The multiplication in this semi-ring is given by
`(f * g)(i)(j) = sum_{k in g} f(i)(k) * g(k)(j)`

Note that multiplication distributes over addition, so 

$$
(a \otimes b + c \otimes d) * (x \otimes y) 
= (a \otimes b) * (x \otimes y) + (c \otimes d) * (x \otimes y) 
= B(b, x) \cdot (a \otimes y) + B(d, x) \cdot (c \otimes y)
$$.

$$
(a \otimes b + c \otimes d) * (x \otimes y + w \otimes z) 
= (a \otimes b) * (x \otimes y) + (c \otimes d) * (x \otimes y) + (a \otimes b) * (w \otimes z) + (c \otimes d) * (w \otimes z) 
= B(b, x) \cdot (a \otimes y) + B(d, x) \cdot (c \otimes y) + B(b, w) \cdot (a \otimes z) + B(d, w) \cdot (c \otimes z)
$$.

So, we may implement this if we have a function `decompose : V ⊗ V -> List (V * V)`. Apparently, optimal tensor
decomposition is difficult, but we can just do suboptimal tensor decomposition for now.

For example: if `V = R^2, c = R`, then 
`decompose(<<1,2>, <3,4>>) = [(<1,0>, <1, 0>), (<0,1>, <2,0>), (<3, 0>, <0,1>), (<4,0>, <0,1>)]`
