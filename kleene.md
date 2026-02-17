NAME
Kleene's Algorithm - the theory behind it
brief introduction

DESCRIPTION
Semi-Rings
A Semi-Ring (S, +, ., 0, 1) is characterized by the following properties:
) a) (S, +, 0) is a Semi-Group with neutral element 0
b) (S, ., 1) is a Semi-Group with neutral element 1

c) 0 . a = a . 0 = 0 for all a in S

) "+" is commutative and idempotent, i.e., a + a = a
) Distributivity holds, i.e.,
a) a . ( b + c ) = a . b + a . c for all a,b,c in S

b) ( a + b ) . c = a . c + b . c for all a,b,c in S

) SUM_{i=0}^{+infinity} ( a[i] )
exists, is well-defined and unique

for all a[i] in S

and associativity, commutativity and idempotency hold

) Distributivity for infinite series also holds, i.e.,
  ( SUM_{i=0}^{+infty} a[i] ) . ( SUM_{j=0}^{+infty} b[j] )
  = SUM_{i=0}^{+infty} ( SUM_{j=0}^{+infty} ( a[i] . b[j] ) )
EXAMPLES:
S1 = ({0,1}, |, &, 0, 1)
Boolean Algebra

See also MatrixBool(3)

S2 = (pos. reals with 0 and +infty, min, +, +infty, 0)
Positive real numbers including zero and plus infinity

See also MatrixReal(3)

S3 = (Pot(Sigma*), union, concat, {}, {''})
Formal languages over Sigma (= alphabet)

See also Kleene(3)

Operator '*'
(reflexive and transitive closure)
Define an operator called ``*'' as follows:

    a in S   ==>   a*  :=  SUM_{i=0}^{+infty} a^i
where

    a^0  =  1,   a^(i+1)  =  a . a^i
Then, also

    a*  =  1 + a . a*,   0*  =  1*  =  1
hold.

Kleene's Algorithm
In its general form, Kleene's algorithm goes as follows:
    for i := 1 to n do
        for j := 1 to n do
        begin
            C^0[i,j] := m(v[i],v[j]);
            if (i = j) then C^0[i,j] := C^0[i,j] + 1
        end
    for k := 1 to n do
        for i := 1 to n do
            for j := 1 to n do
                C^k[i,j] := C^k-1[i,j] +
                            C^k-1[i,k] . ( C^k-1[k,k] )* . C^k-1[k,j]
    for i := 1 to n do
        for j := 1 to n do
            c(v[i],v[j]) := C^n[i,j]
Kleene's Algorithm and Semi-Rings
Kleene's algorithm can be applied to any Semi-Ring having the properties listed previously (above). (!)
EXAMPLES:

S1 = ({0,1}, |, &, 0, 1)
G(V,E) be a graph with set of vortices V and set of edges E:

m(v[i],v[j]) := ( (v[i],v[j]) in E ) ? 1 : 0

Kleene's algorithm then calculates

c^{n}_{i,j} = ( path from v[i] to v[j] exists ) ? 1 : 0

using

C^k[i,j] = C^k-1[i,j] | C^k-1[i,k] & C^k-1[k,j]

(remember

 0*  =  1*  =  1 
)
S2 = (pos. reals with 0 and +infty, min, +, +infty, 0)
G(V,E) be a graph with set of vortices V and set of edges E, with costs m(v[i],v[j]) associated with each edge (v[i],v[j]) in E:

m(v[i],v[j]) := costs of (v[i],v[j])

for all (v[i],v[j]) in E

Set m(v[i],v[j]) := +infinity if an edge (v[i],v[j]) is not in E.


  ==E<gt>  a* = 0  for all a in S2

  ==E<gt>  C^k[i,j]  =  min( C^k-1[i,j] ,

           C^k-1[i,k]  +  C^k-1[k,j] )
Kleene's algorithm then calculates the costs of the ``shortest'' path from any v[i] to any other v[j]:

C^n[i,j] = costs of "shortest" path from v[i] to v[j]

S3 = (Pot(Sigma*), union, concat, {}, {''})
M in DFA(Sigma) be a Deterministic Finite Automaton with a set of states Q, a subset F of Q of accepting states and a transition function delta : Q x Sigma --> Q.

Define

m(v[i],v[j]) :=


    { a in Sigma | delta( q[i] , a ) = q[j] }
and

C^0[i,j] := m(v[i],v[j]);

if (i = j) then C^0[i,j] := C^0[i,j] union {''}

({''} is the set containing the empty string, whereas {} is the empty set!)

Then Kleene's algorithm calculates the language accepted by Deterministic Finite Automaton M using

C^k[i,j] = C^k-1[i,j] union


    C^k-1[i,k] concat ( C^k-1[k,k] )* concat C^k-1[k,j]
and

L(M) = UNION_{ q[j] in F } C^n[1,j]

(state q[1] is assumed to be the ``start'' state)

finally being the language recognized by Deterministic Finite Automaton M.

Note that instead of using Kleene's algorithm, you can also use the ``*'' operator on the associated matrix:
Define A[i,j] := m(v[i],v[j])


  ==E<gt>   A*[i,j]  =  c(v[i],v[j])
Proof:

A* = SUM_{i=0}^{+infty} A^i

where A^0 = E_{n}

(matrix with one's in its main diagonal and zero's elsewhere)

and A^(i+1) = A . A^i

Induction over k yields:

A^k[i,j] = c_{k}(v[i],v[j])

k = 0:
c_{0}(v[i],v[j]) = d_{i,j}
with d_{i,j} := (i = j) ? 1 : 0

and A^0 = E_{n} = [d_{i,j}]

k-1 -gt k:
c_{k}(v[i],v[j])
= SUM_{l=1}^{n} m(v[i],v[l]) . c_{k-1}(v[l],v[j])

= SUM_{l=1}^{n} ( a[i,l] . a[l,j] )

= [a^{k}_{i,j}] = A^1 . A^(k-1) = A^k

qed
In other words, the complexity of calculating the closure and doing matrix multiplications is of the same order O( n^3 ) in Semi-Rings!

SEE ALSO
Math::MatrixBool(3), Math::MatrixReal(3), DFA::Kleene(3).
(All contained in the distribution of the ``Bit::Vector'' module, formerly named ``Set::IntegerFast'')

Dijkstra's algorithm for shortest paths.

AUTHOR
This document is based on lecture notes and has been put into POD format by Steffen Beyer .
COPYRIGHT
Copyright (c) 1997 by Steffen Beyer. All rights reserved.


Square Matrices over Kleene Algebras
There is a natural way of defining a Kleene algebra K = (Mn, +, ·,∗ , 0, 1) over Mn, where
Mn is the set of all n × n-matrices with elements in some Kleene algebra K. To do this,
simply define + as the usual matrix addition, · as standard matrix multiplication, 0 as
the zero matrix and 1 as the identity matrix.
As for the star operator, in the case of 1 × 1-matrices the definition is trivial, namely,
(a)∗ = (a∗). For larger matrices, consider the following automaton [9]
9
1 2
b
a
c
d
Figure 1: An automaton with two states over the alphabet Σ = {a, b, c, d}.
and the matrix, E =
[a b
c d
]
, where a, b, c and d are elements of a Kleene algebra. For
each pair u, v of states in the automaton depicted in Figure 1, consider the set of inputs
that takes state u to state v. These sets can be represented by the following regular
expressions:
1 −→ 1 : (a + bd∗c)∗
1 −→ 2 : (a + bd∗c)∗bd∗
2 −→ 1 : d∗c(a + bd∗c)∗
2 −→ 2 : d∗ + d∗c(a + bd∗c)∗bd∗
Let f = a + bd∗c, then we define:
E∗ =
[ f ∗ f ∗bd∗
d∗cf ∗ d∗ + d∗cf ∗bd∗
]
If E is of a larger dimension, say n×n, where n > 2, then we define the star operation
by partitioning E into submatrices A, B, C and D, such that A and D are square.
[ A B
C D
]
Let F = A + BD∗C and define
E∗ =
[ F ∗ F ∗BD∗
D∗CF ∗ D∗ + D∗CF ∗BD∗
]
(16)
With this definition E∗ satisfies the axioms concerning the Kleene star [1].
This means that square matrices over a Kleene algebra themselves form a Kleene
algebra together with the above operations
qute://pdfjs/web/viewer.html?filename=tmp68wmok37_FULLTEXT01.pdf&file=&source=https://www.diva-portal.org/smash/get/diva2:690270/FULLTEXT01.pdf
