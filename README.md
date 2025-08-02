# Bracoid-HGS
Two (MAGMA) algorithms for classifying and enumerating Hopf-Galois structures and skew bracoids of low degree. The main function for both algorithms is NumAll.

-----------------------------------------------------------------------------------------------------------------
## Bracoid-HGS Algorithm (Enumerations).m

Given an integer n, outputs the number of Hopf-Galois structures (HGSs) on separable extensions of dgeree n (of each type) and the number of skew bracoids (SBs) of degree n (of each type). The number of almost classical structures as well as the number of HGSs giving bijective correspondence is also given.

Here is a sample output:
```
  rec<RF1 |
    type := <2,1>,
    HGS := 1,
    Galois := 1,
    ac := 1,
    bc := 1>
rec<RF2 |
    type := <2,1>,
    sbracoids := 1,
    sbraces := 1,
    ac := 1>
In total, there are  1  HGS on separable extensions of degree  2 .  1  Galois,
and  1  a.c.  1  give bijective correspondence. There are also  1  skew bracoids
of degree  2 .  1  skew braces, and  1  a.c.
```

The first record tells us that there is 1 HGS of type <2,1> (the cyclic group of order 2). It is admitted by a Galois extension (of degree 2), it is almost classically Galois, and hence also gives a bijective correspondence.
The second record tells us that there is 1 skew bracoid of type <2,1>. It is essentially a skew brace and almost classical.

-----------------------------------------------------------------------------------------------------------------
## Bracoid-HGS Algorithm (Structures).m

Given an integer n, outputs a list of equivalence classes[^1] of transitive permutation groups G of degree n which
- arise as the Galois group of the Galois closure of an extension of degree n admitting a Hopf-Galois structure
- arise as the 'multiplicative group' of a (family of) skew bracoid(s) of degree n
The number of corresponding HGSs and SBs are given for each type that is admitted.

[^1]: two permutation groups G1 and G2 are equivalent if there is an isomorphism a:G1->G2 such that a(G1')=G2', where the prime denotes the stabiliser of the identity of the action. This is needed for classifying HGSs, and is kept as a convenience for the SBs (two isomorphic skew bracoids have equivalent permutation groups).

Here is a sample output:
```
[
    rec<recformat<classsize, isomtype, permID, Gsol, structures> |
        classsize := 1,
        isomtype := <2, 1>,
        permID := 1,
        Gsol := true,
        structures := [
            rec<recformat<group, numgrps, HGS, SB, type> |
                group := Symmetric group acting on a set of cardinality 2
                Order = 2
                    (1, 2),
                numgrps := 1,
                HGS := rec<recformat<total, Gal, AC, BC> |
                    total := 1,
                    Gal := 1,
                    AC := 1,
                    BC := 1>,
                SB := rec<recformat<total, Sbrace, AC> |
                    total := 1,
                    Sbrace := 1,
                    AC := 1>,
                type := rec<recformat<IDtype, Nsol> |
                    IDtype := <2,1>,
                    Nsol := true>>
        ]>
]
```
Additional information is given such as the ID of G as an abstract group, and also as a transitive permutation group. MAGMA also checks whether each G and N is solvable.


