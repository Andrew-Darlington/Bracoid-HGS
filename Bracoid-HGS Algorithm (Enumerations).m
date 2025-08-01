//computes Aut(G,G')
 NumOfAutomorphisms:=function(G)
	A:=AutomorphismGroup(G); ng:=Ngens(A);
	prep,P:=PermutationRepresentation(A);
	//generators of A should correspond to those of P --> we check it:
	assert ng eq Ngens(P) and forall{i: i in [1..ng] | A.i @ prep eq P.i};

	//Computation of automorphisms of G sending Stab(G,1) to itself
	Gprime:=[Stabiliser(G,1)]; //images of Stab(G,1) under automorphisms
	perms:=[[]: i in [1..ng]];  //permutations of Gprime induced by A.i
	j:=1;
	while j le #Gprime do
		S:=Gprime[j];
		for i in [1..ng] do
			im:=(A.i)(S);
			pos:=Position(Gprime,im);
			if pos eq 0 then //new image
				Append(~Gprime,im);
				pos:=#Gprime;
			end if;
			Append(~perms[i],pos);
		end for;
		j:=j+1;
	end while;
	pgp:=sub<Sym(#Gprime) | {Sym(#Gprime)!perms[i]: i in [1..ng]}>;
	act:=hom<P->pgp | perms>;
	Q:=Stabiliser(pgp,1) @@ act;
	return #Q;
end function;

//computes the number of HGSs and SBs of type <N>.
NumOfType := function(N);
	n:=Order(N);
	hol,f:=Holomorph(N);
	N := f(N);
    t := Subgroups(hol:OrderMultipleOf := n, IsTransitive:=true);
	//here we sum by multiplying out by the sizes of the conjugacy classes.
	hgs1:=0;
	hgs2:=0;
	hgs3:=0;
	hgs4:=0;
	sb1:=0;
	sb2:=0;
	sb3:=0;
	for G in t do
		intfields:=#IntermediateSubgroups(G`subgroup,Stabiliser(G`subgroup,1))+2;
		subGst:=0;
		for H in AllSubgroups(N) do
			if G`subgroup subset Normalizer(hol,H) then
				subGst:=subGst+1;
			end if;
		end for;
		if G`order eq n then
			s:=(Order(AutomorphismGroup(G`subgroup)))*(G`length)/(Order(hol)/n);
			hgs1:=hgs1+s;
			hgs2:=hgs2+s;
			sb1:=sb1+1;
			sb2:=sb2+1;
			if intfields eq subGst then
				hgs4:=hgs4+s;
				if Centralizer(SymmetricGroup(n),N) subset G`subgroup then
					hgs3:=hgs3+s;
					sb3:=sb3+1;
				end if;
			end if;
		else
			a:=NumOfAutomorphisms(G`subgroup);
			s:=(a*(G`length))/(Order(hol)/n);
			hgs1:=hgs1+s;
			sb1:=sb1+1;
			if intfields eq subGst then
				hgs4:=hgs4+s;
				if Centralizer(SymmetricGroup(n),N) subset G`subgroup then
					hgs3:=hgs3+s;
					sb3:=sb3+1;
				end if;
			end if;
		end if;
	end for;
	RF1:=recformat<HGS:Integers(),Galois:Integers(),ac : Integers(),bc : Integers()>;
	RF2:=recformat<sbracoids:Integers(),sbraces:Integers(),ac : Integers()>;
	r1:=rec<RF1 | HGS:=hgs1,Galois:=hgs2,ac:=hgs3,bc:=hgs4>;
	r2:=rec<RF2 | sbracoids:=sb1,sbraces:=sb2,ac:=sb3>;
return r1,r2;
end function;


 /*
  MAIN function
  Given a positive integer n, computes the total
  number of HGSs and SBs of degree n.
 */
 NumAll := function(n);
	hgs1 := 0;
	hgs2 := 0;
	hgs3 := 0;
	hgs4 := 0;
	sb1:=0;
	sb2:=0;
	sb3:=0;
	k:=1;
	for N in SmallGroups(n) do
		hgs,sb:=NumOfType(N);
		hgs1:=hgs1+hgs`HGS;
		hgs2:=hgs2+hgs`Galois;
		hgs3:=hgs3+hgs`ac;
		hgs4:=hgs4+hgs`bc;
		sb1:=sb1+sb`sbracoids;
		sb2:=sb2+sb`sbraces;
		sb3:=sb3+sb`ac;
		type:="<" cat IntegerToString(n) cat "," cat IntegerToString(k) cat ">";
		RF1:=recformat<type,HGS:Integers(),Galois:Integers(),ac : Integers(), bc : Integers()>;
		RF2:=recformat<type,sbracoids:Integers(),sbraces:Integers(),ac : Integers()>;
		r1:=rec<RF1 | type:=type,HGS:=hgs`HGS,Galois:=hgs`Galois,ac:=hgs`ac, bc:=hgs`bc>;
		r2:=rec<RF2 | type:=type,sbracoids:=sb`sbracoids,sbraces:=sb`sbraces,ac:=sb`ac>;
		print r1;
		print r2;
		k:=k+1;
	end for;
return "In total, there are ",hgs1," HGS on separable extensions of degree ",n,". ",hgs2," Galois, and ",hgs3," a.c. ",hgs4," give bijective correspondence. There are also ",sb1," skew bracoids of degree ",n,". ",sb2," skew braces, and ",sb3," a.c.";
end function;