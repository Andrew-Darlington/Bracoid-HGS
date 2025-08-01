//given a transitive subgroup G, returns |Aut(G,G')| along with the list of images of G' under Aut(G) 	
NumOfAutomorphisms:=function(G);
	A:=AutomorphismGroup(G);
	ng:=Ngens(A);
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
	return #Q,Gprime;
end function;


/*
* given an integer n, outputs a list of all transitive subgroups G (of Hol(N) for each N) with the following data:
* - the set of images of G' under Aut(G)
* - |Aut(G,G')|
* - the number of (transitive) subgroups conjugate to G
* - whether G is a regular subgroup
* - whether G corresponds to an almost classical(ly Galois) structure
* - whether G corresponds to a HGS admitting bijective correspondence
* - the group ID of N, the type, N, admitted by G
* - whether N is solvable
*/
Data:=function(n);
	RFgroup:=recformat<transgroup,stabs,ordaut,numconjugates,reg,AC,BC,Gsol>;
	RFtype:=recformat<IDtype,Nsol>;
	list:=[];
	i:=1;
	for N in SmallGroups(n) do
		Nsolvable:=IsSolvable(N);
		hol,f:=Holomorph(N);
		imN := f(N); //isomorphic image of N in f
		t := Subgroups(hol:OrderMultipleOf := n, IsTransitive:=true);
		for G in t do
			intfields:=#IntermediateSubgroups(G`subgroup,Stabiliser(G`subgroup,1))+2;
			subGst:=0;
			for H in AllSubgroups(imN) do
				if G`subgroup subset Normalizer(hol,H) then
					subGst:=subGst+1;
				end if;
			end for;
			if G`order eq n then
				if intfields eq subGst then
					isBC:=true;
					if Centralizer(SymmetricGroup(n),imN) subset G`subgroup then
						isAC:=true;
					else
						isAC:=false;
					end if;
				else
					isBC:=false;
					isAC:=false;
				end if;
				rgroup:=rec<RFgroup | transgroup:=G`subgroup,stabs:=[PermutationGroup<{1..n} | [] >],ordaut:=Order(AutomorphismGroup(G`subgroup)),numconjugates:=G`length,reg:=true,AC:=isAC,BC:=isBC,Gsol:=IsSolvable(G`subgroup)>;
				rtype:=rec<RFtype | IDtype:="<" cat IntegerToString(n) cat "," cat IntegerToString(i) cat ">",Nsol:=Nsolvable>;
			else
				numaut,stab:=NumOfAutomorphisms(G`subgroup);
				if intfields eq subGst then
					isBC:=true;
					if Centralizer(SymmetricGroup(n),imN) subset G`subgroup then
						isAC:=true;
					else
						isAC:=false;
					end if;
				else
					isBC:=false;
					isAC:=false;
				end if;
				rgroup:=rec<RFgroup | transgroup:=G`subgroup,stabs:=stab,ordaut:=numaut,numconjugates:=G`length,reg:=false,AC:=isAC,BC:=isBC>;
				rtype:=rec<RFtype | IDtype:="<" cat IntegerToString(n) cat "," cat IntegerToString(i) cat ">",Nsol:=Nsolvable>;
			end if;
			Append(~list,[*rgroup,rtype*]);
		end for;
		i:=i+1;
	end for;
	return list;
end function;

//sorts the transitive subgroups into permutation isomorphism classes
TransEquiv := function(n);
	RF:=recformat<classsize : Integers(),isomtype,permID,Gsol,class>;
	equivclasses:=[];	//list of equivalence classes
	usedgroups:=[]; //groups which have already been sorted into equivalence classes
	D:=Data(n);
	k:=1;
	for G1 in D do
		if Index(usedgroups,k) eq 0 then
			try
				id:=IdentifyGroup(G1[1]`transgroup);
			catch e;
				id:="unknown";
			end try;
			try
				permid:=TransitiveGroupIdentification(G1[1]`transgroup);
			catch e;
				permid:="unknown";
			end try;
			equivclass:=[];
			i:=k;
			s:=0;
			for G2 in [D[j] : j in [k..#D]] do //only need to run from G1 up to end
				if Index(usedgroups,i) eq 0 then
					bool,isom:=IsIsomorphic(G1[1]`transgroup,G2[1]`transgroup);
					if bool then
						if Position(G2[1]`stabs,isom(Stabiliser(G1[1]`transgroup,1))) gt 0 then
							Append(~equivclass,G2);
							Append(~usedgroups,i);
							s:=s+G2[1]`numconjugates;
						end if;
					end if;
				end if;
				i:=i+1;
			end for;
			if #equivclass gt 0 then
				r:=rec<RF | classsize:=s,isomtype:=id,permID:=permid,Gsol:=IsSolvable(G1[1]`transgroup),class:=equivclass>;
				Append(~equivclasses,r);
			end if;
		end if;
		k:=k+1;
	end for;
	return equivclasses; //list of equivalence classes along with size of each one
end function;

//given an equivalence class of transitive permutation groups, returns the number of HGS and skew bracoids of each type
NumOfType := function(n,EquivClass);
	HGS_Sbracoid_list:=[];
	RF1:=recformat<total,Gal,AC,BC>;
	RF2:=recformat<total,Sbrace,AC>;
	RF:=recformat<group,numgrps,HGS,SB,type>;
	j:=1;
	for i in [1..NumberOfSmallGroups(n)] do
		if j le #EquivClass and EquivClass[j][2]`IDtype eq "<" cat IntegerToString(n) cat "," cat IntegerToString(i) cat ">" then
			ordautN := Order(AutomorphismGroup(SmallGroups(n)[i]));
			hgstot:=0;
			hgsgal:=0;
			hgsbc:=0;
			hgsac:=0;
			sbtot:=0;
			sbrace:=0;
			sbac:=0;
			totgrps:=0;
			while j le #EquivClass and EquivClass[j][2]`IDtype eq "<" cat IntegerToString(n) cat "," cat IntegerToString(i) cat ">" do
				totgrps:=totgrps+EquivClass[j][1]`numconjugates;
				hgstot := hgstot + EquivClass[j][1]`numconjugates;
				sbtot := sbtot + 1;
				if EquivClass[j][1]`reg then
					hgsgal := hgsgal + EquivClass[j][1]`numconjugates;
					sbrace := sbrace + 1;
				end if;
				if EquivClass[j][1]`BC then
					hgsbc := hgsbc + EquivClass[j][1]`numconjugates;
					if EquivClass[j][1]`AC then
						hgsac := hgsac + EquivClass[j][1]`numconjugates;
						sbac := sbac + 1;
					end if;
				end if;
				j:=j+1;
			end while;
			ordautG:=EquivClass[j-1][1]`ordaut;
			factor:=ordautG/ordautN;
			r1:=rec<RF1 | total:=(hgstot*factor), Gal:=(hgsgal*factor), AC:=(hgsac*factor), BC:=(hgsbc*factor)>;
			r2:=rec<RF2 | total:=sbtot, Sbrace:=sbrace, AC:=sbac>;
			r:=rec< RF | group:=EquivClass[j-1][1]`transgroup,numgrps:=totgrps,HGS:=r1, SB:=r2, type:=EquivClass[j-1][2]>;
			Append(~HGS_Sbracoid_list,r);
		end if;
	end for;
	return HGS_Sbracoid_list;
end function;

//MAIN function, returns a database of HGSs & SBs of degree n with attached data
NumAll:=function(n);
	RF:=recformat<classsize,isomtype,permID,Gsol,structures>;
	database:=[];
	equivclasses:=TransEquiv(n);
	for c in equivclasses do
		r:=rec<RF | classsize:=c`classsize, isomtype:=c`isomtype, permID:=c`permID, Gsol:=c`Gsol, structures:=NumOfType(n,c`class)>;
		Append(~database,r);
	end for;
	return database;
end function;