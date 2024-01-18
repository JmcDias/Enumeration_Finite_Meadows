LoadPackage("semi");
LoadPackage("smallsemi");
LoadPackage("digraphs");

# Checks if a Partition lst is admissible
admissible_partition_checker := function(lst)
	local i,j, n,allGcdGreaterThan1; 
    n := Length(lst);
	
    for i in [1..n] do
        allGcdGreaterThan1 := true;
        for j in [1..n] do
        if i <> j  then
		if IsSubsetSet( PrimeDivisors(lst[i]), PrimeDivisors(lst[j]) ) = false  then
			allGcdGreaterThan1 := false;
            break;
		fi;fi;od;
		
        if allGcdGreaterThan1 then
            return true;
        fi;
    od;
    return false;
end;

# Checks if there is a meadow associated with a Labelled Lattice
is_meadow:= function (p,mult,perm)
	local i,j, status;
	
	status:= true;
	for i in [2 .. Size(p)] do
	for j in [2 .. Size(p)] do 
	if mult[OnPoints(i,perm)][OnPoints(j,perm)] = OnPoints(i,perm) and IsSubsetSet( PrimeDivisors(p[j]), PrimeDivisors(p[i]) )= false then
		status := false;
		break;
	fi;od;od;

	if status then
		return true;
	else
		return false;
	fi;
end;

# Checks if the perm defines an isomophism of Labelled Lattices
is_isomorphic:=function(m,part,mult,perm)
	local is_isomorph,i,j,n;
	is_isomorph := true;
	
	n:= Size(mult);
	
	if m[2]= mult and m[1]=Permuted(part,perm) then
		for i in [1 .. n] do 
		for j in [1 .. n] do 
			if mult[i][j]=j and mult[OnPoints(i,perm)][OnPoints(j,perm)]<>OnPoints(j,perm) then
				is_isomorph:=false;
				break;
			fi;
			if mult[i][j]<>j and mult[OnPoints(i,perm)][OnPoints(j,perm)]=OnPoints(j,perm) then
				is_isomorph:=false;
				break;
			fi;	
		od;od;
	else
		is_isomorph:=false;
	fi;
	
	if is_isomorph then
		return true;
	else
		return false;
	fi;
	
end;

# Checks if there is a Labelled Lattice isomorphic in the set 
isomorph:= function(meadow,part,mult)
	local n,pe,m,iso;
	n:= Size(mult);
	iso:= false;
	
	for m in meadow do
		if m[2][Size(m[2])]=part[Size(part)]then
			break;
		fi;
		for pe in SymmetricGroup([1 .. n]) do
			if is_isomorphic(m,part,mult,pe) then
				iso:= true;
				return false;
			fi;
		od;
	od;
	
	if iso=false then
		return true;
	else
		return false;
	fi;
end;

# Given a Semigroups returns the order relation defined by x<y if xy=x
SemigroupToEdges:=function(mult)
    local edges, n, i, j, k;
    edges := [];
    n := Size(mult);

    for i in [1..n] do
    for j in [1..n] do
	if mult[i][j] = j and i<>j then
				Add(edges, [i, j]);
	fi;od;od;
	
    return edges;
end;

# Returns the minimal generating set for a given relation
RemoveRedundantPairs := function(L)
    local toRemove, i, j, k;
    toRemove := [];

    for i in [1..Length(L)] do
    for j in [1..Length(L)] do
    if i <> j and L[i][2] = L[j][2] then
    for k in [1..Length(L)] do
    if k <> i and k <> j and L[i][1] = L[k][2] and L[j][1] = L[k][1] then
        Add(toRemove, L[j]);
    fi;od;fi;od;od;

    return Filtered(L, el -> not el in toRemove);
end;

# Returns all the Labelled Lattices with label p
lattrings := function(p)
	local i,j,k,Ring,total,new_total,Rin,R;
	total := [[[1,1]]];
	
	for j in [2 .. Size(p)] do
		new_total := [];
		for Ring in total do
			for k in [1 .. NumberSmallRings(p[j])] do
				R := SmallRing(p[j],k);
				if One(R)<> fail and IsCommutative(R) then
					Rin := ShallowCopy(Ring);
					Add(Rin,[p[j],k]);
					Add(new_total,Rin);
				fi;
			od;
		od;
		total:= new_total;
	od;
	return total;
end;

# Returns all the Ring Homomorphisms between rings A and B
morphism_rings:= function(A,B)
		local x,y,morphisms,n;
		morphisms:=[];
		
		if Size(A)=1 and Size(B)=1 then
			return [IdentityMapping( A )];
		fi;
		
		if Size(GeneratorsOfRing(A)) = 1 then
			if Size(Elements(B))=1 then
				return [RingHomomorphismByImages( A, B, [One(A)], [Elements(B)[1]] )];
			fi;
			if RingHomomorphismByImages( A, B, [One(A)], [One(B)] ) <> fail then
				Add(morphisms,RingHomomorphismByImages( A, B, [One(A)], [One(B)] ));
			fi;
		fi;
		
		if Size(GeneratorsOfRing(A)) = 2 then
			if Size(Elements(B))=1 then
				return [RingHomomorphismByImages( A, B, [One(A),GeneratorsOfRing(A)[2]], [Elements(B)[1],Elements(B)[1]] )];
			fi;
			for x in Elements(B) do
				if RingHomomorphismByImages( A, B, [One(A),GeneratorsOfRing(A)[2]], [One(B),x] ) <> fail then
					Add(morphisms,RingHomomorphismByImages( A, B, [One(A),GeneratorsOfRing(A)[2]], [One(B),x] ));
				fi;
			od;
		fi;
		
		if Size(GeneratorsOfRing(A)) = 3 then
			if Size(Elements(B))=1 then
				return [RingHomomorphismByImages( A, B, [One(A),GeneratorsOfRing(A)[2],GeneratorsOfRing(A)[3]], [Elements(B)[1],Elements(B)[1],Elements(B)[1]] )];
			fi;
			for x in Elements(B) do
				for y in Elements(B) do
				if RingHomomorphismByImages( A, B, [One(A),GeneratorsOfRing(A)[2],GeneratorsOfRing(A)[3]], [One(B),x,y] ) <> fail then
					Add(morphisms,RingHomomorphismByImages( A, B, [One(A),GeneratorsOfRing(A)[2],GeneratorsOfRing(A)[3]], [One(B),x,y] ));
				fi;
			od;
			od;
		fi;
	return morphisms;
end;

# Checks if there is a homomorphism between any two related elements
morphisms_sort:=function(edges,m)
	local e;
	for e in edges do
		if e[2] <> 1 then
			if morphism_rings(m[e[1]],m[e[2]])=[] then
				return false;
			fi;
		fi;
	od;
	return true;
	
end;

# Returns all Directed Lattices of Rings even if they not commute
edges_to_morphism := function(edges,rings)
	local morphisms, new_morphisms,m,hom,i,m_shallow;
	morphisms := [morphism_rings(rings[2],rings[1])];
	for i in [2 .. Size(edges)] do
		new_morphisms:=[];
		for m in morphisms do 
			for hom in morphism_rings(rings[edges[i][1]],rings[edges[i][2]]) do
				m_shallow := ShallowCopy(m);
				Add(m_shallow,hom);
				Add(new_morphisms,m_shallow);
			od;
		od;
		morphisms:=new_morphisms;
	od;
	return morphisms;
end;

# Checks if the Directed Lattices are in fact commutative diagrams
check_composition := function(edges,hom,mring)
	local e,f,k,status,a,b,c;
	for e in [1 .. Size(edges)] do
	for f in [1 .. Size(edges)] do
		if edges[e][2]=edges[f][1] and [edges[e][1],edges[f][2]] in edges and edges[f][2]<>1  then
			k := Position(edges,[edges[e][1],edges[f][2]]);
			a:=hom[f];
			b:=hom[e];
			c:=hom[k];

			if b*a <> c then
				return false;
			fi;
		fi;
		
		if edges[e][2]=edges[f][1] and [edges[e][1],edges[f][2]] in edges and edges[f][2]<>1 and Range(hom[e]) <> Source(hom[f]) then		
			return false;
		fi;
	od;od;
	return true;
end;

# Checks if a given function is an isomorphism
bijec:=function(f)
	local ker,image,e;
	ker:=[];
	image:=[];
	for e in Elements(Source(f)) do
		if f(e)= Zero(Range(f)) then
			Add(ker,e);;
		fi;
		Add(image,f(e));;
	od;
	image:=List(Set(image), x -> x);;
	if Size(ker) = 1 and Size(image)=Size(Range(f)) then
		return true;
	else
		return false;
	fi;
end;

# Checks if two directed lattices are isomorphic
meadow_isomorphism := function(mm1,p1,edges1,mm2,p2,edges2)
	local status,mring,iso,morphism,set_iso,isomorfismo,set_iso1,isomorfismo1,status2,i,f1,f2,g1,g2,id1,id2;
	status := true;
	set_iso:=[];

	if edges1= edges2 then
	if mm1=mm2 then
		mring:=List(mm1,x->SmallRing(x[1],x[2]));
		set_iso:=[[MappingByFunction(SmallRing(1,1),SmallRing(1,1),x->x)]];
		for i in [2 .. Size(mring)] do 
			set_iso1:=[];
			for isomorfismo in set_iso do
				for morphism in morphism_rings(mring[i],mring[i]) do
					if bijec(morphism) then
						isomorfismo1:=ShallowCopy(isomorfismo);
						Add(isomorfismo1,morphism);
						Add(set_iso1,isomorfismo1);
					fi;
				od;	
			od;
			set_iso:=set_iso1;
		od;

		for isomorfismo in set_iso do
			status2:= true;
			for i in [1 .. Size(edges1)] do
				
				id1:=MappingByFunction(Range(p1[i]),Source(isomorfismo[edges1[i][2]]),Elements(Range(p1[i])),Elements(Source(isomorfismo[edges1[i][2]])) );
				id2:=MappingByFunction(Range(isomorfismo[edges2[i][1]]),Source(p2[i]),Elements(Range(isomorfismo[edges2[i][1]])),Elements(Source(p2[i])) );

				if p1[i]*id1*isomorfismo[edges1[i][2]]  <>  isomorfismo[edges2[i][1]]*id2*p2[i] then
					status2:=false;
					break;
				fi;
				
			od;
			if status2=false then
			status:= false;
			break;
			fi;
			
		od;
		
	fi;fi;
	
	if status then
		return true;
	else
		return false;
	fi;	
end;
#------------------------------------------------------------------------
enumeration_meadows:=function(n,splash)
	local meadow,mead,p,S,perm,pp,part,edges,edges_simple,m,digraph,Ms,Mss,i,si,counter,listt,mm,prov,mring,isomorphism;
	meadow:= [];
	Print("----------Partitions ",n," ----------\n");
	part := Partitions(n-1);
	
	for p in part do
	if ForAll(p, x -> x <> 1) and admissible_partition_checker(p)then
		Add(p,1,1);
		si:=Size(p)-1;
		for S in  AllSmallSemigroups(si,IsCommutative,true) do
		if IsBand(S) then
	
		Mss := MultiplicationTable(S);
		Ms:=ShallowCopy(Mss);
		for i in [1..si] do    
			 Ms[i] := Concatenation(Ms[i], [i]);
		od;
		Ms := Concatenation(Ms, [[1..si+1]]);
		if ForAll([2..Length(p)-1], i -> p[i] = p[i+1]) then
			Add(meadow,[p,Ms]);		
		else
			pp:=p;
			for perm in SymmetricGroup([1 .. Size(p)]) do
				if is_meadow(p,Ms,perm) and OnPoints(1,perm)=1 then
					prov:=pp;
					pp := Permuted (p,perm);
					if perm = () then
						Add(meadow,[pp,Ms]);
					else
						if prov<>pp then
							if isomorph(meadow,pp,Ms) then
								Add(meadow,[pp,Ms]);
							fi;
						fi;						
					fi;	
				fi;
			od;
		fi;
		fi;od;
	fi;od;
		
	mead:=List(Set(meadow), x -> x);;
	meadow:= [];
	for m in mead do
		edges := SemigroupToEdges(m[2]);
		edges_simple:=RemoveRedundantPairs(edges);
		listt:=lattrings(m[1]);
		
		for mm in listt do
			mring:=List(mm,x->SmallRing(x[1],x[2]));
			if morphisms_sort(edges_simple,mring) then
				for p in edges_to_morphism(edges,mring) do
					if check_composition(edges,p,mring) then
						isomorphism:= true;
						for pp in meadow do 
							if meadow_isomorphism(mm,p,edges,pp[1],pp[2],pp[3]) = false then
								isomorphism:= false;
							fi;
						od;
						if isomorphism then
							Add(meadow,[mm,p,edges]);

						if splash=true then
							digraph := DigraphByEdges(edges_simple);
							SetDigraphVertexLabels(digraph,mm);
							Splash(DotVertexLabelledDigraph(digraph));
						fi;
						fi;
					fi;
				od;
			fi;
		od;
	od;
	
	Print(Size(meadow),"\n");
	return meadow;
end;
