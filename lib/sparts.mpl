isSectorValid:= proc(n, mbar, mubar, mbarbar)
	local result, debug;
	#Tells you wether the sector is empty or not
	if n < mbar*(mbar-1)/2 + mubar*(mubar-1)/2 then 
		result:= false;
		debug:= "not enough boxes";
	end if:
	return result;	
end proc:

genN1spart:= proc(n,m)
	local sparts;
	sparts:= genN2spart(n,0, m,0);
	if sparts = [[],[],[],[]] then return [[],[]]; end if;
	sparts:= map(x-> x[3..4], sparts);
	return sparts;
end proc:

isSpartValid:= proc(spart, debug:=0) local spartphi, spartthe, spartzed, spartpt;
	#tells you wether a spart is valid or not. 
	if type(spart, list) <> true then 
		return false; 
	end if;
	if nops(spart) <> 4 then 
			return false; 
		end if; 
		#Some local vars
		spartpt :=  spart[1];
		spartphi:=  spart[2];
		spartthe:=  spart[3];
		spartzed:=  spart[4];
		#Conditions on constituting partitions
		if MakeUnique(sort(spartphi)) <> sort(spartphi) then return false; end if;
		if MakeUnique(sort(spartthe)) <> sort(spartthe) then return false; end if;
		if min(FlattenOnce(spart)) < 0 then return false; end if;
		return true;
end proc:

giveSpartSector:= proc(spart::pN2spart)
		local n, mbar, mubar, mbarbar;
	#Takes a spart and returns the sector
		n := add(k, k in Flatten(spart));
		mbarbar:= nops(spart[1]);
		mbar:= nops(spart[2]);
		mubar:= nops(spart[3]);
		return [n, mbar, mubar, mbarbar];
end proc:

genN2spart:= proc(n, mbar, mubar, mbarbar, mode:=[1,2,3])
	local degreePT, ptSparts, spartPhi, spartThe, spartZed, degreePhi, degreeThe, degreeZed, sparts, newsparts, T, phiSparts, thetaSparts, zedSparts, part_of_n, ones_list;
	#Returns all the spart in a given sector
	#Initializing the number of boxes in each subpart
	sparts:= [];
	degreePT := n -mubar*(mubar-1)/2 - mbar*(mbar-1)/2;
	degreePhi:= n - degreePT;
	degreeThe:= n-degreePhi;
	degreeZed:= 0;
	if degreePT < 0 then return [[],[],[],[]]; end if;
	while degreePT >=0 do
		ptSparts:= partition(degreePT+mbarbar);
		ptSparts:= map(x-> if nops(x) <> mbarbar then NULL; else x; end if, ptSparts); 
		ones_list:= map(x-> [seq(1, j=1..nops(x))], ptSparts);
		ptSparts:= ptSparts - ones_list;
		ptSparts:= map(x-> Reverse(x), ptSparts); 
	
		degreePhi:= n - degreePT;
		while degreePhi >= mbar*(mbar-1)/2 do
			#All the dispart with degreePhi starting High
			phiSparts:=genSpartDist(degreePhi,mbar);

			degreeThe:=n-degreePhi-degreePT;
			while degreeThe >= mubar*(mubar-1)/2 do
				degreeZed:= n - degreePhi - degreeThe -degreePT;

				thetaSparts:= genSpartDist(degreeThe,mubar);
				#zedSparts:= Reverse(partition(degreeZed));
				part_of_n:= partition(degreeZed);
				zedSparts:= map(x-> Reverse(x), part_of_n); 
				#Update the list of sparts
				T:=cartprod([ptSparts, phiSparts, thetaSparts, zedSparts]);
				newsparts:= [];
				while not T[finished] do newsparts:= [op(newsparts),T[nextvalue]()] end do;
				sparts:= [op(sparts), op(newsparts)];
	
				degreeThe:= degreeThe-1;
			end do:
			degreePhi:= degreePhi-1;
		end do:
	degreePT:= degreePT-1; 
	end do:
return(spart_sort(sparts, mode));
end proc:

spart_sort:= proc(sparts, mode:=[1,2,3])
	local scores, k, j, out, perms, dom_score;
	scores:=[];
	for k in sparts do
		dom_score:=add(j, j in map(x->if `<` = sCompareDominance(k, x, mode) then 1; else 0; end if, sparts));
		scores:=[op(scores), dom_score]; 
	end do:
	perms:=sort(scores, output=permutation);
	out:= map(x->sparts[x], perms);
	return out;
end proc:

super_pol_sort:= proc(expr, the_symbol, sector, mode:=[1,2,3])
	local sort_vec;
	sort_vec:= map(x-> the_symbol[op(x)], genN2spart(op(sector), mode)); 
	return sort(expr, sort_vec); 
end proc:

list_sort:= proc(in1, in2)
	if sCompareDominance([op(in1)], [op(in2)]) = `>` then return true; else return false; end if;
end proc:

genSpartDist:=proc(n,ell, debug:=0)
		local part_list, one_list;
	#Generates all the sparts with distinct parts including the zeros
	part_list:= Reverse(partition(n+ell));
	if debug <> 0 then print(part_list); end if;
		part_list:= map(x-> if nops(x) <> ell then NULL; else x; end if, part_list);
	if debug <> 0 then print(part_list); end if;
		part_list:= map(x-> if FindRepetitions(x) <> [] then NULL; else Reverse(x); end if, part_list);
	if debug <> 0 then print(part_list); end if;
	one_list:= map(x-> [seq(1, i=1..(nops(x)))], part_list); 
		#part_list:= map(x-> Reverse(x - [seq(1, i=1..nops(x))]), part_list); 
	part_list:= part_list - one_list; 
		return part_list;
end proc:

switch_notation:= proc(spart, numbering:=a, uniquenum:=0, mode:=[1,2,3])
	local phis, thetas, phithetas, zeds, Lambda, pts, newLambda, counter,k;
	# exchange a spart for the other notation ( [] [] [] ) --> ( 4T, 3C, ...)
	pts := spart[1];
	if nops(spart[1])<>0 then pts := map(x-> [x, "TC", numbering^(x+1)], pts); end if;
	phis:= spart[2];
	if nops(spart[2])<>0 then phis:= map( x-> [x,"T",numbering^(x)], phis); end if;
	thetas:= spart[3];
	if nops(spart[3])<>0 then thetas:= map(x-> [x,"C", numbering^(x)], thetas); end if;
	zeds:= spart[4];
	if nops(spart[4])<>0 then zeds:= map(x-> [x,"", numbering^(x)], zeds); end if;
	Lambda:= Reverse(sort([op(pts),op(phis), op(thetas), op(zeds)]));
	if uniquenum=0 then
		newLambda:=[];
		counter:=1;
		for k from 1 to nops(Lambda) do
			if (op(2,Lambda[k]) = "T") or (op(2,Lambda[k]) = "C") then
				newLambda:=[op(newLambda), [op(Lambda[k]), numbering[counter]]];
				counter:= counter + 1;
			else
				newLambda:= [op(newLambda), [op(Lambda[k]), numbering]]; 
			end if;
		end do:
		Lambda:=newLambda;
		#Lambda:= map(x-> 
		#if (op(2,Lambda[x]) = "T") or (op(2,Lambda[x]) = "C")  then
		#[op(Lambda[x]), numbering[x]];
		#else
		#[op(Lambda[x]), numbering]; end if, [seq(k, k=1..nops(Lambda))]); 
	else
		Lambda:= map(x-> 
		[op(Lambda[x]), numbering[x]]
		, [seq(k, k=1..nops(Lambda))]); 
	end if;
	if mode <> [1,2,3] then
		Lambda:= sort_switch(Lambda, mode);	
	end if;
	return Lambda;
end proc:

sort_switch:= proc(sw_spart, mode:=[1,2,3])
	local orig, perm, sublist, switched;
	orig:= ["TC", "T", "C"];
	perm:= subs({1="TC", 2="T", 3="C"}, mode);
	sublist:= {perm[1]="C0", perm[2]="B0", perm[3]="A0"};
	switched:= subs(sublist, sw_spart);
	switched:= Reverse(sort(switched)); 
	sublist:= {"C0"=perm[1], "B0"=perm[2], "A0"=perm[3]};
	switched:= subs(sublist, switched); 
	return switched;
end proc:

reverse_notation:= proc(spart)
	local phis, thetas, phithetas, zeds, Lambda;
	phis:= 		Reverse(sort(map(x-> if x[2] = "T" then x[1]; else NULL; end if, spart)));
	thetas:= 	Reverse(sort(map(x-> if x[2] = "C" then x[1]; else NULL; end if, spart)));
	phithetas:= 	Reverse(sort(map(x-> if x[2] = "TC" then x[1]; else NULL; end if, spart)));
	zeds:= 		Reverse(sort(map(x-> if x[2] = "" then x[1]; else NULL; end if, spart)));
	Lambda:=	[phithetas,phis,thetas,zeds];
	return Lambda;
end proc:

#n-tupple aka compositions 
#compositions
compare_bruhat:= proc(composition1, composition2)
	local compart, cumul_part1, cumul_part2, max_length, is1greater2, is1smaller2; 
	# compare the weight of two composition, not really the bruhat order, it's the order defined in Baker, T. H., & Forrester, P. J. (1996). Non-Symmetric Jack Polynomials and Integral Kernels, 33. Quantum Algebra. Retrieved from http://arxiv.org/abs/q-alg/9612003
	compart:= compare_dominance(Reverse(sort(composition1)), Reverse(sort(composition2))); 
	if composition1 = composition2 then return `=`; end if;
	if compart = `>` then 
		return compart; 
	elif compart = `<` then 
		return compart; 
	elif compart = `Non-comparable` then
		return compart; 
	elif compart= `=` then 
		cumul_part1:= PartialSums(composition1);
		cumul_part2:= PartialSums(composition2);
		max_length:= min(nops(cumul_part1), nops(cumul_part2));
		is1greater2 := map(x-> if op(x, cumul_part1) >= op(x, cumul_part2) then true; else false; end if, [seq(i, i=1..max_length)]);
		is1smaller2 := map(x-> if op(x, cumul_part1) <= op(x, cumul_part2) then true; else false; end if, [seq(i, i=1..max_length)]);
	
		if false in is1greater2 then 
			if false in is1smaller2 then 
						return `Non-comparable`;
				else 
						return `<`;
			end if;
		else
				return `>`;
			end if; 
	end if; 
return `ErrorInBruhat`; 
end proc:

genCompositions:=proc(weight, complength)
	local allcomp;
	allcomp:= [seq(op(composition(weight,k)),k=1..complength)]; 
	allcomp:= map(x-> if nops(x) < complength then [op(x),seq(0, k=1..(complength-nops(x)))]; else x; end if, allcomp); 
	allcomp:= map(x-> permute(x), allcomp); 
	allcomp:= FlattenOnce(allcomp); 
	allcomp:= MakeUnique(allcomp); 
	return allcomp;
end proc:

give_smallerComps:= proc(composition)
	local weight, allcomp, smallercomp;
	weight:= add(k, k in composition); 
	allcomp:= genCompositions(weight, nops(composition)); 
	smallercomp:= map(x-> if compare_bruhat(composition, x) = `>` then x; else NULL; end if, allcomp); 
	return smallercomp;
end proc:

compare_dominance:= proc(part1, part2, TEST:=NULL)
	local cumul_part1, cumul_part2, max_length, is1greater2, is1smaller2;
	#Normal dominance ordering comparision 
	if part1=part2 then return `=`; end if;
	if add(i,i in part1) <> add(i,i in part2) then return `Non-comparable`; end if;
	cumul_part1:= PartialSums(part1);
	cumul_part2:= PartialSums(part2);
	if TEST <> NULL then 
		if nops(part1) > nops(part2) then
			return `>`; 
		else
			return `<`; 
		end if;
	end if;
	max_length:= min(nops(cumul_part1), nops(cumul_part2));
	is1greater2 := map(x-> if op(x, cumul_part1) >= op(x, cumul_part2) then true; else false; end if, [seq(i, i=1..max_length)]);
	is1smaller2 := map(x-> if op(x, cumul_part1) <= op(x, cumul_part2) then true; else false; end if, [seq(i, i=1..max_length)]);
#debug

	if false in is1greater2 then 
		if false in is1smaller2 then 
			return `Non-comparable`;
		else 
			return `<`;
		end if;
	else
		return `>`;
	end if;
end proc:

ell:= proc(spart)
	local ell_out;
	#Returns the length of a spart
	ell_out:= nops(Flatten(spart)); 
	return ell_out; 
end proc:

lambda_box:= proc(spart)
	#removes circles from diagram
	return eliminate_zeros(sort(Flatten(spart), `>`)); 
end proc:

lambda_phitheta:= proc(spart)
	local phis, thetas, zeds, pts, ones;
	#removes h-circle, convert v-circle into boxes
	pts:= spart[1];
	ones:= [seq(1, k=1..nops(pts))];
	pts:= pts+ones;
	phis:= eliminate_zeros(spart[2]);
	thetas:= eliminate_zeros(spart[3]);
	zeds:= spart[4];
	return sort(Flatten([pts, phis, thetas, zeds]), `>`);
end proc:

lambda_phitheta_phi:= proc(spart)
	local pts, phis, thetas, zeds, ones;
	#removes h-circle, convert v-circle into boxes
	pts:= spart[1];
	ones:= [seq(1, k=1..nops(pts))];
	pts:= pts+ones;
	phis:= spart[2];
	ones:= [seq(1, k=1..nops(phis))];
	phis:= phis+ones;
	thetas:= eliminate_zeros(spart[3]);
	zeds:= spart[4];
	return sort(Flatten([pts, phis, thetas, zeds]), `>`);
end proc:

lambda_phitheta_phi_theta:= proc(spart)
	local pts, phis, thetas, zeds, ones;
	#removes h-circle, convert v-circle into boxes
	pts:= spart[1];
	ones:= [seq(1, k=1..nops(pts))];
	pts:= pts+ones;
	phis:= spart[2];
	ones:= [seq(1, k=1..nops(phis))];
	phis:= phis+ones;
	thetas:= spart[3];
	ones:= [seq(1, k=1..nops(thetas))]; 
	thetas:= thetas+ones;
	zeds:= spart[4];
	return sort(Flatten([pts, phis, thetas, zeds]), `>`);
end proc:

lambda_circle:= proc(spart, circs)
	local sector, pts, phis, thetas, zeds, partition, theseq;
	sector:= giveSpartSector(spart);
	pts:= spart[1];
	phis:= spart[2];
	thetas:= spart[3]; 
	zeds := spart[4];
	if 1 in circs then
		theseq:= [seq(1, k=1..sector[-1])];
		pts:= pts+theseq;
	end if:
	if 2 in circs then
		theseq:= [seq(1, k=1..sector[2])];
		phis:= phis+theseq;
	end if:
	if 3 in circs then
		theseq:= [seq(1, k=1..sector[3])];
		thetas:= thetas+theseq;
	end if:
	partition:= Flatten([pts, phis, thetas, zeds]); 
	partition:= Reverse(sort(partition)); 
	return eliminate_zeros(partition); 
end proc:

star_quatuor:= proc(spart, mode:=[1,2,3])
	local gradation, quatuor;
	#Self explanatory
	#Allowed modes: 
	# [TC, T, C]=[1,2,3](Normal), [TC, C, T]=[1,3,2], [T, C, TC]=2,3,1, [T, TC, C]=[2,1,3]...
	gradation:= [ seq(mode[1..k], k=0..3) ]; 
	quatuor:= map(x-> lambda_circle(spart,x), gradation);
	return quatuor; 
	#return [ lambda_box(spart), lambda_phitheta(spart), lambda_phitheta_phi(spart), lambda_phitheta_phi_theta(spart)];
end proc:

eliminate_zeros:= proc(a_list)
	#Removes 0's from a list
	return map(x-> if x = 0 then NULL; else x; end if, a_list);
end proc:

conjugate_part:= proc(part)
	local eat_part, new_part, len, ones;
	eat_part:= part;
	new_part:= [];
	len := nops(part);
	while len <> 0 do
		len := nops(eat_part);
		ones := [seq(1,j=1..len)];
		eat_part := eliminate_zeros(eat_part - ones);
		if len <> 0 then new_part := [op(new_part), len]; end if;
	end do:
	return new_part; 
end proc:

sCompareDominance:= proc(spart1, spart2, mode:=[1,2,3])
	local quatuor1, quatuor2, quatuor_dom; option remember;
	#Compares the dominance of two sparts
	if spart1 = spart2 then return `=`; end if;
	quatuor1:= star_quatuor(spart1, mode);
	quatuor2:= star_quatuor(spart2, mode);
	quatuor_dom:=map(x-> compare_dominance(quatuor1[x], quatuor2[x]), [1,2,3,4]);
	if 	`Non-comparable` in quatuor_dom then return `Non-comparable`;
	elif 	`>` in quatuor_dom and `<` in quatuor_dom then return `Non-comparable`;
	elif	`>` in quatuor_dom then return `>`;
	elif	`<` in quatuor_dom then return `<`;
	else	return "This should not happen, error in sCompareDominance"; 
	end if;
end proc:

sKeep_smaller_sparts:= proc(spart, sparts, mode:=[1,2,3]) local compared_dominance, list_indices, smaller_sparts;
	#Given a spart and a list of sparts, returns all the sparts within the set that are smaller than then one given
	compared_dominance:= map(x-> sCompareDominance(spart, x, mode), sparts);
	list_indices:= [seq(k, k=1..nops(sparts))]; 
	smaller_sparts:= map(x-> if compared_dominance[x] = `>` then sparts[x]; else NULL; end if, list_indices); 
	return smaller_sparts;
end proc:

give_greatest_spart:= proc(sparts, mode:=[1,2,3]) local k, dominance_of_spart;
	#Given a set of sparts, returns the highest one in the dominance ordering
	for k in sparts do
		dominance_of_spart:=map(x-> if x <> k then sCompareDominance(k, x, mode); else NULL; end if, sparts);
		if MakeUnique(dominance_of_spart) = [`>`] then return k; end if;
	end do:
end proc:


give_smallest_spart:= proc(sparts, mode:=[1,2,3]) local k, dominance_of_spart;
	#Given a set of sparts, returns the lowest one in the dominance ordering
	for k in sparts do
		dominance_of_spart:=map(x-> if x <> k then sCompareDominance(k, x, mode); else NULL; end if, sparts);
		if MakeUnique(dominance_of_spart) = [`<`] then return k; end if;
	end do:
end proc:

arm_part:= proc(i,j,part)
	#i is the row
	#j is the column
	return part[i]-j;
end proc:
co_arm_part:= proc(i,j,part)
	return j-1;
end proc:
co_leg_part:= proc(i,j,part)
	return i-1;
end proc:
leg_part:= proc(i,j,part)
	#i is the row
	#j is the column
	return conjugate_part(part)[j] - i;
end proc:
Jack_norm:= proc(spart, mode:=[1,2,3])
	local quatuor, spart0, spart1, spart2, spart3, spart_sector, M3, switched, nb_parts, B0, Btc, Bt, Bc, B1,B2,B3, ncoeff0, ncoeff1, ncoeff2, ncoeff3, the_coeff, pt_part, pt_distPart, zeta1;
	spart_sector:= giveSpartSector(spart); 
	quatuor := star_quatuor(spart, mode);
	M3:= spart_sector[2] + spart_sector[3] + spart_sector[4]; 
	spart0:= quatuor[1];
	spart1:= quatuor[2];
	spart2:= quatuor[3];
	spart3:= quatuor[4];
	switched := switch_notation(spart, a, 0, mode);
	nb_parts := nops(switched); 
	B0 := map(x-> if switched[x][2] = "" then seq([x,j], j=1..switched[x][1]); else NULL; end if, [seq(k, k=1..nb_parts)]);
	Btc := map(x-> if switched[x][2] = "TC" then seq([x,j], j=1..switched[x][1]); else NULL; end if, [seq(k, k=1..nb_parts)]);
	Bt := map(x-> if switched[x][2] = "T" then seq([x,j], j=1..switched[x][1]); else NULL; end if, [seq(k, k=1..nb_parts)]);
	Bt := map(x-> if x[2]-1 in spart[2] then NULL; else x; end if, Bt); 
	Bc := map(x-> if switched[x][2] = "C" then seq([x,j], j=1..switched[x][1]); else NULL; end if, [seq(k, k=1..nb_parts)]);
	Bc := map(x-> if x[2]-1 in spart[3] then NULL; else x; end if, Bc); 
	if mode[1] = 1 then
		B1:= Btc;
	elif mode[1] = 2 then
		B1:= Bt;
	elif mode[1] = 3 then
		B1:= Bc;
	end if;
	if mode[2] = 1 then
		B2:= Btc;
	elif mode[2] = 2 then
		B2:= Bt;
	elif mode[2] = 3 then
		B2:= Bc;
	end if;
	if mode[3] = 1 then
		B3:= Btc;
	elif mode[3] = 2 then
		B3:= Bt;
	elif mode[3] = 3 then
		B3:= Bc;
	end if;
	ncoeff0:= map(x->(leg_part(op(x),spart3) + alpha*(arm_part(op(x), spart0) + 1))/(leg_part(op(x),spart0) + 1 + alpha*arm_part(op(x), spart3)), B0); 
	ncoeff1:= map(x->(leg_part(op(x),spart0) + alpha*(arm_part(op(x), spart0) + 1))/(leg_part(op(x),spart1) + 1 + alpha*arm_part(op(x), spart3)), B1); 
	ncoeff2:= map(x->(leg_part(op(x),spart1) + alpha*(arm_part(op(x), spart0) + 1))/(leg_part(op(x),spart2) + 1 + alpha*arm_part(op(x), spart3)), B2); 
	ncoeff3:= map(x->(leg_part(op(x),spart2) + alpha*(arm_part(op(x), spart0) + 1))/(leg_part(op(x),spart3) + 1 + alpha*arm_part(op(x), spart3)), B3); 
	the_coeff:= mul(x, x in ncoeff0);
	the_coeff:= the_coeff*mul(x, x in ncoeff1);
	the_coeff:= the_coeff*mul(x, x in ncoeff2);
	the_coeff:= the_coeff*mul(x, x in ncoeff3);
	pt_part:= spart[1];
	pt_distPart:= {op(pt_part)}; 
	zeta1:= mul(factorial(Occurrences(i,pt_part)), i in pt_distPart);
	return factor(1/zeta1*alpha^(M3)*the_coeff); 
end proc:


down_hook:= proc(spart, mode:=[1,2,3])
	local quatuor, spart0, spart1, spart2, spart3, spart_sector, M3, switched, nb_parts, B0, Btc, Bt, Bc, B1,B2,B3, ncoeff0, ncoeff1, ncoeff2, ncoeff3, the_coeff, pt_part, pt_distPart, zeta1;
	spart_sector:= giveSpartSector(spart); 
	quatuor := star_quatuor(spart, mode);
	M3:= spart_sector[2] + spart_sector[3] + spart_sector[4]; 
	spart0:= quatuor[1];
	spart1:= quatuor[2];
	spart2:= quatuor[3];
	spart3:= quatuor[4];
	switched := switch_notation(spart, a, 0, mode);
	nb_parts := nops(switched); 
	B0 := map(x-> if switched[x][2] = "" then seq([x,j], j=1..switched[x][1]); else NULL; end if, [seq(k, k=1..nb_parts)]);
	Btc := map(x-> if switched[x][2] = "TC" then seq([x,j], j=1..switched[x][1]); else NULL; end if, [seq(k, k=1..nb_parts)]);
	Bt := map(x-> if switched[x][2] = "T" then seq([x,j], j=1..switched[x][1]); else NULL; end if, [seq(k, k=1..nb_parts)]);
	Bt := map(x-> if x[2]-1 in spart[2] then NULL; else x; end if, Bt); 
	Bc := map(x-> if switched[x][2] = "C" then seq([x,j], j=1..switched[x][1]); else NULL; end if, [seq(k, k=1..nb_parts)]);
	Bc := map(x-> if x[2]-1 in spart[3] then NULL; else x; end if, Bc); 
	if mode[1] = 1 then
		B1:= Btc;
	elif mode[1] = 2 then
		B1:= Bt;
	elif mode[1] = 3 then
		B1:= Bc;
	end if;
	if mode[2] = 1 then
		B2:= Btc;
	elif mode[2] = 2 then
		B2:= Bt;
	elif mode[2] = 3 then
		B2:= Bc;
	end if;
	if mode[3] = 1 then
		B3:= Btc;
	elif mode[3] = 2 then
		B3:= Bt;
	elif mode[3] = 3 then
		B3:= Bc;
	end if;
	ncoeff0:= map(x->(leg_part(op(x),spart0) + 1 + alpha*arm_part(op(x), spart3)), B0); 
	ncoeff1:= map(x->(leg_part(op(x),spart1) + 1 + alpha*arm_part(op(x), spart3)), B1); 
	ncoeff2:= map(x->(leg_part(op(x),spart2) + 1 + alpha*arm_part(op(x), spart3)), B2); 
	ncoeff3:= map(x->(leg_part(op(x),spart3) + 1 + alpha*arm_part(op(x), spart3)), B3); 
	the_coeff:= mul(x, x in ncoeff0);
	the_coeff:= the_coeff*mul(x, x in ncoeff1);
	the_coeff:= the_coeff*mul(x, x in ncoeff2);
	the_coeff:= the_coeff*mul(x, x in ncoeff3);
	pt_part:= spart[1];
	pt_distPart:= {op(pt_part)}; 
	zeta1:= mul(factorial(Occurrences(i,pt_part)), i in pt_distPart);
	return factor(zeta1*the_coeff); 
	#return the_coeff;
end proc:
